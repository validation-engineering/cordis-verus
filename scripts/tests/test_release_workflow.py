"""Release quality is independent; mutation regressions keep complete provenance."""
import fnmatch
import importlib.util
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[2]
RELEASE_WORKFLOW = ROOT / '.github/workflows/release-validation.yml'
WORKFLOW = ROOT / '.github/workflows/negative-regression.yml'
SCRIPT = ROOT / 'scripts/negative-shards.py'
SPEC = importlib.util.spec_from_file_location('release_workflow_shards', SCRIPT)
SHARDS = importlib.util.module_from_spec(SPEC)
exec(compile(SCRIPT.read_bytes(), str(SCRIPT), 'exec'), SHARDS.__dict__)

PACKAGE_SPEC = importlib.util.spec_from_file_location('workflow_package', ROOT / 'scripts/package-runtime-release.py')
PACKAGE = importlib.util.module_from_spec(PACKAGE_SPEC)
PACKAGE_SPEC.loader.exec_module(PACKAGE)


class NegativeWorkflowTests(unittest.TestCase):
    include_macos = False
    include_macos_intel = False

    def setUp(self):
        self.text = WORKFLOW.read_text()
        self.plan = SHARDS.regression_plan(include_macos=self.include_macos, include_macos_intel=self.include_macos_intel)
        self.platforms = self.plan['preflight']['include']
        self.rows = self.plan['negative']['include']

    @staticmethod
    def render(template, attempt, row):
        text = template.replace('${{ github.run_attempt }}', str(attempt))
        return re.sub(r'\$\{\{ matrix\.(\w+) \}\}', lambda match: str(row[match[1]]), text)

    def section(self, name, following):
        return self.text.split('\n  ' + name + ':', 1)[1].split('\n  ' + following + ':', 1)[0]

    def test_one_plan_drives_both_matrices_without_invoking_verus(self):
        plan = self.section('plan', 'preflight')
        preflight = self.section('preflight', 'negative')
        negative = self.section('negative', 'collect')
        self.assertIn('python3 scripts/negative-shards.py plan --github-output "$GITHUB_OUTPUT"', plan)
        self.assertIn('preflight: ${{ steps.matrix.outputs.preflight }}', plan)
        self.assertIn('negative: ${{ steps.matrix.outputs.negative }}', plan)
        self.assertNotIn('install-verus', plan)
        self.assertNotIn('run_verus', plan)
        self.assertIn('matrix: ${{ fromJSON(needs.plan.outputs.preflight) }}', preflight)
        self.assertIn('matrix: ${{ fromJSON(needs.plan.outputs.negative) }}', negative)
        self.assertRegex(preflight, r'(?m)^    needs: plan$')
        self.assertRegex(negative, r'(?m)^    needs: \[plan, preflight\]$')
        self.assertIn("${{ inputs.include_macos_intel && '--include-macos-intel' || '' }}", plan)
        self.assertRegex(self.text, r'include_macos_intel:\n(?:        .+\n)*?        default: false\n        type: boolean')

    def test_each_platform_downloads_only_its_own_complete_current_attempt_shards(self):
        upload = re.findall(r'^          name: (negative-.+)$', self.section('negative', 'collect'), re.M)
        download = re.findall(r'^          pattern: (negative-.+)$', self.text, re.M)
        self.assertEqual(len(upload), 1)
        self.assertEqual(len(download), 1)
        artifacts = [(attempt, row['os'], row['shard'], self.render(upload[0], attempt, row))
                     for attempt in (1, 2) for row in self.rows]
        self.assertEqual(len({item[3] for item in artifacts}), len(artifacts))
        for platform in self.platforms:
            pattern = self.render(download[0], 2, platform)
            selected = {(attempt, os_name, shard) for attempt, os_name, shard, artifact in artifacts
                        if fnmatch.fnmatchcase(artifact, pattern)}
            self.assertEqual(selected, {(2, platform['os'], index) for index in range(platform['shardCount'])})

    def test_each_platform_reuses_only_its_current_attempt_preflight(self):
        preflight = self.section('preflight', 'negative')
        negative = self.section('negative', 'collect')
        upload = re.search(r'^          name: (preflight-.+)$', preflight, re.M)[1]
        download = re.search(r'^          name: (preflight-.+)$', negative, re.M)[1]
        self.assertEqual(upload, download)
        artifacts = {(attempt, row['os']): self.render(upload, attempt, row)
                     for attempt in (1, 2) for row in self.platforms}
        self.assertEqual(len(set(artifacts.values())), 2 * len(self.platforms))
        for row in self.platforms:
            selected = [key for key, value in artifacts.items() if value == self.render(download, 2, row)]
            self.assertEqual(selected, [(2, row['os'])])
        self.assertIn('path: target/negative-preflight', negative)
        self.assertNotIn('run-id:', negative)
        self.assertNotIn('repository:', negative)
        self.assertNotIn('actions/cache', negative)

    def test_platform_command_parameters_match_and_leave_budget_for_cleanup(self):
        preflight = self.section('preflight', 'negative')
        negative = self.section('negative', 'collect')
        preflight_command = re.search(r'^        run: (exec python3 scripts/negative-shards.py preflight .+)$', preflight, re.M)[1]
        negative_command = re.search(r'^          (exec python3 scripts/negative-shards.py run .+)$', negative, re.M)[1]
        self.assertTrue(negative_command.endswith(' "${diagnostic_args[@]}"'))
        negative_command = negative_command.removesuffix(' "${diagnostic_args[@]}"')
        self.assertIn('timeout-minutes: ${{ matrix.preflightMinutes }}', preflight)
        self.assertIn('timeout-minutes: ${{ matrix.shardMinutes }}', negative)
        for row in self.rows:
            p_args = shlex.split(self.render(preflight_command, 1, row))
            args = shlex.split(self.render(negative_command, 1, row))
            p_options = dict(zip(p_args[4::2], p_args[5::2]))
            options = dict(zip(args[4::2], args[5::2]))
            self.assertEqual(set(options), {'--shard-index', '--shard-count', '--output', '--jobs',
                                           '--threads', '--timeout', '--compile-timeout', '--preflight'})
            self.assertEqual(int(options['--shard-count']), row['shardCount'])
            self.assertEqual(int(options['--shard-index']), row['shard'])
            self.assertEqual(options['--threads'], p_options['--threads'])
            self.assertEqual(options['--timeout'], p_options['--timeout'])
            self.assertEqual(options['--compile-timeout'], '300')
            self.assertEqual(options['--jobs'], '1')
            self.assertEqual(options['--preflight'], 'target/negative-preflight')
            maximum = (self.plan['mutationCount'] + row['shardCount'] - 1) // row['shardCount']
            budget = maximum * (int(options['--timeout']) + int(options['--compile-timeout']))
            self.assertGreaterEqual(row['shardMinutes'] * 60 - budget, 30 * 60)
            self.assertGreaterEqual(row['preflightMinutes'] * 60 - int(p_options['--timeout']), 15 * 60)
        collector = self.text.split('\n  collect:', 1)[1]
        self.assertRegex(collector, r'(?m)^    needs: \[plan, negative\]$')
        self.assertIn('negative-shards.py collect --input target/full-negative-shards --output target/proof-negative', collector)
        self.assertNotIn('record-verification.py', self.text)
        self.assertNotIn('contents: write', self.text)
        self.assertNotIn('gh release', self.text)


class DiagnosticWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.text = WORKFLOW.read_text()

    def step_script(self, name):
        section = self.text.split('      - name: ' + name + '\n', 1)[1]
        body = re.search(r'        run: \|\n((?:          .*\n|\n)+)', section)[1]
        return textwrap.dedent(body)

    def test_diagnostic_is_opt_in_and_skips_accepted_regression_collection(self):
        self.assertRegex(self.text, r'diagnostic_keep_going:\n(?:        .+\n)*?        default: false\n        type: boolean')
        collector = self.text.split('\n  collect:', 1)[1]
        self.assertIn('if: ${{ !inputs.diagnostic_keep_going }}', collector)
        self.assertNotIn('draft-release:', self.text)
        self.assertNotIn('continue-on-error:', self.text)
        negative = self.text.split('\n  negative:', 1)[1].split('\n  collect:', 1)[0]
        self.assertIn('fail-fast: false', negative)
        upload = negative.split('      - name: Retain negative evidence, including failures', 1)[1]
        self.assertIn('if: always()', upload)

    def test_failure_summaries_run_before_upload_without_changing_verification_status(self):
        for job, following, kind, directory, upload in (
                ('preflight', 'negative', 'baseline', 'negative-preflight', 'Retain baseline diagnostics, including failures'),
                ('negative', 'collect', 'negative', 'negative-shard', 'Retain negative evidence, including failures')):
            with self.subTest(job=job):
                section = self.text.split('\n  ' + job + ':', 1)[1].split('\n  ' + following + ':', 1)[0]
                expected = ('      - name: Summarize ' + kind + ' results before artifact upload\n'
                            '        if: always()\n'
                            '        run: python3 scripts/summarize-negative.py --input target/' + directory
                            + ' --github-summary "$GITHUB_STEP_SUMMARY"\n')
                self.assertIn(expected, section)
                self.assertLess(section.index(expected), section.index('      - name: ' + upload))
                self.assertNotIn('continue-on-error:', section)

    def test_dispatch_passes_keep_going_only_when_enabled(self):
        row = SHARDS.regression_plan()['negative']['include'][0]
        script = NegativeWorkflowTests.render(self.step_script('Verify this shard as complete crates'), 1, row)
        with tempfile.TemporaryDirectory(prefix='cordis-workflow-test-') as temporary:
            executable = Path(temporary) / 'python3'
            executable.write_text("#!/bin/bash\nprintf '%s\\n' \"$@\"\n")
            executable.chmod(0o755)
            for mode in ('false', 'true'):
                with self.subTest(mode=mode):
                    run = subprocess.run(['bash', '--noprofile', '--norc', '-eo', 'pipefail', '-c', script], capture_output=True, text=True,
                                         env={**os.environ, 'PATH': temporary + os.pathsep + os.environ['PATH'],
                                              'DIAGNOSTIC_KEEP_GOING': mode})
                    self.assertEqual(run.returncode, 0, run.stderr)
                    arguments = run.stdout.splitlines()
                    self.assertEqual(arguments[:2], ['scripts/negative-shards.py', 'run'])
                    self.assertEqual(arguments.count('--keep-going'), 1 if mode == 'true' else 0)
                    self.assertNotIn('', arguments)


class AllPlatformNegativeWorkflowTests(NegativeWorkflowTests):
    include_macos = True
    include_macos_intel = True


class ReleaseWorkflowTests(unittest.TestCase):
    def test_release_has_no_negative_dependency_and_draft_requires_all_quality_jobs(self):
        text = RELEASE_WORKFLOW.read_text()
        self.assertNotIn('negative-shards.py', text)
        self.assertNotIn('diagnostic_keep_going', text)
        self.assertNotIn('target/proof-negative', text)
        self.assertNotIn('  preflight:', text)
        self.assertNotIn('  negative:', text)
        quality = text.split('\n  quality:', 1)[1].split('\n  draft-release:', 1)[0]
        self.assertRegex(quality, r'(?m)^    needs: plan$')
        self.assertIn('run: exec python3 scripts/record-verification.py', quality)
        self.assertIn('target/positive-proof/', quality)
        self.assertIn('package-runtime-release.py package', quality)
        self.assertIn('install-cordis.mjs --from-directory', quality)
        self.assertIn('npm ci --offline --ignore-scripts', quality)
        draft = text.split('\n  draft-release:', 1)[1]
        self.assertRegex(draft, r'(?m)^    needs: \[plan, quality\]$')
        self.assertIn('if: ${{ inputs.create_draft }}', draft)
        self.assertIn('pattern: full-validation-${{ github.run_attempt }}-*', draft)
        self.assertIn('--targets-json "$RELEASE_TARGETS_JSON"', draft)
        self.assertIn('recorded as not_run', draft)
        self.assertNotIn('continue-on-error:', text)

    def test_release_plan_cli_selects_matching_jobs_and_assets_without_a_mutation_manifest(self):
        for intel in (False, True):
            with self.subTest(intel=intel), tempfile.TemporaryDirectory() as directory:
                output = Path(directory) / 'outputs'
                command = ['python3', str(ROOT / 'scripts/package-runtime-release.py'), 'plan', '--github-output', str(output)]
                if intel: command.append('--include-macos-intel')
                subprocess.run(command, check=True, capture_output=True)
                plan = {key: json.loads(value) for key, value in (line.split('=', 1) for line in output.read_text().splitlines())}
                self.assertEqual(plan, PACKAGE.release_plan(intel))
                self.assertEqual(set(plan['targets']), PACKAGE.TARGETS if intel else PACKAGE.DEFAULT_TARGETS)
                self.assertEqual(len(plan['quality']['os']), len(plan['targets']))


class DevelopmentWorkflowTests(unittest.TestCase):
    def test_default_and_manual_matrices_match_release_platform_selection(self):
        text = (ROOT / '.github/workflows/verify.yml').read_text()
        self.assertRegex(text, r'include_macos_intel:\n(?:        .+\n)*?        default: false\n        type: boolean')
        # Push and PR events cannot enable Intel, even if an input-shaped value exists.
        expression = re.search(r'^        os: (.+)$', text, re.M)[1]
        self.assertIn("github.event_name == 'workflow_dispatch' && inputs.include_macos_intel", expression)
        choices = re.findall(r"'(\[.+?\])'", expression)
        self.assertEqual(len(choices), 2)
        manual, default = map(json.loads, choices)
        self.assertEqual(default, PACKAGE.release_plan()['quality']['os'])
        self.assertEqual(manual, PACKAGE.release_plan(include_macos_intel=True)['quality']['os'])
        self.assertIn('exec python3 scripts/record-development.py', text)


if __name__ == '__main__':
    unittest.main()
