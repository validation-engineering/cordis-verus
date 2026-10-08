"""Release matrices preserve full coverage, budgets and current-attempt provenance."""
import fnmatch
import importlib.util
from pathlib import Path
import re
import shlex
import unittest

ROOT = Path(__file__).resolve().parents[2]
WORKFLOW = ROOT / '.github/workflows/release-validation.yml'
SCRIPT = ROOT / 'scripts/negative-shards.py'
SPEC = importlib.util.spec_from_file_location('release_workflow_shards', SCRIPT)
SHARDS = importlib.util.module_from_spec(SPEC)
exec(compile(SCRIPT.read_bytes(), str(SCRIPT), 'exec'), SHARDS.__dict__)


class ReleaseWorkflowTests(unittest.TestCase):
    def setUp(self):
        self.text = WORKFLOW.read_text()
        self.plan = SHARDS.release_plan()
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
        negative = self.section('negative', 'quality')
        self.assertIn('python3 scripts/negative-shards.py plan --github-output "$GITHUB_OUTPUT"', plan)
        self.assertIn('preflight: ${{ steps.matrix.outputs.preflight }}', plan)
        self.assertIn('negative: ${{ steps.matrix.outputs.negative }}', plan)
        self.assertNotIn('install-verus', plan)
        self.assertNotIn('run_verus', plan)
        self.assertIn('matrix: ${{ fromJSON(needs.plan.outputs.preflight) }}', preflight)
        self.assertIn('matrix: ${{ fromJSON(needs.plan.outputs.negative) }}', negative)
        self.assertRegex(preflight, r'(?m)^    needs: plan$')
        self.assertRegex(negative, r'(?m)^    needs: \[plan, preflight\]$')
        quality = self.section('quality', 'draft-release')
        quality_platforms = set(re.search(r'        os: \[(.+)\]', quality)[1].split(', '))
        self.assertEqual(quality_platforms, {row['os'] for row in self.platforms})

    def test_each_platform_downloads_only_its_own_complete_current_attempt_shards(self):
        upload = re.findall(r'^          name: (negative-.+)$', self.text, re.M)
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
        negative = self.section('negative', 'quality')
        upload = re.search(r'^          name: (preflight-.+)$', preflight, re.M)[1]
        download = re.search(r'^          name: (preflight-.+)$', negative, re.M)[1]
        self.assertEqual(upload, download)
        artifacts = {(attempt, row['os']): self.render(upload, attempt, row)
                     for attempt in (1, 2) for row in self.platforms}
        self.assertEqual(len(set(artifacts.values())), 6)
        for row in self.platforms:
            selected = [key for key, value in artifacts.items() if value == self.render(download, 2, row)]
            self.assertEqual(selected, [(2, row['os'])])
        self.assertIn('path: target/negative-preflight', negative)
        self.assertNotIn('run-id:', negative)
        self.assertNotIn('repository:', negative)
        self.assertNotIn('actions/cache', negative)

    def test_platform_command_parameters_match_and_leave_budget_for_cleanup(self):
        preflight = self.section('preflight', 'negative')
        negative = self.section('negative', 'quality')
        preflight_command = re.search(r'^        run: (exec python3 scripts/negative-shards.py preflight .+)$', preflight, re.M)[1]
        negative_command = re.search(r'^        run: (exec python3 scripts/negative-shards.py run .+)$', negative, re.M)[1]
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
        quality = self.section('quality', 'draft-release')
        self.assertRegex(quality, r'(?m)^    needs: negative$')
        self.assertIn('record-verification.py --negative-shards target/full-negative-shards', quality)
        draft = self.text.split('\n  draft-release:', 1)[1]
        self.assertRegex(draft, r'(?m)^    needs: quality$')
        self.assertIn('pattern: full-validation-${{ github.run_attempt }}-*', draft)


if __name__ == '__main__':
    unittest.main()
