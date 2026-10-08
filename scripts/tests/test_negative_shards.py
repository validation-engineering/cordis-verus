"""Reject incomplete or mixed full-crate shard evidence without invoking Verus.

The tiny verifier outputs below are synthetic gate-test fixtures, not proof
results and never copied into a release artifact.
"""
import contextlib
import copy
import importlib.util
import io
import json
import shutil
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]


def load(filename, name):
    path = SCRIPTS / filename
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), 'exec'), result.__dict__)
    return result


SHARDS = load('negative-shards.py', 'negative_shards_test')
CHECKS = load('check-negative.py', 'negative_shards_checker_test')
RECORD = load('record-verification.py', 'negative_shards_record_test')


class ShardEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='cordis-shard-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / 'repository'
        self.source = self.repo / 'crates/cordis-kernel/src'
        self.source.mkdir(parents=True)
        (self.source / 'lib.rs').write_text('pub const A: u8 = 0;\npub const B: u8 = 0;\n')
        self.inputs = self.root / 'inputs'
        self.inputs.mkdir()
        self.output = self.root / 'collected'
        self.manifest = [('first', 'lib.rs', 'A: u8 = 0', 'A: u8 = 1'),
                         ('second', 'lib.rs', 'B: u8 = 0', 'B: u8 = 1')]
        self.bound = {'sourceHashes': {'lib.rs': SHARDS.digest(self.source / 'lib.rs')},
                      'toolHashes': {'verus': 'synthetic'}, 'manifestSha256': SHARDS.fingerprint(self.manifest),
                      'host': {'os': 'fixture', 'architecture': 'fixture'},
                      'origin': {'GITHUB_REPOSITORY': 'fixture/repository', 'GITHUB_RUN_ID': '123', 'GITHUB_RUN_ATTEMPT': '1', 'GITHUB_SHA': 'fixture'}}
        self.execution = {'availableCpus': 2, 'cpuBudget': 2, 'requestedJobs': 1, 'jobs': 1,
                          'threadsPerWorker': 2, 'baselineThreads': 2, 'timeoutSeconds': 2400,
                          'compileTimeoutSeconds': 300, 'diagnostics': True}
        self.version = {'version': 'synthetic-unit-fixture'}
        self.baseline = {'success': True, 'encountered-vir-error': False, 'encountered-error': False,
                         'verified': 40, 'errors': 0, 'is-verifying-entire-crate': True}
        self.negative = {**self.baseline, 'success': False, 'encountered-error': True, 'verified': 39, 'errors': 1}
        self.stack = contextlib.ExitStack()
        self.stack.enter_context(contextlib.redirect_stderr(io.StringIO()))
        self.addCleanup(self.stack.close)
        self.stack.enter_context(patch.object(SHARDS, 'ROOT', self.repo))
        self.stack.enter_context(patch.object(SHARDS, 'checker', return_value=CHECKS))
        self.stack.enter_context(patch.object(SHARDS, 'recorder', return_value=RECORD))
        self.stack.enter_context(patch.object(SHARDS, 'binding', side_effect=lambda *_: copy.deepcopy(self.bound)))
        self.stack.enter_context(patch.object(CHECKS, 'toolchain', return_value=(Path('/pinned/verus'), {})))
        self.stack.enter_context(patch.object(CHECKS, 'mutation_manifest', return_value=self.manifest))
        for index in range(2):
            self.write_shard(index)

    def write_stage(self, directory, stem, source_hash, *, kind='negative'):
        compile_only = kind == 'compile'
        stats = self.negative if kind == 'negative' else self.baseline
        if compile_only:
            stats = {**stats, 'verified': 0}
        code = 1 if kind == 'negative' else 0
        command = ['/pinned/verus', '/temporary/source/lib.rs', '--crate-name', 'cordis_negative',
                   '--crate-type=lib', '--edition=2021', '--no-cheating', '--output-json',
                   '--triggers-mode', 'silent', '--num-threads', '2', '--trace', '--time']
        if compile_only:
            command += ['--no-verify', '--compile', '-o', '/temporary/source/compile-check.rlib']
        SHARDS.save(directory / (stem + '.stdout.json'), {'verification-results': stats, 'verus': self.version})
        (directory / (stem + '.stderr.txt')).write_text('error: assertion failed\n' if code else '')
        SHARDS.save(directory / (stem + '.meta.json'), {
            'schema': 'cordis.negative-stage/v1', 'command': command, 'status': 'completed',
            'returncode': code, 'sourceSha256': source_hash, 'threads': 2,
            'timeoutSeconds': self.execution['compileTimeoutSeconds' if compile_only else 'timeoutSeconds'],
            'compileOnly': compile_only, 'durationSeconds': 0.1, 'diagnostics': True,
            'pid': 42, 'cleanup': {'observationMethod': 'waitid', 'leaderReaped': True,
                'snapshots': [{'phase': phase, 'members': [{'pid': 42, 'groupId': 42, 'state': 'Z'}]}
                              for phase in ['before-cleanup', 'before-kill', 'after-kill']]}})

    def write_shard(self, index, count=2):
        directory = self.inputs / str(index)
        directory.mkdir()
        selected = SHARDS.assigned(self.manifest, index, count)
        self.write_stage(directory, 'baseline', CHECKS.source_fingerprint(self.source), kind='positive')
        rows, filenames = [], SHARDS.stage_files('baseline')
        for name, relative, old, new in selected:
            source = self.source / relative
            text = source.read_text()
            source.write_text(text.replace(old, new))
            mutated = CHECKS.source_fingerprint(self.source)
            source.write_text(text)
            self.write_stage(directory, name + '-compile', mutated, kind='compile')
            self.write_stage(directory, name, mutated)
            filenames += SHARDS.stage_files(name + '-compile') + SHARDS.stage_files(name)
            rows.append({'name': name, 'compiles': True, 'verification-results': self.negative})
        SHARDS.save(directory / 'shard.json', {
            'schema': SHARDS.SCHEMA, 'status': 'passed', 'binding': self.bound, 'baselineMode': 'local',
            'shard': {'index': index, 'count': count, 'names': [item[0] for item in selected]},
            'execution': self.execution, 'baseline': self.baseline, 'verus': self.version,
            'mutations': rows, 'files': {name: SHARDS.digest(directory / name) for name in filenames}})

    def edit(self, relative, change, *, rehash=False):
        path = self.inputs / relative
        value = SHARDS.read_json(path)
        change(value)
        SHARDS.save(path, value)
        if rehash:
            report = path.parent / 'shard.json'
            value = SHARDS.read_json(report)
            value['files'][path.name] = SHARDS.digest(path)
            SHARDS.save(report, value)

    def collect(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return SHARDS.collect(self.inputs, self.output)

    def rejected(self, message):
        with self.assertRaisesRegex(RuntimeError, message):
            self.collect()
        self.assertFalse((self.output / 'report.json').exists())

    def test_compile_boolean_error_count_is_not_zero_errors(self):
        self.edit('0/first-compile.stdout.json',
                  lambda value: value['verification-results'].update(errors=False), rehash=True)
        self.rejected('compilation did not succeed')

    def test_duplicate_raw_output_keys_are_not_accepted(self):
        path = self.inputs / '0/first.stdout.json'
        path.write_text(path.read_text().replace('"success": false', '"success": true, "success": false'))
        self.edit('0/shard.json', lambda value: value['files'].update({path.name: SHARDS.digest(path)}))
        self.rejected('Duplicate evidence JSON key')

    def test_complete_union_is_canonical_and_retains_raw_evidence_hashes(self):
        summary = self.collect()
        self.assertEqual([item['name'] for item in summary['mutations']], ['first', 'second'])
        self.assertEqual(summary['execution']['mode'], 'full-crate-shards')
        self.assertEqual(summary['execution']['shardCount'], 2)
        self.assertEqual(len(summary['execution']['shards']), 2)
        RECORD.validate_negative_report(summary, ['first', 'second'])

    def test_independent_platform_collections_can_use_different_shard_counts(self):
        for count in [1, 2]:
            with self.subTest(count=count):
                shutil.rmtree(self.inputs)
                self.inputs.mkdir()
                self.output = self.root / ('collected-' + str(count))
                for index in range(count):
                    self.write_shard(index, count)
                summary = self.collect()
                self.assertEqual(summary['execution']['shardCount'], count)
                self.assertEqual([item['name'] for item in summary['mutations']], ['first', 'second'])

    def test_missing_shard_is_not_a_smaller_successful_gate(self):
        (self.inputs / '1/shard.json').unlink()
        self.rejected('Missing or additional')

    def test_duplicate_shard_does_not_replace_missing_coverage(self):
        self.edit('1/shard.json', lambda value: value['shard'].update(index=0))
        self.rejected('Duplicate or missing')

    def test_wrong_count_and_mutation_partition_are_rejected(self):
        self.edit('1/shard.json', lambda value: value['shard'].update(names=['first']))
        self.rejected('selection differs')

    def test_failed_shard_summary_is_not_accepted(self):
        self.edit('1/shard.json', lambda value: value.update(status='failed'))
        self.rejected('identity or selection')

    def test_different_source_toolchain_host_or_ci_attempt_is_rejected(self):
        for key in ['sourceHashes', 'toolHashes', 'host', 'origin', 'manifestSha256']:
            with self.subTest(key=key):
                path = self.inputs / '0/shard.json'
                original = path.read_bytes()
                self.edit('0/shard.json', lambda value: value['binding'].update({key: 'changed'}))
                self.rejected('identity or selection')
                path.write_bytes(original)

    def test_modified_raw_output_does_not_inherit_a_successful_summary(self):
        (self.inputs / '0/first.stderr.txt').write_text('changed')
        self.rejected('Changed stage bytes')

    def test_rehashed_resource_error_is_still_rejected(self):
        path = self.inputs / '0/first.stderr.txt'
        path.write_text('error: assertion failed\nerror: Resource limit (rlimit) exceeded\n')
        self.edit('0/shard.json', lambda value: value['files'].update({path.name: SHARDS.digest(path)}))
        self.rejected('resource or compiler')

    def test_no_contract_error_cannot_be_accepted_from_summary_alone(self):
        path = self.inputs / '0/first.stderr.txt'
        path.write_text('error: unknown identifier\n')
        self.edit('0/shard.json', lambda value: value['files'].update({path.name: SHARDS.digest(path)}))
        self.rejected('no conclusive contract')

    def test_scoped_or_extra_verifier_flags_are_rejected(self):
        self.edit('0/first.meta.json', lambda value: value['command'].extend(['--verify-only-module', 'effects']), rehash=True)
        self.rejected('Unexpected or scoped')

    def test_compilation_must_succeed(self):
        self.edit('0/first-compile.meta.json', lambda value: value.update(returncode=1), rehash=True)
        self.rejected('compilation did not succeed')

    def test_stage_must_bind_the_exact_mutated_source_tree(self):
        self.edit('0/first.meta.json', lambda value: value.update(sourceSha256=CHECKS.source_fingerprint(self.source)), rehash=True)
        self.rejected('stage metadata')

    def test_cancelled_timed_out_and_invalid_stage_metadata_are_rejected(self):
        for change in [{'status': 'timed_out'}, {'status': 'cancelled'}, {'signal': 15},
                       {'cancellationReason': 'interrupted'}, {'threads': True},
                       {'timeoutSeconds': True}, {'durationSeconds': float('nan')},
                       {'durationSeconds': -1}, {'returncode': True}, {'compileOnly': 0},
                       {'diagnostics': False}, {'cleanupError': 'failed'}, {'primaryStatus': 'timed_out'}]:
            with self.subTest(change=change):
                paths = [self.inputs / '0/first.meta.json', self.inputs / '0/shard.json']
                original = [path.read_bytes() for path in paths]
                self.edit('0/first.meta.json', lambda value: value.update(change), rehash=True)
                self.rejected('stage metadata')
                for path, raw in zip(paths, original):
                    path.write_bytes(raw)

    def test_raw_baseline_must_be_positive_and_whole_crate(self):
        self.edit('0/baseline.stdout.json', lambda value: value['verification-results'].update(verified=0), rehash=True)
        self.rejected('positive baseline')

    def test_summary_cannot_relabel_raw_negative_results(self):
        self.edit('0/shard.json', lambda value: value['mutations'][0]['verification-results'].update(errors=2))
        self.rejected('summary differs')

    def test_budget_must_be_internally_consistent(self):
        self.edit('0/shard.json', lambda value: value['execution'].update(cpuBudget=1))
        self.rejected('execution budget')

    def test_extra_stage_files_and_missing_stage_files_are_rejected(self):
        self.edit('0/shard.json', lambda value: value['files'].update({'extra.stdout.json': 'invented'}))
        self.rejected('additional stage')

    def test_symlinked_stage_files_are_not_evidence(self):
        path = self.inputs / '0/first.stdout.json'
        other = self.root / 'outside.json'
        path.rename(other)
        path.symlink_to(other)
        self.rejected('symlinked evidence')

    def test_duplicate_json_keys_are_rejected(self):
        path = self.inputs / '0/shard.json'
        raw = path.read_text()
        path.write_text(raw.replace('"status": "passed"', '"status": "failed", "status": "passed"'))
        self.rejected('Duplicate evidence JSON')

    def test_changes_during_collection_invalidate_all_results(self):
        with patch.object(SHARDS, 'binding', side_effect=[self.bound, {**self.bound, 'origin': 'changed'}]):
            self.rejected('changed during collection')


class SharedPreflightEvidenceTests(unittest.TestCase):
    # All outputs remain synthetic fixtures; no verifier or CI environment is run.
    write_stage = ShardEvidenceTests.write_stage
    write_shard = ShardEvidenceTests.write_shard
    edit = ShardEvidenceTests.edit
    collect = ShardEvidenceTests.collect
    rejected = ShardEvidenceTests.rejected

    def setUp(self):
        ShardEvidenceTests.setUp(self)
        self.preflight = self.root / 'preflight'
        self.preflight.mkdir()
        self.write_stage(self.preflight, 'baseline', CHECKS.source_fingerprint(self.source), kind='positive')
        self.preflight_execution = {key: value for key, value in self.execution.items()
                                    if key != 'compileTimeoutSeconds'}
        SHARDS.save(self.preflight / 'preflight.json', {
            'schema': SHARDS.PREFLIGHT_SCHEMA, 'status': 'passed', 'releaseAcceptance': False,
            'binding': self.bound, 'execution': self.preflight_execution,
            'baseline': self.baseline, 'verus': self.version,
            'files': {name: SHARDS.digest(self.preflight / name) for name in SHARDS.stage_files('baseline')}})
        for index in range(2):
            directory = self.inputs / str(index)
            for name in ['preflight.json'] + SHARDS.stage_files('baseline'):
                shutil.copyfile(self.preflight / name, directory / name)
            self.edit(f'{index}/shard.json', lambda value: value.update(
                baselineMode='preflight', preflightSha256=SHARDS.digest(directory / 'preflight.json')))
            self.edit(f'{index}/shard.json', lambda value: value['files'].update(
                {name: SHARDS.digest(directory / name) for name in ['preflight.json'] + SHARDS.stage_files('baseline')}))

    @contextlib.contextmanager
    def restore_inputs(self):
        original = {path: path.read_bytes() for path in self.inputs.rglob('*') if path.is_file()}
        try:
            yield
        finally:
            for path, raw in original.items():
                path.write_bytes(raw)

    def tamper(self, index, name, change):
        """Rehash all enclosing manifests: rejection must inspect the actual content."""
        directory = self.inputs / str(index)
        path = directory / name
        value = SHARDS.read_json(path)
        change(value)
        SHARDS.save(path, value)
        preflight = SHARDS.read_json(directory / 'preflight.json')
        if name != 'preflight.json':
            preflight['files'][name] = SHARDS.digest(path)
            SHARDS.save(directory / 'preflight.json', preflight)
        self.edit(f'{index}/shard.json', lambda value: value.update(
            preflightSha256=SHARDS.digest(directory / 'preflight.json')))
        self.edit(f'{index}/shard.json', lambda value: value['files'].update(
            {name: SHARDS.digest(directory / name) for name in ['preflight.json'] + SHARDS.stage_files('baseline')}))

    def test_shared_baseline_union_records_one_exact_preflight_identity(self):
        summary = self.collect()
        self.assertEqual(summary['execution']['baselineMode'], 'preflight')
        self.assertEqual(summary['execution']['preflightSha256'], SHARDS.digest(self.preflight / 'preflight.json'))
        self.assertEqual([item['name'] for item in summary['mutations']], ['first', 'second'])

    def test_unhashed_raw_preflight_tampering_is_rejected(self):
        (self.inputs / '0/baseline.stderr.txt').write_text('changed')
        self.rejected('Changed stage bytes')

    def test_rehashed_positive_flags_and_output_are_still_checked(self):
        for changes in [{'verified': 0}, {'errors': 1}, {'success': False},
                        {'encountered-error': True}, {'is-verifying-entire-crate': False}]:
            with self.subTest(changes=changes), self.restore_inputs():
                self.tamper(0, 'baseline.stdout.json', lambda value: value['verification-results'].update(changes))
                self.rejected('positive baseline')

    def test_preflight_requires_complete_current_ci_origin(self):
        for origin in [None, {}, {'GITHUB_RUN_ID': '123'}]:
            with self.subTest(origin=origin), self.assertRaisesRegex(RuntimeError, 'current CI run/attempt'):
                SHARDS.validate_preflight(self.preflight, {**self.bound, 'origin': origin},
                                          CHECKS.source_fingerprint(self.source), self.execution)

    def test_preflight_cannot_be_reused_across_repo_run_attempt_or_commit(self):
        for key in ['GITHUB_REPOSITORY', 'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_SHA']:
            with self.subTest(key=key), self.restore_inputs():
                self.tamper(0, 'preflight.json', lambda value: value['binding']['origin'].update({key: 'different'}))
                self.rejected('Preflight source/toolchain/platform/run identity')

    def test_preflight_requires_same_sources_tools_platform_and_manifest(self):
        for key in ['sourceHashes', 'toolHashes', 'host', 'manifestSha256']:
            with self.subTest(key=key), self.restore_inputs():
                self.tamper(0, 'preflight.json', lambda value: value['binding'].update({key: 'different'}))
                self.rejected('Preflight source/toolchain/platform/run identity')

    def test_preflight_status_alone_cannot_hide_timeout_cancellation_or_cleanup_failure(self):
        for changes in [{'status': 'timed_out'}, {'status': 'cancelled'}, {'signal': 15},
                        {'cancellationReason': 'cancelled'}, {'cleanupError': 'failed'},
                        {'primaryStatus': 'completed'}, {'diagnostics': False}, {'timeoutSeconds': 1}]:
            with self.subTest(changes=changes), self.restore_inputs():
                self.tamper(0, 'baseline.meta.json', lambda value: value.update(changes))
                self.rejected('stage metadata')

    def test_preflight_parameter_mismatch_and_extra_or_missing_flags_are_rejected(self):
        for key, changed in [('threadsPerWorker', 1), ('timeoutSeconds', 1200)]:
            with self.subTest(key=key), self.restore_inputs():
                self.edit('0/shard.json', lambda value: value['execution'].update(
                    {key: changed, **({'baselineThreads': changed} if key == 'threadsPerWorker' else {})}))
                self.rejected('Preflight verifier parameters differ')
        for change in [lambda command: command.extend(['--verify-only-module', 'effects']),
                       lambda command: command.remove('--trace'), lambda command: command.remove('--time')]:
            with self.subTest(change=change), self.restore_inputs():
                self.tamper(0, 'baseline.meta.json', lambda value: change(value['command']))
                self.rejected('Unexpected or scoped')

    def test_rehashed_cleanup_failures_and_live_descendants_are_rejected(self):
        cases = [{'leaderReaped': False}, {'observationMethod': 'unknown'}, {'snapshots': []},
                   {'snapshotError': 'failed'}, {'reapError': 'failed'},
                   {'signalError': 'failed'}, {'additionalError': 'failed'}]
        for changes in cases:
            with self.subTest(changes=changes), self.restore_inputs():
                self.tamper(0, 'baseline.meta.json', lambda value: value['cleanup'].update(changes))
                self.rejected('process cleanup')
        with self.restore_inputs():
            self.tamper(0, 'baseline.meta.json',
                        lambda value: value['cleanup']['snapshots'][-1]['members'][0].update(state='R'))
            self.rejected('Live process-group members')

    def test_repeated_after_kill_observations_are_valid_when_final_members_are_zombies(self):
        for index in range(2):
            def repeat(value):
                snapshots = value['cleanup']['snapshots']
                earlier = copy.deepcopy(snapshots[-1])
                earlier['members'].append({'pid': 43, 'groupId': 42, 'state': 'R'})
                snapshots.insert(-1, earlier)
            self.tamper(index, 'baseline.meta.json', repeat)
        self.collect()

    def test_two_individually_valid_preflights_cannot_be_combined(self):
        self.tamper(1, 'preflight.json', lambda value: value.update(checkedAt='another run of this stage'))
        self.rejected('different preflight evidence')

    def test_mixed_local_and_reused_baselines_and_incomplete_union_are_rejected(self):
        with self.restore_inputs():
            self.edit('0/shard.json', lambda value: value.update(baselineMode='local'))
            self.rejected('Mixed or invalid baseline modes')
        (self.inputs / '1/shard.json').unlink()
        self.rejected('Missing or additional')

    def test_preflight_manifest_digest_and_source_tree_are_bound(self):
        with self.restore_inputs():
            self.edit('0/shard.json', lambda value: value.update(preflightSha256='different'))
            self.rejected('preflight manifest bytes or identity')
        with self.restore_inputs():
            self.tamper(0, 'baseline.meta.json', lambda value: value.update(sourceSha256='other tree'))
            self.rejected('stage metadata')

    def test_preflight_success_summary_and_file_inventory_cannot_replace_raw_evidence(self):
        with self.restore_inputs():
            self.tamper(0, 'preflight.json', lambda value: value['baseline'].update(verified=999))
            self.rejected('Preflight summary differs')
        with self.restore_inputs():
            self.tamper(0, 'preflight.json', lambda value: value['files'].pop('baseline.meta.json'))
            self.rejected('Incomplete or additional preflight')
        with self.restore_inputs():
            self.tamper(0, 'preflight.json', lambda value: value.update(status='failed'))
            self.rejected('preflight failed')

    def copied_mutations(self, selected, _baseline, _temporary, output, *_args, **_kwargs):
        for name, *_ in selected:
            for filename in SHARDS.stage_files(name + '-compile') + SHARDS.stage_files(name):
                shutil.copyfile(self.inputs / '0' / filename, output / filename)
        return SHARDS.read_json(self.inputs / '0/shard.json')['mutations']

    def fake_positive(self, _binary, _environment, source, output, **_kwargs):
        self.write_stage(output.parent, output.name, CHECKS.source_fingerprint(source.parent), kind='positive')
        return CHECKS.subprocess.CompletedProcess([], 0,
            output.with_suffix('.stdout.json').read_text(), output.with_suffix('.stderr.txt').read_text())

    def test_reused_preflight_skips_only_baseline_and_runs_assigned_mutations(self):
        with patch.object(CHECKS, 'run_verus', side_effect=AssertionError('baseline must not rerun')), \
             patch.object(CHECKS, 'check_mutations', side_effect=self.copied_mutations) as mutations, \
             contextlib.redirect_stdout(io.StringIO()):
            report = SHARDS.run_shard(0, 2, self.root / 'run-shard', threads=2, preflight=self.preflight)
        self.assertEqual(report['status'], 'passed')
        self.assertEqual(report['baselineMode'], 'preflight')
        self.assertEqual(mutations.call_args.kwargs['compile_timeout'], 300)
        self.assertEqual(mutations.call_args.kwargs['timeout'], 2400)
        self.assertIs(mutations.call_args.kwargs['diagnostics'], True)
        self.assertEqual(mutations.call_args.args[0], [self.manifest[0]])

    def test_invalid_preflight_stops_before_any_mutants(self):
        path = self.preflight / 'baseline.stdout.json'
        path.write_text('changed')
        with patch.object(CHECKS, 'run_verus') as verifier, patch.object(CHECKS, 'check_mutations') as mutations, \
             self.assertRaisesRegex(RuntimeError, 'Changed stage bytes'):
            SHARDS.run_shard(0, 2, self.root / 'run-shard', threads=2, preflight=self.preflight)
        verifier.assert_not_called()
        mutations.assert_not_called()
        self.assertEqual(SHARDS.read_json(self.root / 'run-shard/shard.json')['status'], 'failed')

    def test_local_run_preserves_a_complete_fresh_baseline(self):
        with patch.object(CHECKS, 'run_verus', side_effect=self.fake_positive) as verifier, \
             patch.object(CHECKS, 'check_mutations', side_effect=self.copied_mutations), \
             contextlib.redirect_stdout(io.StringIO()):
            report = SHARDS.run_shard(0, 2, self.root / 'local-shard', threads=2)
        verifier.assert_called_once()
        self.assertEqual(report['baselineMode'], 'local')
        self.assertNotIn('preflightSha256', report)
        self.assertNotIn('preflight.json', report['files'])

    def test_cancellation_while_restoring_handlers_cannot_write_passed_evidence(self):
        @contextlib.contextmanager
        def cancel_on_exit(supervisor):
            yield supervisor
            supervisor.cancel(CHECKS.RunCancelled('cancelled during handler restoration'))

        for action in ['preflight', 'shard']:
            with self.subTest(action=action):
                output = self.root / ('cancelled-' + action)
                with patch.object(CHECKS.ProcessSupervisor, 'signal_handlers', cancel_on_exit), \
                     patch.object(CHECKS, 'run_verus', side_effect=self.fake_positive), \
                     patch.object(CHECKS, 'check_mutations', side_effect=self.copied_mutations), \
                     contextlib.redirect_stdout(io.StringIO()), self.assertRaises(CHECKS.RunCancelled):
                    if action == 'preflight':
                        SHARDS.run_preflight(output, threads=2)
                    else:
                        SHARDS.run_shard(0, 2, output, threads=2, preflight=self.preflight)
                report = SHARDS.read_json(output / (action + '.json'))
                self.assertEqual(report['status'], 'failed')
                self.assertEqual(report['failureSummary']['errorType'], 'RunCancelled')

    def test_cancellation_during_final_binding_cannot_write_passed_evidence(self):
        for action in ['preflight', 'shard']:
            with self.subTest(action=action):
                supervisor = CHECKS.ProcessSupervisor()
                calls = []
                def observe_binding(*_args):
                    calls.append(None)
                    if len(calls) > 1:
                        supervisor.cancel(CHECKS.RunCancelled('cancelled before saving evidence'))
                    return copy.deepcopy(self.bound)
                output = self.root / ('late-cancelled-' + action)
                with patch.object(CHECKS, 'ProcessSupervisor', return_value=supervisor), \
                     patch.object(SHARDS, 'binding', side_effect=observe_binding), \
                     patch.object(CHECKS, 'run_verus', side_effect=self.fake_positive), \
                     patch.object(CHECKS, 'check_mutations', side_effect=self.copied_mutations), \
                     contextlib.redirect_stdout(io.StringIO()), self.assertRaises(CHECKS.RunCancelled):
                    if action == 'preflight':
                        SHARDS.run_preflight(output, threads=2)
                    else:
                        SHARDS.run_shard(0, 2, output, threads=2, preflight=self.preflight)
                report = SHARDS.read_json(output / (action + '.json'))
                self.assertEqual(report['status'], 'failed')
                self.assertEqual(report['failureSummary']['errorType'], 'RunCancelled')

    def test_reporting_disk_and_pipe_failures_preserve_original_error_in_both_runners(self):
        actual_save = SHARDS.save
        for action in ['preflight', 'shard']:
            for fault in ['save', 'print']:
                with self.subTest(action=action, fault=fault):
                    primary = RuntimeError('original verifier failure')
                    output = self.root / ('report-fault-' + action + '-' + fault)
                    def failing_save(path, value):
                        if fault == 'save' and value.get('status') == 'failed':
                            raise OSError('disk unavailable')
                        actual_save(path, value)
                    def failing_print(message, **_kwargs):
                        if fault == 'print' and message.startswith(('Negative verification failed:', 'Raw proof evidence')):
                            raise BrokenPipeError('pipe closed')
                    with patch.object(SHARDS, 'save', side_effect=failing_save), \
                         patch.object(SHARDS, 'print', side_effect=failing_print, create=True), \
                         patch.object(CHECKS, 'run_verus', side_effect=primary), \
                         self.assertRaises(RuntimeError) as failure:
                        if action == 'preflight':
                            SHARDS.run_preflight(output, threads=2)
                        else:
                            SHARDS.run_shard(0, 2, output, threads=2)
                    self.assertIs(failure.exception, primary)

    def test_preflight_stage_records_raw_baseline_but_is_not_release_acceptance(self):
        with patch.object(CHECKS, 'run_verus', side_effect=self.fake_positive) as verifier, \
             contextlib.redirect_stdout(io.StringIO()):
            report = SHARDS.run_preflight(self.root / 'new-preflight', threads=2)
        verifier.assert_called_once()
        self.assertIs(verifier.call_args.kwargs['diagnostics'], True)
        self.assertEqual(report['schema'], SHARDS.PREFLIGHT_SCHEMA)
        self.assertEqual(report['status'], 'passed')
        self.assertIs(report['releaseAcceptance'], False)
        SHARDS.validate_preflight(self.root / 'new-preflight', self.bound,
                                  CHECKS.source_fingerprint(self.source), self.execution)


class PlatformPlanTests(unittest.TestCase):
    def test_plan_is_pure_and_covers_each_selected_platform(self):
        for include_intel in (False, True):
            with self.subTest(include_intel=include_intel), \
                 patch.object(SHARDS, 'checker', return_value=CHECKS), \
                 patch.object(CHECKS, 'toolchain', side_effect=AssertionError('plan must not install tools')), \
                 patch.object(CHECKS, 'run_verus', side_effect=AssertionError('plan must not run proofs')):
                plan = SHARDS.release_plan(include_macos_intel=include_intel)
                self.assertEqual(plan['mutationCount'], 114)
                self.assertEqual(len(plan['negative']['include']), 80 if include_intel else 42)
                expected = [('ubuntu-24.04', 2400, 18, 55), ('macos-15', 3600, 24, 75)]
                targets = ['linux-x64-gnu-napi8', 'darwin-arm64-napi8']
                if include_intel:
                    expected.append(('macos-15-intel', 5400, 38, 105))
                    targets.append('darwin-x64-napi8')
                self.assertEqual([(row['os'], row['timeout'], row['shardCount'], row['preflightMinutes'])
                                  for row in plan['preflight']['include']], expected)
                self.assertEqual(plan['quality'], {'os': [row[0] for row in expected]})
                self.assertEqual(plan['targets'], targets)
                manifest = CHECKS.mutation_manifest()
                for platform in plan['preflight']['include']:
                    rows = [row for row in plan['negative']['include'] if row['os'] == platform['os']]
                    self.assertEqual([row['shard'] for row in rows], list(range(platform['shardCount'])))
                    self.assertTrue(all({key: row[key] for key in platform} == platform for row in rows))
                    covered = [item for row in rows for item in SHARDS.assigned(manifest, row['shard'], row['shardCount'])]
                    self.assertEqual(len(covered), len(manifest))
                    self.assertEqual(set(covered), set(manifest))

    def test_growth_cannot_silently_exceed_job_budget(self):
        for include_intel in (False, True):
            for manifest in [[], [('same',)] * 114, [(f'control-{index}',) for index in range(200)]]:
                with self.subTest(count=len(manifest), intel=include_intel), self.assertRaises(RuntimeError):
                    SHARDS.release_plan(manifest, include_macos_intel=include_intel)

    def test_platform_opt_in_is_boolean(self):
        for value in ('false', 'true', 1, None):
            with self.subTest(value=value), self.assertRaises(RuntimeError):
                SHARDS.release_plan(include_macos_intel=value)

    def test_github_outputs_are_json_from_the_same_plan(self):
        with tempfile.TemporaryDirectory(prefix='cordis-plan-test-') as temporary:
            for include_intel in (False, True):
                output = Path(temporary) / str(include_intel)
                with contextlib.redirect_stdout(io.StringIO()):
                    plan = SHARDS.write_plan(output, include_macos_intel=include_intel)
                values = dict(line.split('=', 1) for line in output.read_text().splitlines())
                self.assertEqual(set(values), {'preflight', 'negative', 'quality', 'targets'})
                for key, value in values.items():
                    self.assertEqual(json.loads(value), plan[key])


class FailureSummaryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='cordis-failure-summary-')
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)

    def write_timeout(self, stem='baseline'):
        # Small synthetic equivalent of the Intel timeout shape; no solver is run.
        metadata = {'status': 'timed_out', 'returncode': -15, 'durationSeconds': 2401.65,
                    'timeoutSeconds': 2400, 'startedAtUnix': 100,
                    'cleanup': {'observationMethod': 'waitid', 'leaderReaped': True,
                        'snapshots': [{'phase': 'after-kill', 'members': [{'state': 'Z<'}]}]}}
        SHARDS.save(self.directory / (stem + '.meta.json'), metadata)
        (self.directory / (stem + '.stdout.json')).write_text('')
        (self.directory / (stem + '.stderr.txt')).write_text(''.join(f'note: verifying function_{index}\n' for index in range(40)))

    def test_wall_timeout_summary_preserves_empty_json_and_successful_cleanup(self):
        self.write_timeout()
        originals = {path.name: path.read_bytes() for path in self.directory.iterdir()}
        error = CHECKS.subprocess.TimeoutExpired(['verus'], 2400)
        summary = SHARDS.failure_summary(self.directory, error)
        self.assertEqual(summary['errorType'], 'TimeoutExpired')
        stage = summary['stages'][0]
        self.assertEqual(stage['status'], 'timed_out')
        self.assertEqual(stage['durationSeconds'], 2401.65)
        self.assertEqual(stage['returncode'], -15)
        self.assertTrue(stage['cleanup']['leaderReaped'])
        self.assertEqual(stage['cleanup']['lastObservedLiveMembers'], 0)
        self.assertIn('incomplete JSON', stage['verificationOutput'])
        self.assertEqual(len(stage['lastTrace']), 12)
        self.assertEqual(stage['lastTrace'][-1], 'note: verifying function_39')
        self.assertEqual(originals, {path.name: path.read_bytes() for path in self.directory.iterdir()})

    def test_cleanup_failure_and_primary_timeout_are_both_retained(self):
        self.write_timeout()
        path = self.directory / 'baseline.meta.json'
        metadata = SHARDS.read_json(path)
        metadata.update(cleanupError='PermissionError: cleanup denied', primaryStatus='timed_out')
        metadata['cleanup'].update(leaderReaped=False, signalError='PermissionError: TERM denied')
        SHARDS.save(path, metadata)
        stage = SHARDS.failure_summary(self.directory, PermissionError('cleanup denied'))['stages'][0]
        self.assertEqual(stage['status'], 'timed_out')
        self.assertEqual(stage['primaryStatus'], 'timed_out')
        self.assertEqual(stage['cleanupError'], 'PermissionError: cleanup denied')
        self.assertFalse(stage['cleanup']['leaderReaped'])
        self.assertIn('TERM denied', stage['cleanup']['signalError'])

    def test_current_mutant_failure_is_not_hidden_by_reused_baseline(self):
        self.write_timeout('a-mutant')
        self.write_timeout('baseline')
        path = self.directory / 'baseline.meta.json'
        metadata = SHARDS.read_json(path)
        metadata.update(status='completed', returncode=0, startedAtUnix=1)
        SHARDS.save(path, metadata)
        summary = SHARDS.failure_summary(self.directory, RuntimeError('a-mutant failed'))
        self.assertEqual([row['stage'] for row in summary['stages']], ['a-mutant'])

    def test_completed_proof_failure_includes_actual_verification_counts(self):
        self.write_timeout()
        path = self.directory / 'baseline.meta.json'
        metadata = SHARDS.read_json(path)
        metadata.update(status='completed', returncode=1)
        SHARDS.save(path, metadata)
        SHARDS.save(self.directory / 'baseline.stdout.json',
                    {'verification-results': {'success': False, 'verified': 2290, 'errors': 7}})
        stage = SHARDS.failure_summary(self.directory, RuntimeError('positive baseline failed'))['stages'][0]
        self.assertEqual(stage['verification'], {'success': False, 'verified': 2290, 'errors': 7})

    def test_diagnostics_are_bounded_safe_log_text_and_cannot_mark_failure_passed(self):
        self.write_timeout()
        (self.directory / 'baseline.stderr.txt').write_text('::error::not a workflow command\n' + 'x' * 3000)
        record = {'status': 'running'}
        output = io.StringIO()
        with contextlib.redirect_stderr(output):
            SHARDS.record_failure(self.directory, 'preflight.json', record, RuntimeError('original failure'))
        self.assertEqual(record['status'], 'failed')
        self.assertEqual(SHARDS.read_json(self.directory / 'preflight.json')['status'], 'failed')
        self.assertNotIn('\n::error::', output.getvalue())
        self.assertLessEqual(max(map(len, record['failureSummary']['stages'][0]['lastTrace'])), 500)
        self.assertIn('original failure', output.getvalue())
        self.assertIn('timed_out', output.getvalue())

    def test_missing_malformed_or_unavailable_diagnostics_do_not_replace_the_error(self):
        (self.directory / 'broken.meta.json').write_text('{broken')
        summary = SHARDS.failure_summary(self.directory, RuntimeError('keep this failure'))
        self.assertEqual(summary['message'], 'keep this failure')
        self.assertEqual(summary['stages'], [])
        record = {}
        with patch.object(SHARDS, 'failure_summary', side_effect=OSError('diagnostics unavailable')), \
             contextlib.redirect_stderr(io.StringIO()):
            SHARDS.record_failure(self.directory, 'shard.json', record, ValueError('primary error'))
        self.assertEqual(record['failure'], 'ValueError: primary error')
        self.assertEqual(record['status'], 'failed')
        self.assertEqual(record['failureSummary']['message'], 'primary error')


class SelectionTests(unittest.TestCase):
    def test_all_114_controls_are_partitioned_once_without_changing_each_control(self):
        manifest = CHECKS.mutation_manifest()
        self.assertEqual(len(manifest), 114)
        for count, maximum in [(18, 7), (24, 5), (38, 3)]:
            with self.subTest(count=count):
                pieces = [SHARDS.assigned(manifest, index, count) for index in range(count)]
                flattened = [item for group in pieces for item in group]
                self.assertEqual(len(flattened), 114)
                self.assertEqual(set(flattened), set(manifest))
                self.assertEqual(max(map(len, pieces)), maximum)

    def test_invalid_shards_are_rejected(self):
        for index, count in [(0, 0), (-1, 2), (2, 2), (True, 2), (0, True), (0, 3)]:
            with self.subTest(index=index, count=count), self.assertRaises(RuntimeError):
                SHARDS.assigned(['one', 'two'], index, count)


if __name__ == '__main__':
    unittest.main()
