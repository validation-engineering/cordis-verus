"""Reject incomplete or mixed full-crate shard evidence without invoking Verus.

The tiny verifier outputs below are synthetic gate-test fixtures, not proof
results and never copied into a release artifact.
"""
import contextlib
import copy
import importlib.util
import io
import json
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
                      'origin': {'GITHUB_RUN_ID': '123', 'GITHUB_RUN_ATTEMPT': '1', 'GITHUB_SHA': 'fixture'}}
        self.execution = {'availableCpus': 2, 'cpuBudget': 2, 'requestedJobs': 1, 'jobs': 1,
                          'threadsPerWorker': 2, 'baselineThreads': 2, 'timeoutSeconds': 1200}
        self.version = {'version': 'synthetic-unit-fixture'}
        self.baseline = {'success': True, 'encountered-vir-error': False, 'encountered-error': False,
                         'verified': 40, 'errors': 0, 'is-verifying-entire-crate': True}
        self.negative = {**self.baseline, 'success': False, 'encountered-error': True, 'verified': 39, 'errors': 1}
        self.stack = contextlib.ExitStack()
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
                   '--triggers-mode', 'silent', '--num-threads', '2']
        if compile_only:
            command += ['--no-verify', '--compile', '-o', '/temporary/source/compile-check.rlib']
        SHARDS.save(directory / (stem + '.stdout.json'), {'verification-results': stats, 'verus': self.version})
        (directory / (stem + '.stderr.txt')).write_text('error: assertion failed\n' if code else '')
        SHARDS.save(directory / (stem + '.meta.json'), {
            'schema': 'cordis.negative-stage/v1', 'command': command, 'status': 'completed',
            'returncode': code, 'sourceSha256': source_hash, 'threads': 2, 'timeoutSeconds': 1200,
            'compileOnly': compile_only, 'durationSeconds': 0.1})

    def write_shard(self, index):
        directory = self.inputs / str(index)
        directory.mkdir()
        selected = SHARDS.assigned(self.manifest, index, 2)
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
            'schema': SHARDS.SCHEMA, 'status': 'passed', 'binding': self.bound,
            'shard': {'index': index, 'count': 2, 'names': [item[0] for item in selected]},
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
                       {'durationSeconds': -1}, {'returncode': True}, {'compileOnly': 0}]:
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


class SelectionTests(unittest.TestCase):
    def test_all_114_controls_are_partitioned_once_without_changing_each_control(self):
        manifest = CHECKS.mutation_manifest()
        self.assertEqual(len(manifest), 114)
        pieces = [SHARDS.assigned(manifest, index, 12) for index in range(12)]
        flattened = [item for group in pieces for item in group]
        self.assertEqual(len(flattened), 114)
        self.assertEqual(set(flattened), set(manifest))
        self.assertEqual(sorted(map(len, pieces)), [9] * 6 + [10] * 6)

    def test_invalid_shards_are_rejected(self):
        for index, count in [(0, 0), (-1, 2), (2, 2), (True, 2), (0, True), (0, 3)]:
            with self.subTest(index=index, count=count), self.assertRaises(RuntimeError):
                SHARDS.assigned(['one', 'two'], index, count)


if __name__ == '__main__':
    unittest.main()
