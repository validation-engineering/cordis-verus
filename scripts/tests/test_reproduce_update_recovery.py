"""Evidence must distinguish the actual host scenario from the native scenario."""
from contextlib import redirect_stdout
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('update_recovery_reproduction', ROOT / 'scripts/reproduce-update-recovery.py')
REPRODUCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(REPRODUCE)


class ReproductionEvidenceTests(unittest.TestCase):
    def exercise(self, wrong_host):
        calls = []

        def cargo(command, **_kwargs):
            calls.append(command)
            if '--example' in command:
                package = command[command.index('-p') + 1]
                label = 'native' if package == 'cordis-kernel' else 'host'
                if wrong_host:
                    label = 'native'
                stdout = json.dumps({'schema': f'cordis-verus.update-recovery-{label}/v1', 'status': 'passed'})
            else:
                stdout = 'test result: ok.\n'
            return subprocess.CompletedProcess(command, 0, stdout, '')

        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / 'evidence'
            with patch.object(REPRODUCE, 'ROOT', Path(directory)), \
                    patch.object(REPRODUCE, 'OUTPUT', output), \
                    patch.object(REPRODUCE, 'sources', return_value={'source.rs': 'fixed'}), \
                    patch.object(REPRODUCE.subprocess, 'run', side_effect=cargo), \
                    patch.object(sys, 'argv', ['reproduce-update-recovery.py', '--offline']), \
                    redirect_stdout(io.StringIO()):
                if wrong_host:
                    with self.assertRaisesRegex(RuntimeError, 'host did not complete the expected scenario'):
                        REPRODUCE.main()
                else:
                    REPRODUCE.main()
            return json.loads((output / 'report.json').read_text()), calls

    def test_success_records_distinct_examples_and_does_not_claim_unrun_proofs(self):
        report, calls = self.exercise(False)
        self.assertEqual(report['status'], 'passed')
        self.assertEqual([c[c.index('--example') + 1] for c in calls if '--example' in c],
                         ['update_recovery_native', 'update_recovery'])
        self.assertEqual(report['proof'], {'status': 'not_run'})
        self.assertFalse(report['paperCompletion'])
        self.assertFalse(report['r01Completion'])
        self.assertEqual(len(report['runs']), 3)
        self.assertTrue(all(row['returncode'] == 0 and row['stdoutSha256'] for row in report['runs']))

    def test_native_success_cannot_be_recorded_as_host_evidence(self):
        report, calls = self.exercise(True)
        self.assertEqual(report['status'], 'failed')
        self.assertNotIn('host', report)
        self.assertEqual(len(calls), 2)
        self.assertEqual(report['proof'], {'status': 'not_run'})


class ProofScopeTests(unittest.TestCase):
    def output(self, extra=None, work=True):
        modules = [*REPRODUCE.PROOF_MODULES, *([extra] if extra else [])]
        return {
            'verification-results': {'errors': 0, 'verified': 35, 'encountered-error': False,
                                     'encountered-vir-error': False, 'is-verifying-entire-crate': False},
            'times-ms': {'smt': {'smt-run-module-times': [
                {'module': name, 'function-breakdown': [
                    {'success': True, 'time-micros': 1 if work else 0, 'rlimit': 0}]
                } for name in modules]}},
        }

    def test_successful_zero_work_entries_do_not_establish_module_coverage(self):
        with self.assertRaisesRegex(RuntimeError, 'no actual proof work'):
            REPRODUCE.checked_proof(self.output(work=False))

    def test_unexpected_module_work_rejects_an_otherwise_successful_summary(self):
        REPRODUCE.checked_proof(self.output())
        with self.assertRaisesRegex(RuntimeError, 'outside the selected modules'):
            REPRODUCE.checked_proof(self.output(extra='unselected'))


if __name__ == '__main__':
    unittest.main()
