"""A native build on one platform cannot inherit another platform's runtime pass."""
from copy import deepcopy
import importlib.util
import io
import os
import sys
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('runtime_acceptance', Path(__file__).resolve().parents[1] / 'record-runtime.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class RuntimeAcceptanceTests(unittest.TestCase):
    def record(self):
        sources = {'kernel.rs': 'a' * 64}
        build = {'schema': 'cordis-verus.node-build/v1', 'platform': 'win32', 'architecture': 'x64',
                 'sourceHashes': sources, 'artifactSha256': 'b' * 64}
        return {'schema': MODULE.SCHEMA, 'status': 'passed', 'proofExecuted': False,
                'releaseAcceptance': False, 'sourceCommit': 'c' * 40, 'sha256': sources,
                'target': 'win32-x64-napi8', 'logSha256': 'd' * 64,
                'steps': [{'name': name, 'status': 'passed'} for name in MODULE.STEPS],
                'nodeBuild': build,
                'npmDistribution': {'schema': 'cordis-verus.npm-package/v1', 'status': 'passed', 'offline': True,
                                    'nativeSourceHashes': sources, 'nativeArtifactSha256': 'b' * 64,
                                    'nativeTarget': 'win32-x64-napi8'},
                'tests': {'total': 20, 'nodeCompatibility': {'tests': 10, 'pass': 10, 'fail': 0,
                                                          'cancelled': 0, 'skipped': 0, 'todo': 0}}}

    def validate(self, record):
        MODULE.validate(record, sources={'kernel.rs': 'a' * 64}, commit='c' * 40)

    def test_host_acceptance_preserves_the_separate_proof_requirement(self):
        self.validate(self.record())
        for key, value in [('status', 'running'), ('proofExecuted', True), ('releaseAcceptance', True),
                           ('sourceCommit', 'e' * 40), ('sha256', {'stale.rs': 'a' * 64})]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.validate({**self.record(), key: value})

    def test_missing_steps_skipped_tests_and_foreign_targets_are_rejected(self):
        for mutate in [lambda r: r['steps'].pop(),
                       lambda r: r['tests']['nodeCompatibility'].update(skipped=1),
                       lambda r: r['tests']['nodeCompatibility'].update({'pass': 9}),
                       lambda r: r['nodeBuild'].update(platform='linux'),
                       lambda r: r['npmDistribution'].update(nativeTarget='darwin-x64-napi8'),
                       lambda r: r['npmDistribution'].update(nativeArtifactSha256='e' * 64),
                       lambda r: r['npmDistribution'].update(nativeSourceHashes={'old.rs': 'a' * 64}),
                       lambda r: r.update(logSha256='')]:
            record = deepcopy(self.record()); mutate(record)
            with self.assertRaises(ValueError):
                self.validate(record)

    def test_failures_collect_later_checks_but_never_become_acceptance(self):
        checks = {name: [[sys.executable, '-c', 'print("ran")']] for name in MODULE.STEPS}
        checks['rust-tests'] = [[sys.executable, '-c', 'raise SystemExit(7)']]
        observed = []
        steps = MODULE.run_checks(checks, os.environ.copy(), io.StringIO(), lambda name, output: observed.append(name))
        self.assertIn('npm-packages', observed)
        self.assertEqual(next(step for step in steps if step['name'] == 'rust-tests')['status'], 'failed')
        record = self.record(); record['steps'] = steps
        with self.assertRaises(ValueError):
            self.validate(record)

        checks['native-build'] = [[sys.executable, '-c', 'raise SystemExit(8)']]
        observed.clear()
        steps = MODULE.run_checks(checks, os.environ.copy(), io.StringIO(), lambda name, output: observed.append(name))
        self.assertIn('crate-packages', observed)
        for name in ('node-tests', 'npm-packages'):
            self.assertNotIn(name, observed)
            self.assertEqual(next(step for step in steps if step['name'] == name)['status'], 'not_run')
        record['steps'] = steps
        with self.assertRaises(ValueError):
            self.validate(record)

    def test_windows_and_unix_rust_logs_have_identical_counts(self):
        verifier = MODULE.helpers()
        log = 'Running unittests src/lib.rs (target/debug/deps/cordis_kernel-0123)\ntest result: ok. 3 passed; 0 failed;\n'
        self.assertEqual(verifier.test_counts(log), verifier.test_counts(log.replace('/', '\\')))


if __name__ == '__main__':
    unittest.main()
