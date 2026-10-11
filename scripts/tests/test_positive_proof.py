"""Positive acceptance requires fresh, complete, compiled, bound proof output."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from contextlib import redirect_stdout
import io
from types import SimpleNamespace

from evidence_fixtures import LOCK, positive, release

ROOT = Path(__file__).resolve().parents[2]


def load(name):
    path = ROOT / 'scripts' / name
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


POSITIVE = load('check-positive.py')
RELEASE = load('record-verification.py')


class PositiveProofTests(unittest.TestCase):
    def test_portable_record_requires_full_proof_compilation_and_pinned_tools(self):
        original = positive()
        POSITIVE.validate(original, sources=original['sourceHashes'], lock=LOCK)
        changes = [lambda r: r.update(status='running'), lambda r: r.update(compiled=False),
                   lambda r: r.update(noCheating=False), lambda r: r.update(returncode=True),
                   lambda r: r['command'].append('--no-verify'), lambda r: r['toolHashes'].pop('z3'),
                   lambda r: r['verus'].update(commit='old'), lambda r: r['artifact'].update(bytes=0),
                   lambda r: r['artifact'].update(sha256='not-a-hash'), lambda r: r.update(sourceHashes={})]
        for stats in [{'verified': 0}, {'verified': True}, {'errors': True}, {'success': False},
                      {'encountered-vir-error': True}, {'encountered-error': True}, {'is-verifying-entire-crate': False}]:
            changes.append(lambda r, stats=stats: r['proof'].update(stats))
        for change in changes:
            candidate = copy.deepcopy(original); change(candidate)
            with self.subTest(candidate=candidate), self.assertRaises(RuntimeError):
                POSITIVE.validate(candidate, sources=original['sourceHashes'], lock=LOCK)

    def test_runner_invalidates_prior_success_and_requires_fresh_artifact_and_raw_evidence(self):
        for failure in (None, 'exit', 'missing-artifact', 'partial', 'source-change'):
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary); out = root / 'target/positive-proof'; out.mkdir(parents=True)
                report = out / 'report.json'; report.write_text(json.dumps(positive()))
                artifact = root / POSITIVE.ARTIFACT; artifact.parent.mkdir(); artifact.write_bytes(b'old')
                (root / 'toolchain.lock.json').write_text(json.dumps(LOCK))
                bound = {key: positive()[key] for key in ('sourceHashes', 'toolHashes')}
                def verify(command, **kwargs):
                    self.assertEqual(command, POSITIVE.COMMAND)
                    self.assertFalse(artifact.exists())
                    self.assertEqual(json.loads(report.read_text())['status'], 'running')
                    if failure != 'missing-artifact': artifact.write_bytes(b'compiled')
                    raw = {'verification-results': positive()['proof'], 'verus': positive()['verus']}
                    if failure == 'partial': raw['verification-results']['is-verifying-entire-crate'] = False
                    kwargs['stdout'].write(json.dumps(raw)); kwargs['stderr'].write('')
                    return SimpleNamespace(returncode=1 if failure == 'exit' else 0)
                with patch.object(POSITIVE, 'ROOT', root), patch.object(POSITIVE, 'inputs', side_effect=[bound, {} if failure == 'source-change' else bound]), \
                        patch.object(POSITIVE.subprocess, 'run', side_effect=verify), redirect_stdout(io.StringIO()):
                    if failure is None:
                        POSITIVE.main()
                        self.assertEqual(json.loads(report.read_text())['status'], 'passed')
                        # Post-run tampering must fail even if the report still says passed.
                        (out / 'stdout.json').write_text('{}')
                        with self.assertRaisesRegex(RuntimeError, 'output changed'):
                            POSITIVE.read_evidence(sources=bound['sourceHashes'])
                    else:
                        with self.assertRaises((RuntimeError, FileNotFoundError)): POSITIVE.main()
                        self.assertEqual(json.loads(report.read_text())['status'], 'failed')


class ReleaseAcceptanceTests(unittest.TestCase):
    def test_new_schema_accepts_positive_proof_without_claiming_negative_execution(self):
        RELEASE.validate_release_report(release())

    def test_development_legacy_skipped_runtime_and_misleading_negative_evidence_fail_closed(self):
        changes = [lambda r: r.update(schema='cordis-verus.verification/v3'),
                   lambda r: r.update(releaseAcceptance=False), lambda r: r.update(proofExecution={}),
                   lambda r: r['negativeControls'].update(status='passed'), lambda r: r.update(negativeControls=[]),
                   lambda r: r['paperCoverage'].update(completionClaimed=True),
                   lambda r: r['tests'].update(total=0), lambda r: r['tests']['nodeCompatibility'].update(skipped=1),
                   lambda r: r['npmDistribution'].update(offline=False), lambda r: r.update(nodeBuild={})]
        for change in changes:
            candidate = release(); change(candidate)
            with self.subTest(candidate=candidate), self.assertRaises(RuntimeError):
                RELEASE.validate_release_report(candidate)


if __name__ == '__main__':
    unittest.main()
