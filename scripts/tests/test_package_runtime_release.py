"""Release packaging must reject development and stale/incomplete evidence."""
import importlib.util
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

SPEC = importlib.util.spec_from_file_location('runtime_release', Path(__file__).resolve().parents[1] / 'package-runtime-release.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class RuntimeReleaseTests(unittest.TestCase):
    def verifier(self):
        return SimpleNamespace(validate_negative_report=Mock(), required_negative_names=lambda: ['one', 'two'], source_hashes=lambda: {'file': 'hash'})

    def report(self):
        return {'schema': 'cordis-verus.verification/v3', 'status': 'passed', 'proof': {}, 'negativeControls': [],
                'sha256': {'file': 'hash'}, 'paperCoverage': {'completionClaimed': False}}

    def test_full_quality_uses_the_canonical_negative_validator(self):
        verifier = self.verifier()
        record = self.report()
        MODULE.validate_quality(record, verifier)
        verifier.validate_negative_report.assert_called_once_with({'baseline': {}, 'mutations': []}, ['one', 'two'])
        verifier.validate_negative_report.side_effect = RuntimeError('missing negative control')
        with self.assertRaisesRegex(RuntimeError, 'missing negative'):
            MODULE.validate_quality(record, verifier)

    def test_development_stale_and_broadened_proof_claims_are_rejected(self):
        for changes in [{'schema': 'cordis-verus.development/v1'}, {'status': 'running'},
                        {'sha256': {'old': 'hash'}}, {'paperCoverage': {'completionClaimed': True}}]:
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                MODULE.validate_quality({**self.report(), **changes}, self.verifier())

    def test_asset_paths_and_bytes_are_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            file = root / 'package.tgz'; file.write_bytes(b'package')
            record = MODULE.asset(file)
            self.assertEqual(MODULE.checked_asset(root, record), file)
            file.write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'integrity'):
                MODULE.checked_asset(root, record)
            for path in ['../file', '/file', 'a/b', 'a\\b', '-argument']:
                with self.subTest(path=path), self.assertRaises(ValueError):
                    MODULE.safe_file(path)

    def test_collection_requires_the_complete_platform_set(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(MODULE, 'run', return_value='a' * 40):
            with self.assertRaisesRegex(ValueError, 'All three'):
                MODULE.collect(Path(directory), Path(directory) / 'output', 'a' * 40)
            self.assertFalse((Path(directory) / 'output').exists())

    def test_collection_rejects_mixed_commits_before_publication(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(MODULE, 'run', return_value='a' * 40):
            root = Path(directory)
            (root / 'cordis-runtime-darwin-arm64-napi8.json').write_text(json.dumps({
                'schema': 'cordis-verus.runtime-release/v1', 'target': 'darwin-arm64-napi8', 'sourceCommit': 'b' * 40}))
            with self.assertRaisesRegex(ValueError, 'mixed-commit'):
                MODULE.collect(root, root / 'output', 'a' * 40)
            self.assertFalse((root / 'output').exists())

    def test_publish_directory_preserves_complete_staged_contents(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); stage = root / 'stage'; stage.mkdir()
            (stage / 'manifest.json').write_text('evidence')
            output = root / 'output'
            MODULE.publish_directory(stage, output)
            self.assertFalse(stage.exists())
            self.assertEqual((output / 'manifest.json').read_text(), 'evidence')

    def test_publish_directory_does_not_replace_an_existing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); stage = root / 'stage'; stage.mkdir()
            output = root / 'output'; output.mkdir(); (output / 'keep').write_text('user data')
            with self.assertRaises(FileExistsError):
                MODULE.publish_directory(stage, output)
            self.assertEqual((output / 'keep').read_text(), 'user data')


if __name__ == '__main__':
    unittest.main()
