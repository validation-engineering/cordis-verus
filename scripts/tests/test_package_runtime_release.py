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

    def test_collection_requires_the_selected_platform_set(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(MODULE, 'run', return_value='a' * 40):
            with self.assertRaisesRegex(ValueError, 'All selected'):
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

    def platform_artifacts(self, inputs, target, commit='a' * 40):
        directory = inputs / target
        directory.mkdir(parents=True)
        (directory / 'install-cordis.mjs').write_bytes(b'installer')
        packages = []
        for name in sorted(MODULE.NAMES):
            path = directory / f'{target}-{name.split("/")[-1]}.tgz'
            path.write_bytes(name.encode())
            packages.append({**MODULE.asset(path), 'name': name, 'version': '0.1.0'})
        npm = {'status': 'passed', 'nativeTarget': target, 'nativeManifestSha256': 'manifest',
               'nativeArtifactSha256': 'binary', 'packages': packages}
        evidence = directory / f'cordis-evidence-{target}.json'
        MODULE.write(evidence, {'sourceCommit': commit, 'verification': self.report(), 'npm': npm})
        record = {'schema': 'cordis-verus.runtime-release/v1', 'sourceCommit': commit, 'target': target,
                  'nativeManifestSha256': 'manifest', 'nativeArtifactSha256': 'binary',
                  'acceptance': {'fullQuality': True, 'negativeControls': 0, 'paperCompletion': False},
                  'packages': packages, 'evidence': MODULE.asset(evidence)}
        manifest = directory / f'cordis-runtime-{target}.json'
        MODULE.write(manifest, record)
        return manifest

    def checkout(self, root):
        checkout = root / 'checkout'
        (checkout / 'scripts').mkdir(parents=True)
        (checkout / 'scripts/install-cordis.mjs').write_bytes(b'installer')
        return checkout

    def test_collection_accepts_default_pair_and_explicit_intel(self):
        for selection in [None, sorted(MODULE.DEFAULT_TARGETS), sorted(MODULE.TARGETS)]:
            with self.subTest(selection=selection), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                inputs, output = root / 'inputs', root / 'output'
                targets = MODULE.DEFAULT_TARGETS if selection is None else set(selection)
                for target in targets:
                    self.platform_artifacts(inputs, target)
                verifier = self.verifier()
                with patch.object(MODULE, 'ROOT', self.checkout(root)), patch.object(MODULE, 'run', return_value='a' * 40), \
                        patch.object(MODULE, 'verification_module', return_value=verifier):
                    MODULE.collect(inputs, output, 'a' * 40, selection)
                self.assertEqual(verifier.validate_negative_report.call_count, len(targets))
                self.assertEqual({path.name for path in output.glob('cordis-runtime-*.json')},
                                 {f'cordis-runtime-{target}.json' for target in targets})
                checksums = (output / 'SHA256SUMS').read_text().splitlines()
                self.assertEqual(len(checksums), len(targets) * 5 + 1)
                for line in checksums:
                    digest, filename = line.split('  ')
                    self.assertEqual(MODULE.digest(output / filename), digest)

    def test_target_selection_rejects_incomplete_unknown_duplicate_and_malformed_sets(self):
        selections = [[], ['linux-x64-gnu-napi8'], ['darwin-arm64-napi8'], ['darwin-x64-napi8'],
                      ['darwin-x64-napi8', 'linux-x64-gnu-napi8'],
                      [*sorted(MODULE.DEFAULT_TARGETS), 'windows-x64-napi8'],
                      [*sorted(MODULE.DEFAULT_TARGETS), 'darwin-arm64-napi8'],
                      'darwin-arm64-napi8', {}, [None], [['darwin-arm64-napi8']]]
        for selection in selections:
            with self.subTest(selection=selection), tempfile.TemporaryDirectory() as directory, \
                    patch.object(MODULE, 'verification_module') as verifier:
                root = Path(directory)
                with self.assertRaises(ValueError):
                    MODULE.collect(root, root / 'output', 'a' * 40, selection)
                verifier.assert_not_called()
                self.assertFalse((root / 'output').exists())

    def test_collection_rejects_missing_selected_and_extra_unselected_platforms(self):
        cases = [(MODULE.DEFAULT_TARGETS, sorted(MODULE.TARGETS), 'All selected'),
                 ({'linux-x64-gnu-napi8'}, None, 'All selected'),
                 (MODULE.TARGETS, None, 'unselected')]
        for artifacts, selection, error in cases:
            with self.subTest(artifacts=artifacts, selection=selection), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                inputs, output = root / 'inputs', root / 'output'
                for target in artifacts:
                    self.platform_artifacts(inputs, target)
                with patch.object(MODULE, 'ROOT', self.checkout(root)), patch.object(MODULE, 'run', return_value='a' * 40), \
                        patch.object(MODULE, 'verification_module', return_value=self.verifier()), \
                        self.assertRaisesRegex(ValueError, error):
                    MODULE.collect(inputs, output, 'a' * 40, selection)
                self.assertFalse(output.exists())

    def test_selected_platform_cannot_reuse_old_or_incomplete_quality_evidence(self):
        for failure in ['commit', 'source', 'negative', 'duplicate']:
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                inputs, output = root / 'inputs', root / 'output'
                for target in MODULE.DEFAULT_TARGETS:
                    self.platform_artifacts(inputs, target)
                manifest = inputs / 'darwin-arm64-napi8/cordis-runtime-darwin-arm64-napi8.json'
                record = MODULE.read(manifest)
                evidence_file = manifest.parent / record['evidence']['file']
                evidence = MODULE.read(evidence_file)
                verifier = self.verifier()
                if failure == 'commit':
                    evidence['sourceCommit'] = 'b' * 40
                elif failure == 'source':
                    evidence['verification']['sha256'] = {'stale': 'hash'}
                elif failure == 'negative':
                    verifier.validate_negative_report.side_effect = ValueError('missing full-crate negative control')
                else:
                    duplicate = inputs / 'duplicate'; duplicate.mkdir()
                    MODULE.write(duplicate / manifest.name, record)
                MODULE.write(evidence_file, evidence)
                record['evidence'] = MODULE.asset(evidence_file)
                MODULE.write(manifest, record)
                with patch.object(MODULE, 'ROOT', self.checkout(root)), patch.object(MODULE, 'run', return_value='a' * 40), \
                        patch.object(MODULE, 'verification_module', return_value=verifier), self.assertRaises(ValueError):
                    MODULE.collect(inputs, output, 'a' * 40)
                self.assertFalse(output.exists())

    def test_cli_target_selection_requires_a_valid_json_array(self):
        self.assertEqual(MODULE.parse_targets_json(json.dumps(sorted(MODULE.DEFAULT_TARGETS))),
                         sorted(MODULE.DEFAULT_TARGETS))
        for value in ['null', '{}', 'false', '"darwin-arm64-napi8"', '[', '[]',
                      json.dumps([*sorted(MODULE.TARGETS), 'darwin-x64-napi8'])]:
            with self.subTest(value=value), self.assertRaises(ValueError):
                MODULE.parse_targets_json(value)

    def test_cli_passes_explicit_targets_to_the_collector(self):
        with patch('sys.argv', ['package-runtime-release.py', 'collect', '--input', 'inputs', '--output', 'output',
                                '--commit', 'a' * 40, '--targets-json', json.dumps(sorted(MODULE.TARGETS))]), \
                patch.object(MODULE, 'collect') as collector:
            MODULE.main()
        collector.assert_called_once_with(Path('inputs'), Path('output'), 'a' * 40, sorted(MODULE.TARGETS))

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
