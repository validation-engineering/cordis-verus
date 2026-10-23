"""Profile selection and source binding must fail closed before invoking Verus."""
from contextlib import redirect_stderr, redirect_stdout
import copy
import importlib.util
import io
from pathlib import Path
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('profile_controls', ROOT / 'scripts/check-profile-controls.py')
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)


class ProfileControls(unittest.TestCase):
    def setUp(self):
        self.h = M.module('test_profile_scoped', 'check-negative-scoped.py')
        self.canonical = M.module('test_profile_canonical', 'check-negative.py')
        self.loader = patch.object(M, 'module', side_effect=lambda _name, filename: {
            'check-negative-scoped.py': self.h, 'check-negative.py': self.canonical,
        }[filename])
        self.loader.start()
        self.addCleanup(self.loader.stop)

    def test_every_profile_resolves_real_mutations_and_nested_diagnostic_anchors(self):
        for profile in M.PROFILES:
            with self.subTest(profile=profile):
                M.load_profile(profile)

    def test_unknown_profile_is_rejected_before_loading_tools(self):
        with patch.object(M, 'module') as load:
            with self.assertRaises(ValueError):
                M.load_profile('../episode')
            with redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as failure:
                M.main(['../episode'])
            self.assertEqual(failure.exception.code, 2)
            load.assert_not_called()

    def test_selection_cannot_silently_drop_or_reorder_controls(self):
        _, _, manifest, _, _ = M.load_profile('update-recovery')
        for cases in (manifest['cases'][1:], list(reversed(manifest['cases']))):
            candidate = copy.deepcopy(manifest)
            candidate['cases'] = cases
            with patch.object(self.h, 'load_json', return_value=candidate):
                with self.assertRaisesRegex(RuntimeError, 'Control selection changed'):
                    M.load_profile('update-recovery')

    def test_profile_cannot_substitute_another_mutation_for_a_named_control(self):
        _, _, manifest, _, _ = M.load_profile('episode')
        candidate = copy.deepcopy(manifest)
        candidate['cases'][0]['mutation']['new'] += '\n// different mutation'
        with patch.object(self.h, 'load_json', return_value=candidate):
            with self.assertRaisesRegex(RuntimeError, 'canonical control'):
                M.load_profile('episode')

    def test_missing_diagnostic_anchor_is_rejected(self):
        _, _, manifest, _, _ = M.load_profile('update-recovery')
        candidate = copy.deepcopy(manifest)
        candidate['cases'][0]['expectedFailures'][0]['uniqueSourceAnchor'] = 'missing reviewed anchor'
        with patch.object(self.h, 'load_json', return_value=candidate):
            with self.assertRaises(RuntimeError):
                M.load_profile('update-recovery')

    def test_check_only_does_not_invoke_verifier_or_create_evidence(self):
        output = io.StringIO()
        with patch.object(self.h, 'tools_for') as tools, patch.object(M.tempfile, 'mkdtemp') as directory:
            with redirect_stdout(output):
                M.main(['update-recovery', '--check'])
            tools.assert_not_called()
            directory.assert_not_called()
        self.assertIn('proofs not run', output.getvalue())


if __name__ == '__main__':
    unittest.main()
