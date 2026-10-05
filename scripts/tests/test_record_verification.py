"""Release evidence must match the complete, current mutation manifest."""
import copy
import importlib.util
from pathlib import Path
import unittest
import tempfile
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "record-verification.py"
SPEC = importlib.util.spec_from_file_location("verification_record", SCRIPT)
RECORD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RECORD)


def report(names):
    positive = {"success": True, "errors": 0, "verified": 40,
                "encountered-vir-error": False, "is-verifying-entire-crate": True}
    negative = {**positive, "success": False, "errors": 1, "verified": 39}
    return {"baseline": positive, "mutations": [
        {"name": name, "compiles": True, "verification-results": negative.copy()} for name in names
    ]}


class CompleteRecordTests(unittest.TestCase):
    def test_accepts_every_control_in_manifest_order(self):
        names = RECORD.required_negative_names()
        self.assertGreater(len(names), 5)
        RECORD.validate_negative_report(report(names), names)

    def test_rejects_missing_duplicate_extra_and_reordered_controls(self):
        expected = ["first", "second", "third", "fourth", "fifth", "sixth"]
        for recorded in [expected[:5], expected + ["extra"], expected[:-1] + ["first"], list(reversed(expected))]:
            with self.subTest(recorded=recorded), self.assertRaisesRegex(RuntimeError, "manifest"):
                RECORD.validate_negative_report(report(recorded), expected)

    def test_rejects_partial_or_failed_positive_baseline(self):
        original = report(["one"])
        for change in [{"success": False}, {"errors": 1}, {"errors": False}, {"verified": 0}, {"verified": True}, {"verified": "40"},
                       {"encountered-vir-error": True}, {"is-verifying-entire-crate": False}]:
            candidate = copy.deepcopy(original)
            candidate["baseline"].update(change)
            with self.subTest(change=change), self.assertRaisesRegex(RuntimeError, "positive"):
                RECORD.validate_negative_report(candidate, ["one"])

    def test_rejects_uncompiled_or_nonconclusive_control_stats(self):
        original = report(["one"])
        for change in [{"success": True}, {"errors": 0}, {"verified": 0}, {"verified": True}, {"verified": "40"},
                       {"encountered-vir-error": True}, {"is-verifying-entire-crate": False}]:
            candidate = copy.deepcopy(original)
            candidate["mutations"][0]["verification-results"].update(change)
            with self.subTest(change=change), self.assertRaisesRegex(RuntimeError, "negative"):
                RECORD.validate_negative_report(candidate, ["one"])
        original["mutations"][0]["compiles"] = False
        with self.assertRaisesRegex(RuntimeError, "negative"):
            RECORD.validate_negative_report(original, ["one"])

    def test_rejects_empty_or_ambiguous_manifest(self):
        for expected in [[], ["same", "same"]]:
            with self.subTest(expected=expected), self.assertRaisesRegex(RuntimeError, "manifest"):
                RECORD.validate_negative_report(report(expected), expected)


class NativeEvidenceInputTests(unittest.TestCase):
    def test_hashes_javascript_types_and_locks_but_not_node_modules_or_binaries(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixtures = ["packages/compat-cordis/runtime.js", "packages/compat-cordis/index.cjs",
                        "packages/compat-cordis/index.d.ts", "scripts/build-node.mjs",
                        "tests/node-compat/lifecycle.test.mjs", "tests/node-compat/types.tsx",
                        "package-lock.json", "node_modules/vendor/index.js",
                        "packages/compat-cordis/node_modules/vendor/index.js",
                        "packages/compat-cordis/native/cordis.node", "target/node-compat/build.json",
                        "packages/compat-cordis/native/manifest.json",
                        "packages/compat-cordis/native/provenance/darwin-arm64-napi8.json"]
            for name in fixtures:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(name)
            with patch.object(RECORD, "ROOT", root):
                hashes = RECORD.source_hashes()
            self.assertEqual(set(hashes), set(fixtures[:7]))

    def test_unit_test_counts_keep_all_workspace_crates_separate(self):
        lines = []
        for name, count in (("cordis", 2), ("cordis_kernel", 3), ("cordis_driver", 5), ("cordis_node", 7)):
            lines.extend([f"Running unittests src/lib.rs (target/debug/deps/{name}-abc012)",
                          f"test result: ok. {count} passed; 0 failed;"])
        counts = RECORD.test_counts("\n".join(lines))
        self.assertEqual(counts["suites"], {"host_unit": 2, "kernel_unit": 3, "cordis_driver_unit": 5, "cordis_node_unit": 7})
        self.assertEqual(counts["total"], 17)


if __name__ == "__main__":
    unittest.main()
