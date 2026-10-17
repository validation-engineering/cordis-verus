import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location("r2_acceptance", ROOT / "scripts/check-r2-acceptance.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)

class R2AcceptanceTests(unittest.TestCase):
    def log(self, result=None, node=None):
        return "R2_NATIVE_ACCEPTANCE " + json.dumps(result or checker.NATIVE_RESULT) + "\n" + (node or "ok 7 - " + checker.NODE_CASE) + "\n"

    def test_both_real_paths_are_required(self):
        evidence = checker.runtime_evidence(self.log())
        self.assertEqual(evidence["native"]["restored"], 10)
        with self.assertRaisesRegex(RuntimeError, "Node production"):
            checker.runtime_evidence(self.log(node="not ok 7 - " + checker.NODE_CASE))
        with self.assertRaisesRegex(RuntimeError, "Node production"):
            checker.runtime_evidence(self.log(node="ok 7 - " + checker.NODE_CASE + " # SKIP"))

    def test_incomplete_duplicate_or_wrong_native_result_is_rejected(self):
        incomplete = copy.deepcopy(checker.NATIVE_RESULT)
        incomplete["stages"].remove("blocked")
        with self.assertRaisesRegex(RuntimeError, "native production"):
            checker.runtime_evidence(self.log(incomplete))
        incomplete = copy.deepcopy(checker.NATIVE_RESULT)
        incomplete["restored"] = 13
        with self.assertRaisesRegex(RuntimeError, "native production"):
            checker.runtime_evidence(self.log(incomplete))
        with self.assertRaisesRegex(RuntimeError, "native production"):
            checker.runtime_evidence(self.log() + self.log())

    def test_omitted_mutation_fails_before_trusting_any_artifact(self):
        with self.assertRaisesRegex(RuntimeError, "missing or reordered"):
            checker.validate_cases({"cases": []}, [], None, Path("unused"))

    def test_fixed_selection_is_still_canonical_and_current(self):
        h = checker.module("r2_test_negatives", "check-negative-scoped.py")
        self.assertEqual([c["name"] for c in checker.selection(h)], list(checker.CASES))
        self.assertEqual(len(checker.CASES), 12)

    def test_new_running_record_invalidates_old_success(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            checker.save({"status": "passed", "development": "old"}, path)
            checker.save({"status": "running", "cases": []}, path)
            self.assertEqual(json.loads((path / "report.json").read_text()), {"status": "running", "cases": []})
            self.assertFalse((path / "report.json.tmp").exists())

if __name__ == "__main__":
    unittest.main()
