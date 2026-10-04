"""Regression tests for the proof evidence gate, independent of Verus itself."""
import contextlib
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import tempfile
import threading
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "check-negative.py"
SPEC = importlib.util.spec_from_file_location("negative_checks", SCRIPT)
CHECKS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKS)


def result(*, code=1, stderr="error: assertion failed", **changes):
    stats = {
        "success": False, "encountered-vir-error": False,
        "verified": 42, "errors": 1, "is-verifying-entire-crate": True,
    }
    stats.update(changes)
    return subprocess.CompletedProcess([], code, json.dumps({"verification-results": stats}), stderr)


class EvidenceGateTests(unittest.TestCase):
    def test_accepts_compiled_complete_crate_with_concrete_contract_failure(self):
        evidence = CHECKS.rejected_result("example", result())
        self.assertEqual(evidence["name"], "example")
        self.assertEqual(evidence["verification-results"]["verified"], 42)

    def test_rejects_success_partial_runs_and_frontend_errors(self):
        for changes in [
            {"code": 0}, {"success": True}, {"encountered-vir-error": True},
            {"verified": 0}, {"errors": 0}, {"is-verifying-entire-crate": False},
            {"verified": True}, {"errors": True}, {"success": 0},
        ]:
            with self.subTest(changes=changes), self.assertRaises(RuntimeError):
                CHECKS.rejected_result("example", result(**changes))

    def test_resource_exhaustion_is_not_a_contract_failure(self):
        with self.assertRaisesRegex(RuntimeError, "no conclusive contract failure"):
            CHECKS.rejected_result("example", result(stderr="error: Resource limit (rlimit) exceeded"))

    def test_contract_text_in_a_source_excerpt_is_not_a_diagnostic(self):
        diagnostic = "error: Resource limit (rlimit) exceeded\n 10 | // error: assertion failed"
        with self.assertRaisesRegex(RuntimeError, "no conclusive contract failure"):
            CHECKS.rejected_result("example", result(stderr=diagnostic))

    def test_a_contract_failure_does_not_hide_resource_exhaustion_or_a_crash(self):
        for failure in [
            "error: function body check: Resource limit (rlimit) exceeded",
            "error: solver returned unknown",
            "error: verification timed out",
            "thread 'main' panicked at internal compiler error",
            "error: out of memory",
        ]:
            with self.subTest(failure=failure), self.assertRaisesRegex(RuntimeError, "resource or compiler failure"):
                CHECKS.rejected_result("example", result(stderr="error: assertion failed\n" + failure))

    def test_resource_words_in_source_excerpts_do_not_invalidate_a_contract(self):
        diagnostic = "error: assertion failed\n 10 | // previously hit a resource limit (rlimit)\n   | ^^^^^^^^^"
        self.assertEqual(CHECKS.rejected_result("example", result(stderr=diagnostic))["name"], "example")

    def test_malformed_or_incomplete_reports_are_rejected(self):
        for stdout in ["not JSON", "{}", '{"verification-results": {}}', '{"verification-results": null}']:
            with self.subTest(stdout=stdout), self.assertRaises(RuntimeError):
                CHECKS.rejected_result("example", subprocess.CompletedProcess([], 1, stdout, "error: assertion failed"))


class IsolatedRunnerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="cordis-negative-test-")
        self.root = Path(self.temporary.name)
        self.baseline = self.root / "baseline"
        self.baseline.mkdir()
        (self.baseline / "lib.rs").write_text("pub const TAG: u8 = 0;\n")
        self.reports = self.root / "reports"
        self.reports.mkdir()
        self.mutation = ("example", "lib.rs", "= 0", "= 1")

    def tearDown(self):
        self.temporary.cleanup()

    def run_one(self, runner, mutation=None):
        return CHECKS.check_mutation(mutation or self.mutation, self.baseline, self.root,
                                     self.reports, "unused-verus", {}, runner=runner)

    def test_compile_failure_cannot_be_counted_as_proof_rejection(self):
        calls = []

        def runner(*args, **kwargs):
            calls.append(args)
            return result(stderr="error: unknown identifier")

        with self.assertRaisesRegex(RuntimeError, "did not compile"):
            self.run_one(runner)
        self.assertEqual(len(calls), 1)

    def test_timeout_cannot_be_counted_as_proof_rejection(self):
        def runner(*args, **kwargs):
            raise subprocess.TimeoutExpired("verus", 1)

        with self.assertRaisesRegex(RuntimeError, "timed out"):
            self.run_one(runner)

    def test_timeout_preserves_partial_output_without_accepting_evidence(self):
        prefix = self.reports / "interrupted"
        error = subprocess.TimeoutExpired("verus", 600, output=b'{"unfinished":', stderr=b'partial diagnostic')
        with patch.object(CHECKS.subprocess, "run", side_effect=error):
            with self.assertRaises(subprocess.TimeoutExpired):
                CHECKS.run_verus("verus", {}, self.baseline / "lib.rs", prefix)
        self.assertEqual(prefix.with_suffix(".stdout.json").read_text(), '{"unfinished":')
        self.assertEqual(prefix.with_suffix(".stderr.txt").read_text(), 'partial diagnostic')
        self.assertFalse((self.reports / "report.json").exists())

    def test_changed_mutation_anchor_is_rejected_before_compilation(self):
        def runner(*args, **kwargs):
            self.fail("A stale mutation must not invoke the compiler")

        with self.assertRaisesRegex(RuntimeError, "exactly one source match"):
            self.run_one(runner, ("missing", "lib.rs", "not present", "replacement"))

    def test_workers_use_isolated_trees_and_keep_manifest_order(self):
        barrier = threading.Barrier(2)
        second_done = threading.Event()
        mutations = [("first", "lib.rs", "= 0", "= 1"), ("second", "lib.rs", "= 0", "= 2")]
        completed = []

        def runner(binary, environment, source, report_path, compile_only=False, **kwargs):
            name = source.parent.name
            expected = 1 if name == "first" else 2
            self.assertEqual(source.read_text(), f"pub const TAG: u8 = {expected};\n")
            self.assertEqual(kwargs["threads"], 4)
            self.assertEqual(kwargs["timeout"], 240)
            if compile_only:
                return subprocess.CompletedProcess([], 0, "", "")
            barrier.wait(timeout=5)
            if name == "first":
                self.assertTrue(second_done.wait(timeout=5))
            completed.append(name)
            if name == "second":
                second_done.set()
            return result()

        with contextlib.redirect_stdout(io.StringIO()):
            evidence = CHECKS.check_mutations(mutations, self.baseline, self.root, self.reports,
                                              "unused-verus", {}, jobs=2, threads=4, timeout=240, runner=runner)
        self.assertEqual(completed, ["second", "first"])
        self.assertEqual([row["name"] for row in evidence], ["first", "second"])
        self.assertEqual((self.baseline / "lib.rs").read_text(), "pub const TAG: u8 = 0;\n")


if __name__ == "__main__":
    unittest.main()
