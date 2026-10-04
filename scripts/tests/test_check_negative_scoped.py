"""No verifier processes: strict gates, synthetic pipeline, historical parser fixtures."""
import copy
from contextlib import nullcontext
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("scoped_negative", ROOT / "scripts/check-negative-scoped.py")
S = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(S)
TOOL = {"binary": "/fake/verus", "version": "test-version", "commit": "test-commit"}
FUNCTION = "cordis_negative::consumer::reject"


def manifest():
    return {"schema": S.MANIFEST_SCHEMA, "negativeMode": "scoped-negative", "cases": [{
        "name": "wrong-value", "mutation": {"file": "lib.rs", "old": "original", "new": "mutated"},
        "targets": [{"kind": "module", "path": "consumer", "descendants": True}],
        "expectedFailures": [{"function": FUNCTION, "module": "consumer", "file": "consumer.rs",
                              "diagnosticKind": "postcondition not satisfied", "uniqueSourceAnchor": "ensures safe,"}],
        "selectionRationale": "Audited consumer; modifying lib.rs does not identify this proof."}]}


def payload(*, entire=False, failed=False):
    stats = {"verified": 1, "errors": int(failed), "encountered-vir-error": False,
             "encountered-error": failed, "is-verifying-entire-crate": entire}
    if entire:
        stats["success"] = not failed
    return {"verification-results": stats, "verus": TOOL,
            "times-ms": {"smt": {"smt-run-module-times": [{"module": "consumer", "function-breakdown": [
                {"function": FUNCTION, "success": not failed, "time-micros": 10, "rlimit": 100}]}]}}}


class Gates(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "baseline"
        self.source.mkdir()
        (self.source / "lib.rs").write_text("original\n")
        (self.source / "consumer.rs").write_text("pub proof fn reject()\nensures safe,\n{}\n")
        self.reports = self.root / "reports"
        self.reports.mkdir()
        self.counter = 0
        self.manifest = manifest()
        self.case = self.manifest["cases"][0]
        self.tool_check = patch.object(S, "verify_tool_artifacts", return_value=None)
        self.tool_check.start()
        self.addCleanup(self.tool_check.stop)

    def record(self, value=None, stderr="", code=0, command=None):
        self.counter += 1
        prefix = str(self.counter)
        out = self.reports / (prefix + ".stdout.json")
        err = self.reports / (prefix + ".stderr.txt")
        out.write_text(json.dumps(value if value is not None else payload()))
        err.write_text(stderr)
        return {"command": command or [], "timedOut": False, "interrupted": False, "returncode": code,
                "stdout": out.name, "stdoutSha256": S.digest(out),
                "stderr": err.name, "stderrSha256": S.digest(err)}

    def rejection(self, *, source=None, value=None, stderr=None):
        source = source or self.source
        if stderr is None:
            stderr = f"error: postcondition not satisfied\n  --> {source}/consumer.rs:2:1\nerror: aborting due to 1 previous error\n"
        return self.record(value or payload(failed=True), stderr, 1)

    def validate(self, record):
        return S.validate_rejection(record, self.reports, self.case, self.source, TOOL)

    def test_manifest_valid(self):
        S.validate_manifest(self.manifest)
        S.preflight(self.manifest, self.source)

    def test_manifest_rejects_missing_unknown_duplicate_empty_and_out_of_scope(self):
        candidates = []
        for key in self.case:
            candidate = manifest()
            del candidate["cases"][0][key]
            candidates.append(candidate)
        candidate = manifest(); candidate["unknown"] = 1; candidates.append(candidate)
        candidate = manifest(); candidate["cases"] *= 2; candidates.append(candidate)
        candidate = manifest(); candidate["cases"][0]["targets"] = []; candidates.append(candidate)
        candidate = manifest(); candidate["cases"][0]["targets"] *= 2; candidates.append(candidate)
        candidate = manifest(); candidate["cases"][0]["expectedFailures"][0]["module"] = "other"; candidates.append(candidate)
        candidate = manifest(); candidate["cases"][0]["mutation"]["file"] = "../escape.rs"; candidates.append(candidate)
        candidate = manifest(); candidate["cases"][0]["targets"][0]["path"] = "--no-verify"; candidates.append(candidate)
        for candidate in candidates:
            with self.subTest(candidate=candidate), self.assertRaises(RuntimeError):
                S.validate_manifest(candidate)

    def test_nested_and_root_targets_are_explicit(self):
        targets = [{"kind": "module", "path": "mixed_driver::fresh::admitted", "descendants": False}, {"kind": "root", "timingModule": "root"}]
        self.assertEqual(S.selectors(targets), ["--verify-only-module", "mixed_driver::fresh::admitted", "--verify-root"])
        self.assertTrue(S.covered("root", targets))
        self.assertFalse(S.covered("mixed_driver::fresh::admitted::script", targets))

    def test_strict_counts_flags_and_positive_scope(self):
        for entire in (True, False):
            original = payload(entire=entire)
            S.validate_positive(self.record(original), self.reports, entire=entire, expected_tool=TOOL)
            for change in ({"verified": True}, {"verified": 0}, {"errors": False}, {"errors": 1},
                           {"encountered-vir-error": True}, {"encountered-error": True},
                           {"success": False}, {"is-verifying-entire-crate": not entire}):
                value = copy.deepcopy(original); value["verification-results"].update(change)
                with self.subTest(entire=entire, change=change), self.assertRaises(RuntimeError):
                    S.validate_positive(self.record(value), self.reports, entire=entire, expected_tool=TOOL)

    def test_positive_rejects_unknown_target_even_when_another_has_proofs(self):
        targets = self.case["targets"] + [{"kind": "module", "path": "typo", "descendants": True}]
        with self.assertRaisesRegex(RuntimeError, "no timed proof"):
            S.validate_positive(self.record(), self.reports, entire=False, targets=targets)

    def test_positive_rejects_failed_timing_or_unselected_function(self):
        value = payload(); value["times-ms"]["smt"]["smt-run-module-times"][0]["function-breakdown"][0]["success"] = False
        with self.assertRaisesRegex(RuntimeError, "failed timed"):
            S.validate_positive(self.record(value), self.reports, entire=False)
        with self.assertRaisesRegex(RuntimeError, "no timed proof"):
            S.validate_positive(self.record(), self.reports, entire=False, targets=[{"kind": "root", "timingModule": "root"}])

    def test_positive_requires_exact_expected_function_not_only_module(self):
        value = payload()
        value["times-ms"]["smt"]["smt-run-module-times"][0]["function-breakdown"][0]["function"] = "cordis_negative::consumer::unrelated"
        with self.assertRaisesRegex(RuntimeError, "not proved"):
            S.validate_positive(self.record(value), self.reports, entire=False,
                                targets=self.case["targets"], expected_failures=self.case["expectedFailures"])

    def test_method_belongs_to_timing_module_not_type_path(self):
        value = payload()
        value["times-ms"]["smt"]["smt-run-module-times"][0].update({
            "module": "root", "function-breakdown": [{"function": "cordis_negative::Kernel::retire", "success": True, "time-micros": 10, "rlimit": 100}]})
        S.validate_positive(self.record(value), self.reports, entire=False,
                            targets=[{"kind": "root", "timingModule": "root"}],
                            expected_failures=[{"function": "cordis_negative::Kernel::retire", "module": "root"}])

    def test_multiple_failure_functions_not_silently_paired_to_spans(self):
        candidate = manifest()
        failure = copy.deepcopy(candidate["cases"][0]["expectedFailures"][0])
        failure["function"] = "cordis_negative::consumer::other"
        candidate["cases"][0]["expectedFailures"].append(failure)
        with self.assertRaisesRegex(RuntimeError, "exactly one"):
            S.validate_manifest(candidate)

    def test_rejection_without_success_is_accepted_and_not_rewritten(self):
        stats = self.validate(self.rejection())
        self.assertNotIn("success", stats)

    def test_rejection_strict_flags_and_counts(self):
        for change in ({"verified": True}, {"errors": True}, {"errors": 0}, {"errors": 2},
                       {"encountered-vir-error": True}, {"encountered-error": False}, {"success": True},
                       {"is-verifying-entire-crate": True}):
            value = payload(failed=True); value["verification-results"].update(change)
            with self.subTest(change=change), self.assertRaises(RuntimeError):
                self.validate(self.rejection(value=value))

    def test_zero_successful_mutant_proofs_can_still_have_a_conclusive_failure(self):
        value = payload(failed=True); value["verification-results"]["verified"] = 0
        self.validate(self.rejection(value=value))

    def test_wrong_function_or_missing_timing_rejected(self):
        value = payload(failed=True)
        value["times-ms"]["smt"]["smt-run-module-times"][0]["function-breakdown"][0]["function"] = "cordis_negative::consumer::other"
        with self.assertRaisesRegex(RuntimeError, "function set"):
            self.validate(self.rejection(value=value))
        del value["times-ms"]
        with self.assertRaisesRegex(RuntimeError, "attribution"):
            self.validate(self.rejection(value=value))

    def test_expected_function_plus_other_contract_or_resource_failure_rejected(self):
        for trailer in ("error: rlimit exceeded", "error[E0308]: mismatched types",
                        "error: assertion failed\n  --> /elsewhere/file.rs:3:2", "note: solver returned unknown",
                        "error: internal compiler error", "error: verification timed out",
                        "thread 'rustc' panicked at bad", "    resource limit exceeded", "Segmentation fault"):
            stderr = f"error: postcondition not satisfied\n --> {self.source}/consumer.rs:2:1\n{trailer}\n"
            with self.subTest(trailer=trailer), self.assertRaises(RuntimeError):
                self.validate(self.rejection(stderr=stderr))

    def test_excerpt_is_not_contract_and_primary_location_must_match(self):
        for stderr in ("9 | // error: postcondition not satisfied\n",
                       f"error: postcondition not satisfied\n --> {self.source}/consumer.rs:3:1\n",
                       f"error: postcondition not satisfied\n --> {self.source}/lib.rs:2:1\n",
                       "error: postcondition not satisfied\n --> /other/consumer.rs:2:1\n"):
            with self.subTest(stderr=stderr), self.assertRaises(RuntimeError):
                self.validate(self.rejection(stderr=stderr))

    def test_timeout_signal_and_zero_exit_are_never_rejections(self):
        for change in ({"timedOut": True}, {"returncode": -9}, {"returncode": 0}, {"returncode": True}):
            record = self.rejection(); record.update(change)
            with self.subTest(change=change), self.assertRaises(RuntimeError):
                self.validate(record)

    def test_malformed_json_and_changed_logs_rejected(self):
        record = self.rejection()
        (self.reports / record["stdout"]).write_text("not JSON")
        with self.assertRaisesRegex(RuntimeError, "raw output changed"):
            self.validate(record)
        record["stdoutSha256"] = S.digest(self.reports / record["stdout"])
        with self.assertRaisesRegex(RuntimeError, "malformed"):
            self.validate(record)

    def test_unique_anchors_and_symlinks_are_required(self):
        (self.source / "lib.rs").write_text("original original")
        with self.assertRaisesRegex(RuntimeError, "mutation anchor"):
            S.preflight(self.manifest, self.source)
        (self.source / "lib.rs").write_text("original")
        (self.source / "consumer.rs").write_text("ensures safe,\nensures safe,")
        with self.assertRaisesRegex(RuntimeError, "diagnostic anchor"):
            S.preflight(self.manifest, self.source)
        (self.source / "alias.rs").symlink_to(self.source / "lib.rs")
        with self.assertRaisesRegex(RuntimeError, "symlink"):
            S.source_hashes(self.source)

    def test_compile_requires_artifact_and_no_selector(self):
        artifact = self.root / "compiled.rlib"
        record = self.record()
        with self.assertRaisesRegex(RuntimeError, "artifact"):
            S.validate_compile(record, self.reports, artifact)
        artifact.write_bytes(b"compiled")
        S.validate_compile(record, self.reports, artifact)
        with self.assertRaisesRegex(RuntimeError, "whole crate"):
            S.command("/verus", self.source, "compile", self.case["targets"], 1, artifact)

    def fake_runner(self, command, environment, prefix, timeout):
        source = Path(command[1]).parent
        if "--no-verify" in command:
            Path(command[-1]).write_bytes(b"fake compiler artifact, not proof evidence")
            return self.record({}, command=command)
        selected = any(flag in command for flag in ("--verify-module", "--verify-only-module", "--verify-root"))
        failed = selected and source.name != "baseline"
        stderr = f"error: postcondition not satisfied\n --> {source}/consumer.rs:2:1\n" if failed else ""
        return self.record(payload(entire=not selected, failed=failed), stderr, int(failed), command)

    def pipeline(self, runner=None):
        run_binding = S.binding(self.source, self.manifest, TOOL, 1, 600)
        return S.execute(self.manifest, self.source, self.root, self.reports, Path("/fake/verus"), {}, TOOL,
                         run_binding, purpose="calibration", canonical_count=1, runner=runner or self.fake_runner)

    def test_mock_pipeline_scopes_and_calibration_replay(self):
        report = self.pipeline()
        self.assertEqual(report["status"], "passed")
        self.assertIs(report["is-verifying-entire-crate"], False)
        self.assertEqual(report["selectedControlCount"], 1)
        self.assertEqual(report["canonicalControlCount"], 1)
        records = [report["wholePositive"], report["cases"][0]["selectedPositive"],
                   report["cases"][0]["wholeCompile"], report["cases"][0]["selectedMutant"]]
        self.assertNotIn("--verify-module", records[0]["command"])
        self.assertNotIn("--verify-module", records[2]["command"])
        self.assertIn("--no-verify", records[2]["command"])
        self.assertEqual(records[1]["command"][-2:], records[3]["command"][-2:])
        S.validate_calibration(self.reports / "scoped-report.json", report["binding"], self.manifest, self.source, 1)

    def test_stale_calibration_and_tampered_scope_are_rejected(self):
        report = self.pipeline()
        path = self.reports / "scoped-report.json"
        stale = copy.deepcopy(report["binding"]); stale["threads"] = 2
        with self.assertRaisesRegex(RuntimeError, "stale"):
            S.validate_calibration(path, stale, self.manifest, self.source, 1)
        with self.assertRaisesRegex(RuntimeError, "counts"):
            S.validate_calibration(path, report["binding"], self.manifest, self.source, 2)
        report["selectedControlCount"] = 2
        path.write_text(json.dumps(report))
        with self.assertRaisesRegex(RuntimeError, "counts"):
            S.validate_calibration(path, report["binding"], self.manifest, self.source, 1)
        report["selectedControlCount"] = 1
        report["cases"][0]["wholeCompile"]["command"] += ["--verify-module", "consumer"]
        path.write_text(json.dumps(report))
        with self.assertRaisesRegex(RuntimeError, "flags"):
            S.validate_calibration(path, report["binding"], self.manifest, self.source, 1)

    def test_compiler_changing_source_stops_before_selected_mutant(self):
        calls = []
        def runner(cmd, env, prefix, timeout):
            calls.append(cmd)
            record = self.fake_runner(cmd, env, prefix, timeout)
            if "--no-verify" in cmd:
                Path(cmd[1]).write_text("compiler changed source")
            return record
        with self.assertRaisesRegex(RuntimeError, "during compilation"):
            self.pipeline(runner)
        self.assertEqual(len(calls), 3)

    def test_target_compile_and_timeout_failures_stop_pipeline_and_record_failed(self):
        for point in ("whole", "positive", "compile", "mutant"):
            with self.subTest(point=point):
                # Each attempt gets a fresh workspace (the real CLI also requires this).
                destination = self.root / ("work-" + point); destination.mkdir()
                report_dir = self.root / ("logs-" + point); report_dir.mkdir()
                original_reports = self.reports; self.reports = report_dir
                calls = []
                def runner(cmd, env, prefix, timeout):
                    kind = ("compile" if "--no-verify" in cmd else "whole" if "--verify-module" not in cmd
                            else "positive" if Path(cmd[1]).parent.name == "baseline" else "mutant")
                    calls.append(kind)
                    record = self.fake_runner(cmd, env, prefix, timeout)
                    if kind == point:
                        record["timedOut"] = True
                    return record
                with self.assertRaisesRegex(RuntimeError, "timed out"):
                    S.execute(self.manifest, self.source, destination, report_dir, Path("/fake/verus"), {}, TOOL,
                              S.binding(self.source, self.manifest, TOOL, 1, 600),
                              purpose="calibration", canonical_count=1, runner=runner)
                self.assertEqual(calls[-1], point)
                self.assertEqual(json.loads((report_dir / "scoped-report.json").read_text())["status"], "failed")
                self.reports = original_reports

    def test_scoped_evidence_cannot_pass_unchanged_v3_release_gate(self):
        spec = importlib.util.spec_from_file_location("release_record", ROOT / "scripts/record-verification.py")
        release = importlib.util.module_from_spec(spec); spec.loader.exec_module(release)
        legacy_shape = {"baseline": payload(entire=True)["verification-results"], "mutations": [{
            "name": "wrong-value", "compiles": True, "verification-results": payload(failed=True)["verification-results"]}]}
        with self.assertRaisesRegex(RuntimeError, "negative"):
            release.validate_negative_report(legacy_shape, ["wrong-value"])

    def test_duplicate_json_keys_rejected(self):
        path = self.root / "duplicate.json"; path.write_text('{"x":1,"x":2}')
        with self.assertRaisesRegex(RuntimeError, "duplicate JSON"):
            S.load_json(path)
        record = self.rejection()
        raw = json.dumps(payload(failed=True)).replace('"encountered-error": true', '"encountered-error": false, "encountered-error": true')
        path = self.reports / record["stdout"]; path.write_text(raw)
        record["stdoutSha256"] = S.digest(path)
        with self.assertRaisesRegex(RuntimeError, "duplicate JSON"):
            self.validate(record)

    def test_timeout_kills_process_group_and_keeps_output(self):
        fake = unittest.mock.MagicMock()
        fake.pid = 12345; fake.returncode = -15
        fake.communicate.side_effect = [subprocess.TimeoutExpired("verus", 1), ("partial output", "timeout log")]
        with patch.object(S, "verifier_lease", return_value=nullcontext(0.0)), patch.object(S.subprocess, "Popen", return_value=fake), patch.object(S.os, "killpg") as kill:
            record = S.run(["fake"], {}, self.reports / "timed", 1)
        self.assertTrue(record["timedOut"])
        kill.assert_called_once_with(12345, S.signal.SIGTERM)
        self.assertEqual((self.reports / record["stdout"]).read_text(), "partial output")


    def function_target(self):
        return {"kind": "module", "path": "consumer", "descendants": False, "function": FUNCTION}

    def single(self):
        self.case["targets"] = [self.function_target()]
        return self.case["targets"]

    def test_exact_function_selector_positive_negative(self):
        targets = self.single()
        S.validate_manifest(self.manifest)
        self.assertEqual(S.selectors(targets), ["--verify-only-module", "consumer", "--verify-function", "reject"])
        S.validate_positive(self.record(), self.reports, entire=False, targets=targets,
                            expected_failures=self.case["expectedFailures"])
        self.validate(self.rejection())

    def test_function_selector_rejects_wildcards_none_empty_or_multiple_modules(self):
        for function in (None, "", "*reject", "reject", "other::reject", 42):
            target = self.function_target(); target["function"] = function
            with self.subTest(function=function), self.assertRaises(RuntimeError):
                S.selectors([target])
        with self.assertRaises(RuntimeError):
            S.selectors([self.function_target(), {"kind": "root", "timingModule": "root"}])
        target = self.function_target(); target["descendants"] = True
        with self.assertRaises(RuntimeError):
            S.selectors([target])

    def test_single_scope_rejects_sibling_even_if_expected_function_passed(self):
        targets = self.single(); value = payload()
        value["times-ms"]["smt"]["smt-run-module-times"][0]["function-breakdown"].append(
            {"function": "cordis_negative::consumer::sibling", "success": True, "time-micros": 10, "rlimit": 100})
        with self.assertRaisesRegex(RuntimeError, "outside"):
            S.validate_positive(self.record(value), self.reports, entire=False, targets=targets)
        value["times-ms"]["smt"]["smt-run-module-times"][0]["function-breakdown"][0]["success"] = False
        value["verification-results"].update(payload(failed=True)["verification-results"])
        with self.assertRaisesRegex(RuntimeError, "outside"):
            self.validate(self.rejection(value=value))

    def test_single_scope_rejects_wrong_timing_module(self):
        self.single(); value = payload(failed=True)
        value["times-ms"]["smt"]["smt-run-module-times"][0]["module"] = "other"
        with self.assertRaisesRegex(RuntimeError, "different module"):
            self.validate(self.rejection(value=value))

    def test_root_method_single_selector(self):
        function = "cordis_negative::Kernel::retire"
        targets = [{"kind": "root", "timingModule": "", "function": function}]
        self.assertEqual(S.selectors(targets), ["--verify-root", "--verify-function", "Kernel::retire"])
        value = payload(); value["times-ms"]["smt"]["smt-run-module-times"][0] = {
            "module": "", "function-breakdown": [{"function": function, "success": True, "time-micros": 10, "rlimit": 100}]}
        S.validate_positive(self.record(value), self.reports, entire=False, targets=targets,
                            expected_failures=[{"module": "", "function": function}])

    def test_one_failed_function_can_have_multiple_contract_diagnostics(self):
        self.single()
        (self.source / "consumer.rs").write_text("pub proof fn reject()\nensures safe,\nensures sound,\n{}\n")
        second = copy.deepcopy(self.case["expectedFailures"][0]); second["uniqueSourceAnchor"] = "ensures sound,"
        self.case["expectedFailures"].append(second)
        S.validate_manifest(self.manifest)
        stderr = (f"error: postcondition not satisfied\n --> {self.source}/consumer.rs:2:1\n"
                  f"error: postcondition not satisfied\n --> {self.source}/consumer.rs:3:1\n"
                  "error: aborting due to 2 previous errors\n")
        # Verus reports one failed function, despite the two stderr diagnostics.
        stats = self.validate(self.rejection(stderr=stderr))
        self.assertEqual(stats["errors"], 1)
        bad = payload(failed=True); bad["verification-results"]["errors"] = 2
        with self.assertRaisesRegex(RuntimeError, "failed-function count"):
            self.validate(self.rejection(value=bad, stderr=stderr))

    def test_loop_invariant_variants_normalize_only_known_contracts(self):
        self.case["expectedFailures"][0]["diagnosticKind"] = "invariant not satisfied"
        for variant in ("invariant not satisfied", *S.CONTRACT_VARIANTS):
            stderr = f"error: {variant}\n --> {self.source}/consumer.rs:2:1\n"
            self.validate(self.rejection(stderr=stderr))
        with self.assertRaises(RuntimeError):
            self.validate(self.rejection(stderr=f"error: invariant not satisfied for an unknown reason\n --> {self.source}/consumer.rs:2:1\n"))

    def test_crash_exit_codes_with_apparently_valid_contracts_fail(self):
        for code in (2, 101, 134, 137):
            record = self.rejection(); record["returncode"] = code
            with self.subTest(code=code), self.assertRaises(RuntimeError):
                self.validate(record)

    def test_anchor_trailing_newline_does_not_cover_next_line(self):
        self.case["expectedFailures"][0]["uniqueSourceAnchor"] = "ensures safe,\n"
        with self.assertRaisesRegex(RuntimeError, "reviewed anchor"):
            self.validate(self.rejection(stderr=f"error: postcondition not satisfied\n --> {self.source}/consumer.rs:3:1\n"))

    def test_anchor_primary_column_must_be_inside(self):
        (self.source / "consumer.rs").write_text("fn reject()\nensures safe, OTHER\n{}\n")
        with self.assertRaisesRegex(RuntimeError, "reviewed anchor"):
            self.validate(self.rejection(stderr=f"error: postcondition not satisfied\n --> {self.source}/consumer.rs:2:15\n"))

    def test_canonical_exact_order_coverage_and_mutation(self):
        project = self.root / "project"; (project / "scripts").mkdir(parents=True)
        second = copy.deepcopy(self.case); second["name"] = "other-value"
        second["mutation"]["old"] = "second original"
        cases = [self.case, second]
        mutations = [(c["name"], c["mutation"]["file"], c["mutation"]["old"], c["mutation"]["new"]) for c in cases]
        (project / "scripts/check-negative.py").write_text("def mutation_manifest():\n    return " + repr(mutations) + "\n")
        complete = copy.deepcopy(self.manifest); complete["cases"] = copy.deepcopy(cases)
        self.assertEqual(S.validate_canonical_cases(complete, project), 2)
        variants = [cases[:1], cases[::-1], cases + [second], [self.case, self.case]]
        changed = copy.deepcopy(cases); changed[0]["mutation"]["new"] = "another change"; variants.append(changed)
        for candidate in variants:
            altered = copy.deepcopy(complete); altered["cases"] = candidate
            with self.subTest(candidate=candidate), self.assertRaisesRegex(RuntimeError, "exact order"):
                S.validate_canonical_cases(altered, project)

    def test_calibration_rejects_replaced_binary_or_other_baseline(self):
        report = self.pipeline(); original = copy.deepcopy(report); path = self.reports / "scoped-report.json"
        report["cases"][0]["selectedPositive"]["command"][0] = "/unbound/verus"
        path.write_text(json.dumps(report))
        with self.assertRaisesRegex(RuntimeError, "paths"):
            S.validate_calibration(path, report["binding"], self.manifest, self.source, 1)
        report = original
        report["cases"][0]["selectedPositive"]["command"][1] = "/another/baseline/lib.rs"
        path.write_text(json.dumps(report))
        with self.assertRaisesRegex(RuntimeError, "different baseline"):
            S.validate_calibration(path, report["binding"], self.manifest, self.source, 1)

    def test_pipeline_rejects_subset_count(self):
        with self.assertRaisesRegex(RuntimeError, "all canonical"):
            S.execute(self.manifest, self.source, self.root, self.reports, Path("/fake/verus"), {}, TOOL,
                      {}, purpose="calibration", canonical_count=112, runner=self.fake_runner)

    def test_function_scope_pipeline_commands_are_identical(self):
        self.single(); report = self.pipeline(); case = report["cases"][0]
        self.assertEqual(case["selectedPositive"]["command"][-4:], case["selectedMutant"]["command"][-4:])
        self.assertNotIn("--verify-function", case["wholeCompile"]["command"])
        S.validate_calibration(self.reports / "scoped-report.json", report["binding"], self.manifest, self.source, 1)


    def test_tool_artifact_same_path_replacement_is_rejected(self):
        self.tool_check.stop()
        binary = self.root / "verus"; binary.write_bytes(b"original verifier")
        tool = {"binary": str(binary), "files": {"verus": S.digest(binary)},
                "artifactPaths": {"verus": str(binary)}}
        S.verify_tool_artifacts(tool)
        binary.write_bytes(b"replacement verifier")
        with self.assertRaisesRegex(RuntimeError, "tool artifact changed"):
            S.verify_tool_artifacts(tool)

    def test_baseline_drift_during_mutant_compile_is_rejected(self):
        def runner(cmd, env, prefix, timeout):
            record = self.fake_runner(cmd, env, prefix, timeout)
            if "--no-verify" in cmd:
                (self.source / "lib.rs").write_text("unrelated drift")
            return record
        with self.assertRaisesRegex(RuntimeError, "baseline changed"):
            self.pipeline(runner)


    def test_zero_work_placeholders_are_not_proof_evidence(self):
        targets = self.single(); value = payload()
        functions = value["times-ms"]["smt"]["smt-run-module-times"][0]["function-breakdown"]
        functions.append({"function": "cordis_negative::consumer::sibling", "success": True,
                          "time-micros": 0, "rlimit": 0})
        S.validate_positive(self.record(value), self.reports, entire=False, targets=targets,
                            expected_failures=self.case["expectedFailures"])
        self.assertNotIn("cordis_negative::consumer::sibling", S.timed_functions(value))
        functions[0].update({"time-micros": 0, "rlimit": 0})
        with self.assertRaisesRegex(RuntimeError, "no timed proof"):
            S.validate_positive(self.record(value), self.reports, entire=False, targets=targets,
                                expected_failures=self.case["expectedFailures"])

    def test_missing_or_boolean_work_attribution_rejected(self):
        for change in ({"rlimit": True}, {"time-micros": -1}):
            value = payload(); value["times-ms"]["smt"]["smt-run-module-times"][0]["function-breakdown"][0].update(change)
            with self.assertRaisesRegex(RuntimeError, "work attribution"):
                S.validate_positive(self.record(value), self.reports, entire=False)
        value = payload(); del value["times-ms"]["smt"]["smt-run-module-times"][0]["function-breakdown"][0]["rlimit"]
        with self.assertRaisesRegex(RuntimeError, "attribution"):
            S.validate_positive(self.record(value), self.reports, entire=False)


    def test_interrupt_reaps_group_before_lease_release_and_cannot_pass(self):
        fake = unittest.mock.MagicMock(); fake.pid = 12345; fake.returncode = 0
        fake.communicate.side_effect = [KeyboardInterrupt(), (json.dumps(payload()), "")]
        with patch.object(S, "verifier_lease", return_value=nullcontext(0.0)), \
             patch.object(S.subprocess, "Popen", return_value=fake), patch.object(S.os, "killpg") as kill:
            record = S.run(["fake"], {}, self.reports / "interrupted", 1)
        kill.assert_called_once_with(12345, S.signal.SIGTERM)
        self.assertTrue(record["interrupted"])
        with self.assertRaisesRegex(RuntimeError, "interrupted"):
            S.validate_positive(record, self.reports, entire=False)

    def test_timeout_escalates_term_to_kill_and_reaps(self):
        fake = unittest.mock.MagicMock(); fake.pid = 12345; fake.returncode = -9
        fake.communicate.side_effect = [subprocess.TimeoutExpired("verus", 1),
                                       subprocess.TimeoutExpired("verus", 2), ("partial", "logs")]
        with patch.object(S, "verifier_lease", return_value=nullcontext(0.0)), \
             patch.object(S.subprocess, "Popen", return_value=fake), patch.object(S.os, "killpg") as kill:
            record = S.run(["fake"], {}, self.reports / "killed", 1)
        self.assertTrue(record["timedOut"])
        self.assertEqual(kill.call_args_list, [unittest.mock.call(12345, S.signal.SIGTERM),
                                             unittest.mock.call(12345, S.signal.SIGKILL)])
        self.assertEqual(fake.communicate.call_count, 3)



if __name__ == "__main__":
    unittest.main()
