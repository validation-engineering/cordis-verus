"""Development evidence regressions; no compiler or verifier processes are run."""
from contextlib import contextmanager
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import MagicMock, call, patch

SCRIPT = Path(__file__).parents[1] / "record-development.py"
PROJECT = SCRIPT.parent.parent
spec = importlib.util.spec_from_file_location("development_record", SCRIPT)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class DevelopmentEvidenceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="cordis-development-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for name in module.FIXED_SCRIPTS:
            destination = self.root / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(PROJECT / name, destination)
        (self.root / "crates/cordis/examples").mkdir(parents=True)
        (self.root / "crates/cordis/examples/demo.rs").write_text("fn main() {}\n")
        self.record = self.root / "docs/development-report.json"
        self.record.parent.mkdir()
        self.record.write_text(json.dumps({"schema": module.SCHEMA, "status": "passed", "sha256": {"stale": "old"}}))
        self.packages = self.root / "target/release-artifacts/package-report.json"
        self.packages.parent.mkdir(parents=True)
        self.events = []
        self.addCleanup(patch.stopall)
        patch.object(module, "ROOT", self.root).start()
        patch.object(module, "RECORD", self.record).start()
        patch.object(module, "verifier_lease", self.lease).start()
        patch.dict(os.environ, {}, clear=True).start()

    @contextmanager
    def lease(self):
        self.events.append("lock")
        try:
            yield
        finally:
            self.events.append("unlock")

    def log(self):
        return "\n".join([
            "verification results:: 2227 verified, 0 errors",
            module.WORKSPACE_BEGIN,
            "Running tests/lifecycle.rs (target/lifecycle)",
            "test result: ok. 4 passed; 0 failed;",
            "Doc-tests cordis", "test result: ok. 2 passed; 0 failed;",
            module.WORKSPACE_END,
            "Running tests/lifecycle.rs (extracted/lifecycle)",
            "test result: ok. 99 passed; 0 failed;",
            module.MARKER,
        ])

    def successful_checks(self, command, environment, log):
        self.assertFalse(self.packages.exists(), "a stale package report survived preflight")
        self.assertEqual(command, ["./scripts/check-development.sh", "--offline"])
        self.assertEqual(environment["CORDIS_VERUS_THREADS"], "2")
        self.assertEqual(environment["CARGO_NET_OFFLINE"], "true")
        self.assertEqual(json.loads(self.record.read_text())["status"], "running")
        log.write_text(self.log())
        self.packages.write_text(json.dumps({"registry_publish_checked": False, "packages": ["fresh"]}))
        return 0

    def read_record(self):
        return json.loads(self.record.read_text())

    def assert_failed(self):
        record = self.read_record()
        self.assertEqual(record["status"], "failed")
        self.assertEqual(record["sha256"], {})
        self.assertFalse(record["releaseAcceptance"])
        self.assertFalse(record["paperCompletion"])
        for name in ("proof", "tests", "packages", "checkedAt", "workflowSha256"):
            self.assertNotIn(name, record)

    def test_counts_workspace_without_repeated_package_suites(self):
        proof, tests = module.parse_results(self.log())
        self.assertEqual(proof["verified"], 2227)
        self.assertEqual(tests["total"], 4)
        self.assertEqual(tests["doctestTotal"], 2)
        self.assertNotIn("deterministicTraces", tests)

    def test_rejects_failed_missing_ambiguous_or_incomplete_checks(self):
        variants = [self.log().replace("0 errors", "1 errors"),
                    self.log().replace("2227 verified", "0 verified"),
                    self.log().replace(module.MARKER, ""),
                    self.log().replace(module.WORKSPACE_BEGIN, ""),
                    self.log() + "\nverification results:: 1 verified, 0 errors",
                    self.log() + "\n" + module.MARKER,
                    self.log().replace(module.WORKSPACE_END, module.WORKSPACE_END + "\n" + module.WORKSPACE_END),
                    self.log().replace("4 passed; 0 failed;", "4 passed; 1 failed;"),
                    self.log().replace("test result: ok. 4 passed", "test result: FAILED. 4 passed"),
                    self.log().replace(module.WORKSPACE_BEGIN, "temporary").replace(module.WORKSPACE_END, module.WORKSPACE_BEGIN).replace("temporary", module.WORKSPACE_END)]
        for log in variants:
            with self.subTest(log=log), self.assertRaises(RuntimeError):
                module.parse_results(log)

    def test_evidence_is_excluded_but_all_workflow_scripts_are_bound(self):
        before = module.source_hashes()
        self.record.write_text('{"status":"running"}\n')
        self.assertEqual(before, module.source_hashes())
        self.assertNotIn("docs/development-report.json", before)
        self.assertEqual(module.workflow_binding(before), {name: before[name] for name in module.FIXED_SCRIPTS})
        changed = dict(before); changed.pop("scripts/verify.sh")
        with self.assertRaisesRegex(RuntimeError, "Missing fixed"):
            module.workflow_binding(changed)
        changed = dict(before); changed["scripts/record-development.py"] = "changed"
        with self.assertRaisesRegex(RuntimeError, "recorder changed"):
            module.workflow_binding(changed)

    def test_fresh_success_is_development_only_and_hash_check_runs_no_process(self):
        self.packages.write_text('{"old":true}')
        with patch.object(module, "run_checks", side_effect=self.successful_checks) as runner:
            result = module.record_development(offline=True)
            self.assertEqual(runner.call_count, 1)
        self.assertEqual(result["status"], "passed")
        self.assertFalse(result["releaseAcceptance"])
        self.assertEqual(result["fullNegativeControls"], "not run by this command")
        self.assertFalse(result["paperCompletion"])
        self.assertEqual(result["tests"]["total"], 4)
        self.assertEqual(result["packages"]["packages"], ["fresh"])
        self.assertEqual(self.events, ["lock", "unlock"])
        with patch.object(module.subprocess, "Popen", side_effect=AssertionError("hash check must not run checks")):
            module.check_record()

    def test_hash_check_rejects_promoted_release_or_changed_workflow(self):
        with patch.object(module, "run_checks", side_effect=self.successful_checks):
            module.record_development(offline=True)
        original = self.read_record()
        for name, value in (("releaseAcceptance", True), ("paperCompletion", True),
                            ("fullNegativeControls", "passed"), ("command", ["./scripts/quality.sh"]),
                            ("workflowSha256", {})):
            changed = dict(original); changed[name] = value
            self.record.write_text(json.dumps(changed))
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, "stale development"):
                module.check_record()

    def test_source_hashing_failure_invalidates_old_success(self):
        with patch.object(module, "source_hashes", side_effect=OSError("unreadable source")), \
             patch.object(module, "run_checks") as runner, self.assertRaises(OSError):
            module.record_development()
        runner.assert_not_called()
        self.assert_failed()

    def test_unsupported_environment_invalidates_old_success(self):
        with patch.dict(os.environ, {"VERUS_EXTRA_ARGS": "--verify-only-module one"}), \
             patch.object(module, "run_checks") as runner, self.assertRaisesRegex(RuntimeError, "Custom compiler"):
            module.record_development()
        runner.assert_not_called()
        self.assert_failed()

    def test_source_change_during_checks_rejects_success(self):
        def changed(command, environment, log):
            result = self.successful_checks(command, environment, log)
            (self.root / "scripts/verify.sh").write_text("changed workflow")
            return result
        with patch.object(module, "run_checks", side_effect=changed), self.assertRaisesRegex(RuntimeError, "Sources changed"):
            module.record_development(offline=True)
        self.assert_failed()

    def test_previous_package_report_cannot_be_reused(self):
        self.packages.write_text('{"old":true}')
        def missing(_command, _environment, log):
            log.write_text(self.log())
            return 0
        with patch.object(module, "run_checks", side_effect=missing), self.assertRaises(FileNotFoundError):
            module.record_development()
        self.assert_failed()

    def test_nonzero_process_cannot_pass_even_with_complete_log(self):
        def rejected(command, environment, log):
            self.successful_checks(command, environment, log)
            return 1
        with patch.object(module, "run_checks", side_effect=rejected), self.assertRaisesRegex(RuntimeError, "exited 1"):
            module.record_development(offline=True)
        self.assert_failed()

    def test_interrupt_while_waiting_for_lease_records_failure(self):
        @contextmanager
        def interrupted():
            raise KeyboardInterrupt()
            yield
        with patch.object(module, "verifier_lease", interrupted), patch.object(module, "run_checks") as runner, \
             self.assertRaises(KeyboardInterrupt):
            module.record_development()
        runner.assert_not_called()
        self.assert_failed()

    def test_interrupt_after_success_save_removes_passed_fields(self):
        save = module.save_record
        def interrupt(record):
            save(record)
            if record["status"] == "passed":
                raise KeyboardInterrupt()
        with patch.object(module, "save_record", side_effect=interrupt), \
             patch.object(module, "run_checks", side_effect=self.successful_checks), self.assertRaises(KeyboardInterrupt):
            module.record_development(offline=True)
        self.assert_failed()

    def interrupted_process(self, failures):
        process = MagicMock(); process.pid = 12345
        values = iter(failures)
        def wait(*_args, **_kwargs):
            value = next(values)
            if isinstance(value, BaseException):
                self.events.append(type(value).__name__)
                raise value
            self.events.append("reaped")
            return value
        process.wait.side_effect = wait
        def kill(_pid, sig):
            self.assertNotIn("unlock", self.events)
            self.events.append("TERM" if sig == module.signal.SIGTERM else "KILL")
        return process, kill

    def test_interrupt_kills_group_and_reaps_before_lease_release(self):
        process, kill = self.interrupted_process([KeyboardInterrupt(), 0, -9])
        with patch.object(module.subprocess, "Popen", return_value=process) as popen, \
             patch.object(module.os, "killpg", side_effect=kill) as signals, self.assertRaises(KeyboardInterrupt):
            module.record_development()
        self.assertTrue(popen.call_args.kwargs["start_new_session"])
        self.assertEqual(signals.call_args_list, [call(12345, module.signal.SIGTERM), call(12345, module.signal.SIGKILL)])
        # KILL is still sent if the shell exits after TERM: descendants may remain.
        self.assertEqual(self.events, ["lock", "KeyboardInterrupt", "TERM", "reaped", "KILL", "reaped", "unlock"])
        self.assert_failed()

    def test_timeout_escalates_and_reaps_before_releasing_lease(self):
        process, kill = self.interrupted_process([subprocess.TimeoutExpired("checks", 1),
                                                 subprocess.TimeoutExpired("checks", 2), -9])
        with patch.object(module.subprocess, "Popen", return_value=process), \
             patch.object(module.os, "killpg", side_effect=kill), self.assertRaises(subprocess.TimeoutExpired):
            module.record_development()
        self.assertEqual(self.events, ["lock", "TimeoutExpired", "TERM", "TimeoutExpired", "KILL", "reaped", "unlock"])
        self.assert_failed()

    def test_repeated_interrupts_cannot_release_a_live_group(self):
        process, kill = self.interrupted_process([KeyboardInterrupt(), KeyboardInterrupt(), KeyboardInterrupt(), -9])
        with patch.object(module.subprocess, "Popen", return_value=process), \
             patch.object(module.os, "killpg", side_effect=kill), self.assertRaises(KeyboardInterrupt):
            module.record_development()
        self.assertEqual(self.events, ["lock", "KeyboardInterrupt", "TERM", "KeyboardInterrupt", "KILL",
                                      "KeyboardInterrupt", "KILL", "reaped", "unlock"])
        self.assert_failed()

    def test_process_creation_failure_records_failure(self):
        with patch.object(module.subprocess, "Popen", side_effect=OSError("cannot spawn")), self.assertRaises(OSError):
            module.record_development()
        self.assertEqual(self.events, ["lock", "unlock"])
        self.assert_failed()

    def test_term_signal_uses_cleanup_and_restores_handlers(self):
        previous = {sig: module.signal.getsignal(sig) for sig in (module.signal.SIGINT, module.signal.SIGTERM, module.signal.SIGHUP)}
        process = MagicMock(); process.pid = 12345
        calls = 0
        def wait(*_args, **_kwargs):
            nonlocal calls
            calls += 1
            if calls == 1:
                module.signal.getsignal(module.signal.SIGTERM)(module.signal.SIGTERM, None)
            self.events.append("reaped")
            return -9
        process.wait.side_effect = wait
        with patch.object(module.subprocess, "Popen", return_value=process), \
             patch.object(module.os, "killpg") as kill, self.assertRaises(module.TerminationRequested):
            module.record_development()
        self.assertEqual(kill.call_args_list, [call(12345, module.signal.SIGTERM), call(12345, module.signal.SIGKILL)])
        self.assertEqual(self.events, ["lock", "reaped", "reaped", "unlock"])
        self.assertEqual({sig: module.signal.getsignal(sig) for sig in previous}, previous)
        self.assert_failed()

    def test_signal_during_spawn_is_deferred_until_child_pid_can_be_reaped(self):
        process = MagicMock(); process.pid = 12345; process.wait.return_value = -9
        def spawn(*_args, **_kwargs):
            module.signal.getsignal(module.signal.SIGTERM)(module.signal.SIGTERM, None)
            self.events.append("spawn returned")
            return process
        with patch.object(module.subprocess, "Popen", side_effect=spawn), \
             patch.object(module.os, "killpg") as kill, self.assertRaisesRegex(module.TerminationRequested, "while spawning"):
            module.record_development()
        self.assertEqual(kill.call_args_list, [call(12345, module.signal.SIGTERM), call(12345, module.signal.SIGKILL)])
        self.assertEqual(process.wait.call_count, 2)
        self.assertEqual(self.events, ["lock", "spawn returned", "unlock"])
        self.assert_failed()

    def test_interrupted_initial_invalidation_cannot_leave_old_passed(self):
        original = module.save_record
        calls = 0
        def save(record):
            nonlocal calls
            calls += 1
            if calls == 1:
                raise KeyboardInterrupt()
            original(record)
        with patch.object(module, "save_record", side_effect=save), \
             patch.object(module, "run_checks") as runner, self.assertRaises(KeyboardInterrupt):
            module.record_development()
        runner.assert_not_called()
        self.assert_failed()

    def test_atomic_save_leaves_no_temporary_report(self):
        module.save_record({"schema": module.SCHEMA, "status": "running"})
        self.assertEqual(self.read_record()["status"], "running")
        self.assertEqual(list(self.record.parent.glob(".development-report-*.tmp")), [])


if __name__ == "__main__":
    unittest.main()
