"""Regression tests for the proof evidence gate, independent of Verus itself."""
import contextlib
import importlib.util
import io
import json
import os
import signal
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest.mock import Mock, patch

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
        executable = self.root / "fake-verus"
        executable.write_text(f"#!{sys.executable}\nimport time, sys\n"
                              "print('{\"unfinished\":', flush=True)\n"
                              "print('partial diagnostic', file=sys.stderr, flush=True)\n"
                              "time.sleep(30)\n")
        executable.chmod(0o755)
        killpg = os.killpg
        def signal_group(pid, number):
            # macOS can reject signal-0 probes during group teardown even when
            # real termination signals succeed. Cleanup must not depend on it.
            if number == 0:
                raise PermissionError("group disappeared during permission check")
            return killpg(pid, number)
        with patch.object(CHECKS.os, "killpg", side_effect=signal_group), self.assertRaises(subprocess.TimeoutExpired):
            CHECKS.run_verus(executable, os.environ.copy(), self.baseline / "lib.rs", prefix, timeout=1)
        self.assertEqual(prefix.with_suffix(".stdout.json").read_text(), '{"unfinished":\n')
        self.assertEqual(prefix.with_suffix(".stderr.txt").read_text(), 'partial diagnostic\n')
        meta = json.loads(prefix.with_suffix(".meta.json").read_text())
        self.assertEqual(meta["status"], "timed_out")
        self.assertGreaterEqual(meta["durationSeconds"], 1)
        self.assertNotEqual(meta["returncode"], 0)
        self.assertFalse((self.reports / "report.json").exists())

    def test_cancellation_after_compile_does_not_start_verification(self):
        supervisor = CHECKS.ProcessSupervisor()
        calls = []

        def runner(*args, **kwargs):
            calls.append(args)
            supervisor.cancel()
            return result(code=0)

        with self.assertRaises(CHECKS.RunCancelled):
            CHECKS.check_mutation(self.mutation, self.baseline, self.root, self.reports,
                                  "unused-verus", {}, runner=runner, supervisor=supervisor)
        self.assertEqual(len(calls), 1)

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



class CpuBudgetTests(unittest.TestCase):
    def test_default_budget_is_conservative_and_workers_cannot_oversubscribe(self):
        for cpus, jobs, expected_jobs, expected_threads in [(16, 1, 1, 2), (16, 2, 2, 1), (1, 9, 1, 1)]:
            with self.subTest(cpus=cpus, jobs=jobs), patch.object(CHECKS, "available_cpus", return_value=cpus):
                budget = CHECKS.execution_budget(jobs)
                self.assertEqual(budget["jobs"], expected_jobs)
                self.assertEqual(budget["threadsPerWorker"], expected_threads)
                self.assertEqual(budget["baselineThreads"], expected_threads)
                self.assertLessEqual(budget["jobs"] * budget["threadsPerWorker"], budget["cpuBudget"])

    def test_explicit_budget_and_threads_are_bounded_by_available_cpus(self):
        with patch.object(CHECKS, "available_cpus", return_value=6):
            budget = CHECKS.execution_budget(jobs=8, threads=2, cpu_budget=100)
            self.assertEqual((budget["jobs"], budget["cpuBudget"]), (3, 6))
            with self.assertRaisesRegex(ValueError, "exceed"):
                CHECKS.execution_budget(threads=7, cpu_budget=100)
            for options in ({"jobs": 0}, {"threads": 0}, {"cpu_budget": 0}):
                with self.subTest(options=options), self.assertRaises(ValueError):
                    CHECKS.execution_budget(**options)

    def test_main_passes_the_same_explicit_thread_budget_to_baseline_and_mutations(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "crates/cordis-kernel/src"
            source.mkdir(parents=True)
            (source / "lib.rs").write_text("pub const TAG: u8 = 0;")
            baseline = result(code=0, success=True, errors=0)
            payload = json.loads(baseline.stdout)
            payload["verus"] = {"version": "test"}
            baseline.stdout = json.dumps(payload)
            with patch.object(CHECKS, "ROOT", root), patch.object(CHECKS, "toolchain", return_value=("verus", {})), \
                    patch.object(CHECKS, "available_cpus", return_value=8), \
                    patch.object(CHECKS, "run_verus", return_value=baseline) as baseline_runner, \
                    patch.object(CHECKS, "check_mutations", return_value=[]) as mutations, \
                    patch.object(sys, "argv", ["check-negative.py", "--jobs", "2", "--cpu-budget", "2"]), \
                    patch.dict(os.environ, {}, clear=True), contextlib.redirect_stdout(io.StringIO()):
                CHECKS.main()
            self.assertEqual(baseline_runner.call_args.kwargs["threads"], 1)
            self.assertEqual(mutations.call_args.kwargs["threads"], 1)
            self.assertEqual(mutations.call_args.kwargs["jobs"], 2)


@unittest.skipUnless(os.name == "posix", "release runners use POSIX process groups")
class ProcessLifecycleTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="cordis-process-test-")
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        self.source.mkdir()
        (self.source / "lib.rs").write_text("pub const TAG: u8 = 0;\n")
        self.reports = self.root / "reports"
        self.reports.mkdir()

    def tearDown(self):
        self.temporary.cleanup()

    def executable(self, body):
        path = self.root / "fake-verus"
        path.write_text(f"#!{sys.executable}\n" + body)
        path.chmod(0o755)
        return path

    def wait_file(self, path):
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            if path.exists() and path.stat().st_size:
                return path.read_text()
            time.sleep(0.01)
        self.fail(f"Process did not become ready: {path}")

    def assert_reaped(self, pid):
        with self.assertRaises(ChildProcessError):
            os.waitpid(pid, os.WNOHANG)
        with self.assertRaises(ProcessLookupError):
            os.kill(pid, 0)

    def tree_executable(self):
        return self.executable("""import os, signal, sys, time
from pathlib import Path
child = os.fork()
if child == 0:
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    while True:
        time.sleep(10)
def cleanup(_number, _frame):
    os.kill(child, signal.SIGKILL)
    os.waitpid(child, 0)
    sys.exit(143)
signal.signal(signal.SIGTERM, cleanup)
Path(os.environ['READY']).write_text(f'{os.getpid()} {child}')
print('partial stdout', flush=True)
print('partial stderr', file=sys.stderr, flush=True)
while True:
    time.sleep(10)
""")

    def test_timeout_terminates_and_reaps_verus_and_solver_children(self):
        ready = self.root / "ready"
        prefix = self.reports / "timeout"
        with self.assertRaises(subprocess.TimeoutExpired):
            CHECKS.run_verus(self.tree_executable(), {**os.environ, "READY": str(ready)},
                             self.source / "lib.rs", prefix, timeout=1)
        leader, child = map(int, self.wait_file(ready).split())
        self.assert_reaped(leader)
        self.assert_reaped(child)
        self.assertEqual(prefix.with_suffix(".stdout.json").read_text(), "partial stdout\n")
        self.assertEqual(prefix.with_suffix(".stderr.txt").read_text(), "partial stderr\n")
        meta = json.loads(prefix.with_suffix(".meta.json").read_text())
        self.assertEqual(meta["schema"], "cordis.negative-stage/v1")
        self.assertEqual(meta["status"], "timed_out")
        self.assertEqual(meta["sourceSha256"], CHECKS.source_fingerprint(self.source))
        self.assertIn("--no-cheating", meta["command"])

    def test_explicit_cancellation_stops_active_group_before_returning(self):
        ready = self.root / "ready"
        prefix = self.reports / "cancelled"
        supervisor = CHECKS.ProcessSupervisor()
        errors = []

        def work():
            try:
                CHECKS.run_verus(self.tree_executable(), {**os.environ, "READY": str(ready)},
                                 self.source / "lib.rs", prefix, timeout=30, supervisor=supervisor)
            except CHECKS.RunCancelled as error:
                errors.append(error)

        worker = threading.Thread(target=work)
        worker.start()
        leader, child = map(int, self.wait_file(ready).split())
        supervisor.cancel(RuntimeError("peer mutation failed"))
        worker.join(timeout=5)
        self.assertFalse(worker.is_alive())
        self.assertEqual(len(errors), 1)
        self.assertFalse(supervisor.processes)
        self.assert_reaped(leader)
        self.assert_reaped(child)
        meta = json.loads(prefix.with_suffix(".meta.json").read_text())
        self.assertEqual(meta["status"], "cancelled")
        self.assertEqual(meta["cancellationReason"], "peer mutation failed")

    def test_failure_cancels_active_peer_and_does_not_start_queued_mutations(self):
        ready = self.root / "peer-ready"
        binary = self.executable("""import os, signal, sys, time
from pathlib import Path
name = Path(sys.argv[1]).parent.name
ready = Path(os.environ['READY'])
if name == 'failure':
    deadline = time.monotonic() + 5
    while not ready.exists() and time.monotonic() < deadline:
        time.sleep(0.01)
    print('compile failure', file=sys.stderr, flush=True)
    sys.exit(1)
if name != 'peer':
    raise AssertionError('A queued mutation must never start')
child = os.fork()
if child == 0:
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    while True:
        time.sleep(10)
def cleanup(_number, _frame):
    os.kill(child, signal.SIGKILL)
    os.waitpid(child, 0)
    sys.exit(143)
signal.signal(signal.SIGTERM, cleanup)
ready.write_text(f'{os.getpid()} {child}')
while True:
    time.sleep(10)
""")
        mutations = [(name, "lib.rs", "= 0", "= 1") for name in ["failure", "peer", "queued"]]
        supervisor = CHECKS.ProcessSupervisor()
        started = time.monotonic()
        with self.assertRaisesRegex(RuntimeError, "failure did not compile"):
            CHECKS.check_mutations(mutations, self.source, self.root, self.reports, binary,
                                   {**os.environ, "READY": str(ready)}, jobs=2, threads=1,
                                   timeout=30, supervisor=supervisor)
        self.assertLess(time.monotonic() - started, 5)
        self.assertFalse((self.root / "queued").exists())
        self.assertFalse(supervisor.processes)
        leader, child = map(int, self.wait_file(ready).split())
        self.assert_reaped(leader)
        self.assert_reaped(child)
        meta = json.loads((self.reports / "peer-compile.meta.json").read_text())
        self.assertEqual(meta["status"], "cancelled")

    def test_sigterm_cleans_active_group_and_restores_previous_handler(self):
        ready = self.root / "ready"
        binary = self.tree_executable()
        prefix = self.reports / "signal"
        wrapper = self.root / "wrapper.py"
        wrapper.write_text(f"""import importlib.util, os, signal
from pathlib import Path
spec = importlib.util.spec_from_file_location('checks', {str(SCRIPT)!r})
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
supervisor = checks.ProcessSupervisor()
previous = signal.getsignal(signal.SIGTERM)
try:
    with supervisor.signal_handlers():
        checks.run_verus({str(binary)!r}, os.environ.copy(), Path({str(self.source / 'lib.rs')!r}),
                         Path({str(prefix)!r}), supervisor=supervisor, timeout=30)
except checks.RunCancelled:
    assert signal.getsignal(signal.SIGTERM) == previous
    assert not supervisor.processes
    raise SystemExit(7)
raise AssertionError('signal must cancel verification')
""")
        process = subprocess.Popen([sys.executable, str(wrapper)], env={**os.environ, "READY": str(ready)},
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            leader, child = map(int, self.wait_file(ready).split())
            process.send_signal(signal.SIGTERM)
            stdout, stderr = process.communicate(timeout=5)
            self.assertEqual(process.returncode, 7, stdout + stderr)
            self.assert_reaped(leader)
            self.assert_reaped(child)
            meta = json.loads(prefix.with_suffix(".meta.json").read_text())
            self.assertEqual(meta["status"], "cancelled")
            self.assertEqual(meta["signal"], signal.SIGTERM)
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()

    def test_reentrant_cancellation_marks_term_before_sending_and_never_repeats_it(self):
        supervisor = CHECKS.ProcessSupervisor(terminate_grace=0)
        process = Mock(pid=12345)
        supervisor.processes.add(process)
        sent = []

        def deliver(pid, number):
            sent.append((pid, number))
            if number == signal.SIGTERM:
                # Emulate another signal handler before the original syscall
                # returns. Marking after killpg would recurse or resend TERM.
                supervisor.cancel()

        with patch.object(CHECKS.os, "killpg", side_effect=deliver):
            supervisor.cancel()
            supervisor.cancel()
            supervisor.finish(process, terminate=True)
        self.assertEqual(sent, [(process.pid, signal.SIGTERM), (process.pid, signal.SIGKILL)])
        process.wait.assert_called_once()
        self.assertFalse(supervisor.processes)
        self.assertFalse(supervisor.term_sent)

    def test_cancellation_during_final_cleanup_cannot_return_completed_evidence(self):
        class CancelAfterCleanup(CHECKS.ProcessSupervisor):
            def finish(self, process, *, terminate=False):
                super().finish(process, terminate=terminate)
                self.cancel()

        prefix = self.reports / "cancel-at-finish"
        with self.assertRaises(CHECKS.RunCancelled):
            CHECKS.run_verus(self.executable("print('done')\n"), os.environ.copy(), self.source / "lib.rs",
                             prefix, supervisor=CancelAfterCleanup())
        metadata = json.loads(prefix.with_suffix(".meta.json").read_text())
        self.assertEqual(metadata["status"], "cancelled", json.dumps(metadata, indent=2))
        self.assert_reaped(metadata["pid"])

    def test_actual_cleanup_failure_is_preserved_and_never_relabelled_as_cancellation(self):
        class FailedCleanup(CHECKS.ProcessSupervisor):
            def finish(self, process, *, terminate=False):
                super().finish(process, terminate=terminate)
                self.cancel()
                raise PermissionError("test cleanup denied")

        prefix = self.reports / "cleanup-failure"
        with self.assertRaisesRegex(PermissionError, "cleanup denied"):
            CHECKS.run_verus(self.executable("print('done')\n"), os.environ.copy(), self.source / "lib.rs",
                             prefix, supervisor=FailedCleanup())
        metadata = json.loads(prefix.with_suffix(".meta.json").read_text())
        self.assertEqual(metadata["status"], "error", json.dumps(metadata, indent=2))
        self.assertEqual(metadata["cleanupError"], "PermissionError: test cleanup denied")
        self.assert_reaped(metadata["pid"])

    def test_ignored_sigterm_escalates_to_sigkill_and_reaps_leader(self):
        prefix = self.reports / "stubborn"
        binary = self.executable("import signal, time\nsignal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
                                 "print('ready', flush=True)\ntime.sleep(30)\n")
        supervisor = CHECKS.ProcessSupervisor(terminate_grace=0.1)
        with self.assertRaises(subprocess.TimeoutExpired):
            CHECKS.run_verus(binary, os.environ.copy(), self.source / "lib.rs", prefix,
                             timeout=1, supervisor=supervisor)
        meta = json.loads(prefix.with_suffix(".meta.json").read_text())
        self.assertEqual(meta["status"], "timed_out")
        self.assertEqual(meta["returncode"], -signal.SIGKILL)
        self.assert_reaped(meta["pid"])
        self.assertFalse(supervisor.processes)

    def test_cancelled_supervisor_never_spawns_a_new_process(self):
        supervisor = CHECKS.ProcessSupervisor()
        supervisor.cancel()
        with patch.object(CHECKS.subprocess, "Popen") as spawn, self.assertRaises(CHECKS.RunCancelled):
            CHECKS.run_verus("verus", {}, self.source / "lib.rs", self.reports / "never-started",
                             supervisor=supervisor)
        spawn.assert_not_called()
        meta = json.loads((self.reports / "never-started.meta.json").read_text())
        self.assertEqual(meta["status"], "cancelled")
        self.assertIsNone(meta["returncode"])

    def test_completed_stage_metadata_and_fingerprint_bind_the_source(self):
        prefix = self.reports / "complete"
        binary = self.executable("print('complete')\n")
        original = CHECKS.source_fingerprint(self.source)
        result = CHECKS.run_verus(binary, os.environ.copy(), self.source / "lib.rs", prefix,
                                  threads=1, timeout=5, compile_only=True)
        self.assertEqual(result.returncode, 0)
        meta = json.loads(prefix.with_suffix(".meta.json").read_text())
        self.assertEqual(meta["status"], "completed")
        self.assertEqual(meta["returncode"], 0)
        self.assertEqual(meta["threads"], 1)
        self.assertEqual(meta["timeoutSeconds"], 5)
        self.assertTrue(meta["compileOnly"])
        self.assertEqual(meta["sourceSha256"], original)
        (self.source / "compile-check.rlib").write_bytes(b"generated output")
        self.assertEqual(CHECKS.source_fingerprint(self.source), original)
        (self.source / "lib.rs").write_text("changed input")
        self.assertNotEqual(CHECKS.source_fingerprint(self.source), original)
        self.assert_reaped(meta["pid"])

if __name__ == "__main__":
    unittest.main()
