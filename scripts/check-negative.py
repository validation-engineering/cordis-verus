#!/usr/bin/env python3
"""Require proof failures for precise, compilable mutations of executable code."""

import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from contextlib import contextmanager
import importlib.util
import hashlib
import json
import os
from pathlib import Path
import re
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True


def toolchain():
    spec = importlib.util.spec_from_file_location("cordis_installer", ROOT / "scripts/install-verus.py")
    installer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(installer)
    lock = installer.LOCK
    binary = ROOT / ".tools" / lock["verus"]["assets"][installer.platform_key()]["directory"] / "verus"
    environment = os.environ.copy()
    cargo = Path(environment.get("CARGO_HOME", str(Path.home() / ".cargo"))) / "bin"
    environment["PATH"] = str(cargo) + os.pathsep + environment.get("PATH", "")
    environment["RUSTUP_TOOLCHAIN"] = lock["rust"]["channel"]
    return binary, environment


def available_cpus():
    """Respect process affinity and Linux container quotas, when available."""
    counts = [os.cpu_count() or 1]
    if hasattr(os, "process_cpu_count"):
        counts.append(os.process_cpu_count() or 1)
    if hasattr(os, "sched_getaffinity"):
        counts.append(len(os.sched_getaffinity(0)))
    try:
        quota, period = Path("/sys/fs/cgroup/cpu.max").read_text().split()
        if quota != "max":
            counts.append(max(1, int(quota) // int(period)))
    except (OSError, ValueError, ZeroDivisionError):
        pass
    return max(1, min(counts))


def execution_budget(jobs=1, threads=None, cpu_budget=None):
    """Resolve one explicit CPU budget shared by baseline and mutation workers."""
    available = available_cpus()
    budget = min(2 if cpu_budget is None else cpu_budget, available)
    if jobs < 1 or budget < 1 or (threads is not None and threads < 1):
        raise ValueError("jobs, threads and CPU budget must be positive")
    if threads is not None and threads > budget:
        raise ValueError(f"threads per worker ({threads}) exceed the CPU budget ({budget})")
    workers = min(jobs, budget // threads if threads is not None else budget)
    per_worker = threads or max(1, budget // workers)
    return {"availableCpus": available, "cpuBudget": budget, "requestedJobs": jobs,
            "jobs": workers, "threadsPerWorker": per_worker, "baselineThreads": per_worker}


class RunCancelled(RuntimeError):
    """An interrupted process is never acceptable proof evidence."""


class MutationFailure(RuntimeError):
    """An expected control failure, never acceptable negative proof evidence."""


class MutationBatchError(RuntimeError):
    """Diagnostic collection finished, but some controls did not pass the gate."""

    def __init__(self, outcomes):
        self.outcomes = outcomes
        failed = [row["name"] for row in outcomes if row["status"] == "failed"]
        super().__init__(f"{len(failed)} negative control(s) failed: {', '.join(failed)}")


class MutationDiagnostics:
    """Atomic progress for diagnostics; deliberately never a release report."""

    def __init__(self, mutations, reports):
        self.path = reports / "diagnostic.json"
        self.lock = threading.RLock()
        self.report = {
            "schema": "cordis.negative-diagnostic/v1",
            "releaseAcceptance": False, "keepGoing": True, "status": "running",
            "complete": False,
            "outcomes": [{"name": mutation[0], "status": "pending", "attempted": False}
                         for mutation in mutations],
        }
        self._write()

    def _write(self):
        outcomes = self.report["outcomes"]
        attempted = sum(row["attempted"] for row in outcomes)
        self.report["counts"] = {
            "selected": len(outcomes), "attempted": attempted,
            "passed": sum(row["status"] == "passed" for row in outcomes),
            "failed": sum(row["status"] == "failed" for row in outcomes),
            "notRun": len(outcomes) - attempted,
        }
        # A reader sees either the prior complete JSON value or the new one.
        path = None
        try:
            with tempfile.NamedTemporaryFile(mode="w", dir=self.path.parent,
                                             prefix=".diagnostic-", suffix=".tmp", delete=False) as output:
                path = Path(output.name)
                json.dump(self.report, output, indent=2)
                output.write("\n")
                output.flush()
            os.replace(path, self.path)
        finally:
            if path is not None:
                path.unlink(missing_ok=True)

    def update(self, index, status, *, error=None, evidence=None, fatal=False):
        with self.lock:
            row = self.report["outcomes"][index]
            row["status"] = status
            if status == "running":
                row["attempted"] = True
            if error is not None:
                row["error"] = {"type": type(error).__name__, "message": str(error)}
            if evidence is not None:
                row["evidence"] = evidence
            if fatal:
                row["fatal"] = True
            self._write()

    def finish(self, status, error=None):
        with self.lock:
            self.report["status"] = status
            # Completion records exhausted controls, not successful verification.
            # An interrupted or infrastructure-failed control is still incomplete.
            self.report["complete"] = (
                status in ("completed", "failed")
                and (error is None or isinstance(error, MutationBatchError))
                and all(row["status"] in ("passed", "failed") and not row.get("fatal", False)
                        for row in self.report["outcomes"]))
            if error is not None:
                self.report["error"] = {"type": type(error).__name__, "message": str(error)}
            self._write()


class ProcessSupervisor:
    """Own process groups until their leaders have been reaped, including on cancellation.

    Output goes to files instead of pipes: a solver inheriting an open pipe cannot
    make the runner hang after its Verus parent has exited. POSIX groups cover the
    Verus/rustc/Z3 descendants used by all supported release platforms.
    """
    def __init__(self, *, terminate_grace=1.0, poll_interval=0.05):
        self.cancelled = threading.Event()
        self.lock = threading.RLock()
        self.processes = set()
        self.term_sent = set()
        self.failure = None
        self.signal_number = None
        self.terminate_grace = terminate_grace
        self.poll_interval = poll_interval

    def check(self):
        if self.cancelled.is_set():
            raise RunCancelled("Negative verification cancelled; no proof evidence recorded")

    @staticmethod
    def _signal_group(process, number):
        try:
            os.killpg(process.pid, number)
        except ProcessLookupError:
            pass

    def terminate_once(self, process):
        # Mark before entering killpg: Python signal handlers can reenter cancel
        # while the syscall is in progress. A repeated TERM can interrupt a
        # descendant that is already reaping children and race group teardown.
        with self.lock:
            if process in self.term_sent or process._cordis_signals_closed:
                return
            self.term_sent.add(process)
            process._cordis_cleanup["signals"].append({"signal": int(signal.SIGTERM), "atUnix": time.time()})
            try:
                self._signal_group(process, signal.SIGTERM)
            except OSError as error:
                # Signal handlers must still let finish attempt the final cleanup.
                # Keep the actual error; even successful later cleanup cannot turn
                # this interruption into accepted proof evidence.
                process._cordis_signal_error = error
                process._cordis_cleanup["signalError"] = f"{type(error).__name__}: {error}"

    @staticmethod
    def _observe_exit(process):
        """Observe exit without releasing the PID that identifies our process group."""
        if process.returncode is not None:
            raise RuntimeError("Supervised child was reaped before process-group cleanup")
        if process._cordis_observer == "waitid":
            return os.waitid(os.P_PID, process.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT) is not None
        return bool(process._cordis_kqueue.control([], 1, 0))

    def wait(self, process, *, timeout):
        """Popen.wait-compatible timeout, but leave final reaping to finish()."""
        deadline = time.monotonic() + timeout
        while True:
            if process._cordis_exited or self._observe_exit(process):
                process._cordis_exited = True
                return
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise subprocess.TimeoutExpired(process.args, timeout)
            time.sleep(min(self.poll_interval, remaining))

    @staticmethod
    def _group_snapshot(process, phase):
        # ps observes zombies too. Retaining the direct child until the last
        # signal prevents PID/PGID reuse while these snapshots are inspected.
        listing = subprocess.run(["ps", "-axo", "pid=,ppid=,pgid=,uid=,stat=,comm="],
                                 capture_output=True, text=True, check=True, timeout=5)
        members = []
        for line in listing.stdout.splitlines():
            fields = line.split(None, 5)
            if len(fields) < 5:
                raise RuntimeError(f"Cannot parse process snapshot: {line!r}")
            pid, parent, group, uid = map(int, fields[:4])
            if group == process.pid:
                members.append({"pid": pid, "parentPid": parent, "groupId": group,
                                "userId": uid, "state": fields[4],
                                "command": fields[5] if len(fields) == 6 else ""})
        snapshot = {"phase": phase, "observedAtUnix": time.time(), "members": members}
        process._cordis_cleanup["snapshots"].append(snapshot)
        return snapshot

    def start(self, command, **kwargs):
        if os.name != "posix":
            raise RuntimeError("Negative verification requires POSIX process-group supervision")
        with self.lock:
            self.check()
            process = subprocess.Popen(command, start_new_session=True, **kwargs)
            process._cordis_exited = False
            process._cordis_signals_closed = False
            process._cordis_signal_error = None
            process._cordis_kqueue = None
            if all(hasattr(os, name) for name in ("waitid", "WNOWAIT", "WEXITED", "P_PID")):
                process._cordis_observer = "waitid"
            elif hasattr(select, "kqueue"):
                process._cordis_observer = "kqueue"
                process._cordis_kqueue = select.kqueue()
                try:
                    process._cordis_kqueue.control([
                        select.kevent(process.pid, filter=select.KQ_FILTER_PROC,
                                      flags=select.KQ_EV_ADD | select.KQ_EV_ENABLE,
                                      fflags=select.KQ_NOTE_EXIT)], 0, 0)
                except BaseException:
                    process._cordis_kqueue.close()
                    self._signal_group(process, signal.SIGKILL)
                    process.wait()
                    raise
            else:
                self._signal_group(process, signal.SIGKILL)
                process.wait()
                raise RuntimeError("Process supervision requires waitid(WNOWAIT) or kqueue")
            process._cordis_cleanup = {"observationMethod": process._cordis_observer,
                                       "snapshots": [], "signals": [], "leaderReaped": False}
            self.processes.add(process)
            # A signal handler can request cancellation while Popen is starting.
            if self.cancelled.is_set():
                self.terminate_once(process)
            return process

    def cancel(self, failure=None):
        with self.lock:
            if self.failure is None and failure is not None:
                self.failure = failure
            self.cancelled.set()
            for process in self.processes:
                self.terminate_once(process)

    def finish(self, process, *, terminate=False):
        """Signal only the retained group, then reap; never hide a cleanup failure."""
        cleanup = process._cordis_cleanup
        failure = process._cordis_signal_error

        def snapshot(phase):
            nonlocal failure
            try:
                return self._group_snapshot(process, phase)
            except BaseException as error:
                cleanup["snapshotError"] = f"{type(error).__name__}: {error}"
                if failure is None:
                    failure = error
                return None

        def has_live_members(observation):
            return observation is None or any(
                not member["state"].startswith("Z") for member in observation["members"])

        try:
            if process.returncode is not None:
                raise RuntimeError("Supervised child was reaped before process-group cleanup")
            before = snapshot("before-cleanup")
            if terminate:
                if has_live_members(before):
                    self.terminate_once(process)
                    failure = failure or process._cordis_signal_error
                else:
                    cleanup["termSkipped"] = "no-live-group-members"
                # Do not poll/wait here: either would release the leader PID and
                # allow teardown/reuse before the last signal to its group.
                deadline = time.monotonic() + self.terminate_grace
                while time.monotonic() < deadline:
                    time.sleep(min(self.poll_interval, max(0, deadline - time.monotonic())))
            before_kill = snapshot("before-kill")
            if before_kill is not None and not any(
                    member["pid"] == process.pid for member in before_kill["members"]):
                failure = failure or RuntimeError("Retained process-group leader is missing before cleanup")
                # The child has not been reaped, so its PID is still reserved.
                # Incomplete diagnostics must not prevent best-effort termination.
                before_kill = None
            if has_live_members(before_kill):
                cleanup["signals"].append({"signal": int(signal.SIGKILL), "atUnix": time.time()})
                self._signal_group(process, signal.SIGKILL)
            else:
                # A zombie-only group cannot run or fork. Avoid a redundant kill
                # against a group in teardown; its identity remains pinned here.
                cleanup["killSkipped"] = "no-live-group-members"
            self.wait(process, timeout=5)
            deadline = time.monotonic() + 5
            while True:
                after = snapshot("after-kill")
                if after is None or not has_live_members(after):
                    break
                if time.monotonic() >= deadline:
                    raise RuntimeError("Live process-group members remain after cleanup")
                time.sleep(self.poll_interval)
        except BaseException as error:
            if failure is not None and failure is not error:
                cleanup["additionalError"] = f"{type(error).__name__}: {error}"
            failure = failure or error
            snapshot("cleanup-error")
        finally:
            # Reap an exited leader even when group cleanup failed. A live child
            # must not make error reporting block indefinitely.
            try:
                self.wait(process, timeout=0 if failure is not None else 5)
                # A signal can arrive between wait() and removal from processes.
                # Close signaling before reap so it cannot target a reused PGID.
                process._cordis_signals_closed = True
                process.wait()
                cleanup["leaderReaped"] = True
            except BaseException as reap_error:
                cleanup["reapError"] = f"{type(reap_error).__name__}: {reap_error}"
                if failure is None:
                    failure = reap_error
            if cleanup["leaderReaped"]:
                if process._cordis_kqueue is not None:
                    process._cordis_kqueue.close()
                with self.lock:
                    self.processes.discard(process)
                    self.term_sent.discard(process)
        if failure is not None:
            raise failure

    @contextmanager
    def signal_handlers(self):
        if threading.current_thread() is not threading.main_thread():
            yield self
            return
        previous = {}

        def interrupted(number, _frame):
            self.signal_number = number
            self.cancel(RunCancelled(f"Negative verification interrupted by signal {number}"))

        try:
            for number in (signal.SIGINT, signal.SIGTERM):
                previous[number] = signal.signal(number, interrupted)
            yield self
        finally:
            for number, handler in previous.items():
                signal.signal(number, handler)


def source_fingerprint(directory):
    digest = hashlib.sha256()
    for path in sorted(directory.rglob("*.rs")):
        digest.update(path.relative_to(directory).as_posix().encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def run_verus(binary, environment, source, report_path, compile_only=False, *, threads=None,
              timeout=600, supervisor=None, diagnostics=False):
    threads = threads or execution_budget()["threadsPerWorker"]
    supervisor = supervisor or ProcessSupervisor()
    command = [
        str(binary), str(source), "--crate-name", "cordis_negative", "--crate-type=lib",
        "--edition=2021", "--no-cheating", "--output-json", "--triggers-mode", "silent",
        "--num-threads", str(threads), "--multiple-errors", "0",
    ]
    if diagnostics:
        command += ["--trace", "--time"]
    if compile_only:
        command += ["--no-verify", "--compile", "-o", str(source.parent / "compile-check.rlib")]
    started = time.monotonic()
    metadata = {"schema": "cordis.negative-stage/v1", "command": command, "threads": threads,
                "timeoutSeconds": timeout, "compileOnly": compile_only, "diagnostics": diagnostics,
                "startedAtUnix": time.time(),
                "status": "starting", "returncode": None, "sourceSha256": source_fingerprint(source.parent)}
    process = None
    stdout_path = report_path.with_suffix(".stdout.json")
    stderr_path = report_path.with_suffix(".stderr.txt")
    try:
        with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
            process = supervisor.start(command, env=environment, stdin=subprocess.DEVNULL,
                                       stdout=stdout, stderr=stderr)
            metadata["pid"] = process.pid
            while True:
                supervisor.check()
                remaining = timeout - (time.monotonic() - started)
                if remaining <= 0:
                    raise subprocess.TimeoutExpired(command, timeout)
                try:
                    supervisor.wait(process, timeout=min(supervisor.poll_interval, remaining))
                    break
                except subprocess.TimeoutExpired:
                    continue
            supervisor.check()
            metadata["status"] = "completed"
    except subprocess.TimeoutExpired:
        metadata["status"] = "timed_out"
        raise
    except RunCancelled as error:
        metadata["status"] = "cancelled"
        metadata["cancellationReason"] = str(supervisor.failure or error)
        metadata["signal"] = supervisor.signal_number
        raise
    except BaseException as error:
        metadata["status"] = "error"
        metadata["error"] = f"{type(error).__name__}: {error}"
        raise
    finally:
        try:
            if process is not None:
                supervisor.finish(process, terminate=metadata["status"] != "completed")
        except BaseException as error:
            metadata["primaryStatus"] = metadata["status"]
            if metadata["status"] not in ("timed_out", "cancelled"):
                metadata["status"] = "error"
            metadata["cleanupError"] = f"{type(error).__name__}: {error}"
            error._cordis_cleanup_failure = True
            raise
        finally:
            if process is not None:
                metadata["returncode"] = process.returncode
                metadata["cleanup"] = process._cordis_cleanup
            if metadata["status"] == "completed" and supervisor.cancelled.is_set():
                metadata["status"] = "cancelled"
                metadata["cancellationReason"] = str(supervisor.failure or "cancelled during cleanup")
                metadata["signal"] = supervisor.signal_number
            metadata["durationSeconds"] = time.monotonic() - started
            report_path.with_suffix(".meta.json").write_text(json.dumps(metadata, indent=2) + "\n")
    supervisor.check()
    return subprocess.CompletedProcess(command, process.returncode,
                                       stdout_path.read_text(errors="replace"), stderr_path.read_text(errors="replace"))


def rejected_result(name, result):
    """Accept only a complete-crate run with a concrete failed contract."""
    try:
        stats = json.loads(result.stdout)["verification-results"]
        rejected = (
            result.returncode != 0 and stats["success"] is False
            and stats["encountered-vir-error"] is False
            and type(stats["verified"]) is int and stats["verified"] > 0
            and type(stats["errors"]) is int and stats["errors"] > 0
            and stats["is-verifying-entire-crate"] is True
        )
    except (ValueError, KeyError, TypeError):
        raise MutationFailure(f"Mutation {name} produced no complete verification results") from None
    if not rejected:
        raise MutationFailure(f"Mutation {name} was not rejected by full-crate proof checking")
    if not any(line.startswith(message) for line in result.stderr.splitlines() for message in (
        "error: postcondition not satisfied", "error: precondition not satisfied",
        "error: assertion failed", "error: invariant not satisfied",
        "error: possible arithmetic underflow/overflow", "error: decreases not satisfied",
    )):
        raise MutationFailure(f"Mutation {name} has no conclusive contract failure")
    # A real failed contract must not hide a partial, resource-limited or crashed
    # whole-crate run. Rendered source excerpts are data, not diagnostics.
    resource = re.compile(
        r"rlimit|resource.limit|timed? out|timeout|solver.*unknown|"
        r"internal compiler error|panicked at|segmentation fault|killed by|out of memory",
        re.IGNORECASE,
    )
    for line in result.stderr.splitlines():
        if not re.match(r"\s*(?:[0-9]+)?\s*\|", line) and resource.search(line):
            raise MutationFailure(f"Mutation {name} has a resource or compiler failure; this is not accepted proof evidence")
    return {"name": name, "compiles": True, "verification-results": stats}


def check_mutation(mutation, baseline, temporary, reports, binary, environment, *, threads=None,
                   timeout=600, runner=run_verus, supervisor=None, diagnostics=False, compile_timeout=None):
    name, relative, original, replacement = mutation
    supervisor = supervisor or ProcessSupervisor()
    supervisor.check()
    mutated = temporary / name
    shutil.copytree(baseline, mutated)
    source = mutated / relative
    text = source.read_text()
    if text.count(original) != 1:
        raise MutationFailure(f"Mutation {name} no longer has exactly one source match; update the negative check")
    source.write_text(text.replace(original, replacement))
    options = {"threads": threads or execution_budget()["threadsPerWorker"], "timeout": timeout}
    # Existing injectable runners only need the established threads/timeout API.
    if runner is run_verus:
        options["supervisor"] = supervisor
    if diagnostics:
        options["diagnostics"] = True
    try:
        supervisor.check()
        compiled = runner(binary, environment, mutated / "lib.rs", reports / f"{name}-compile", True,
                          **{**options, "timeout": timeout if compile_timeout is None else compile_timeout})
        supervisor.check()
        if compiled.returncode != 0:
            raise MutationFailure(f"Mutation {name} did not compile; this is not an accepted proof failure")
        failed = runner(binary, environment, mutated / "lib.rs", reports / name, **options)
        supervisor.check()
    except subprocess.TimeoutExpired as error:
        if getattr(error, "_cordis_cleanup_failure", False):
            raise
        raise MutationFailure(f"Mutation {name} timed out; this is not an accepted proof failure") from None
    return rejected_result(name, failed)


def check_mutations(mutations, baseline, temporary, reports, binary, environment, *, jobs=1,
                    threads=None, timeout=600, runner=run_verus, supervisor=None, diagnostics=False,
                    compile_timeout=None, keep_going=False, diagnostic=None):
    """Bound dispatch and preserve order; optionally collect expected failures."""
    supervisor = supervisor or ProcessSupervisor()
    if threads is None:
        budget = execution_budget(jobs)
        jobs, threads = budget["jobs"], budget["threadsPerWorker"]
    if diagnostic is not None and not keep_going:
        raise ValueError("Mutation diagnostics require keep_going=True")
    if keep_going:
        (reports / "report.json").unlink(missing_ok=True)
        diagnostic = diagnostic or MutationDiagnostics(mutations, reports)
    results = [None] * len(mutations)

    def checked(index):
        started = False
        try:
            supervisor.check()
            if diagnostic is not None:
                diagnostic.update(index, "running")
            started = True
            try:
                evidence = check_mutation(mutations[index], baseline, temporary, reports, binary, environment,
                                          threads=threads, timeout=timeout, runner=runner, supervisor=supervisor,
                                          diagnostics=diagnostics, compile_timeout=compile_timeout)
            except MutationFailure as error:
                if not keep_going:
                    raise
                diagnostic.update(index, "failed", error=error)
                return error
            if diagnostic is not None:
                diagnostic.update(index, "passed", evidence=evidence)
            return evidence
        except BaseException as error:
            # Only MutationFailure above is collectable. Signals, filesystem and
            # cleanup failures still stop dispatch and terminate active peers.
            supervisor.cancel(error)
            if diagnostic is not None and started:
                status = "interrupted" if isinstance(error, (RunCancelled, KeyboardInterrupt)) else "failed"
                diagnostic.update(index, status, error=error, fatal=True)
            raise

    try:
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            pending = {}
            next_index = 0
            try:
                while pending or next_index < len(mutations):
                    supervisor.check()
                    while len(pending) < jobs and next_index < len(mutations):
                        supervisor.check()
                        pending[pool.submit(checked, next_index)] = next_index
                        next_index += 1
                    completed, _ = wait(pending, return_when=FIRST_COMPLETED)
                    # Inspect the whole completed batch before dispatching more.
                    for future in completed:
                        index = pending.pop(future)
                        evidence = future.result()
                        if isinstance(evidence, MutationFailure):
                            print(f"FAIL {mutations[index][0]}: {evidence}", flush=True)
                            continue
                        results[index] = evidence
                        stats = evidence["verification-results"]
                        print(f"OK {evidence['name']}: compiles; proof rejected ({stats['verified']} verified, {stats['errors']} errors)", flush=True)
            except BaseException as error:
                supervisor.cancel(error)
                for future in pending:
                    future.cancel()
                raise supervisor.failure or error
        supervisor.check()
    except BaseException as error:
        # Pool teardown has joined workers, so no progress update can overwrite
        # this terminal report or race process-group cleanup.
        if diagnostic is not None:
            status = "interrupted" if isinstance(error, (RunCancelled, KeyboardInterrupt)) else "failed"
            diagnostic.finish(status, error)
        raise
    if diagnostic is not None:
        failed = any(row["status"] == "failed" for row in diagnostic.report["outcomes"])
        failure = MutationBatchError(diagnostic.report["outcomes"]) if failed else None
        diagnostic.finish("failed" if failed else "completed", failure)
        if failure is not None:
            raise failure
    return results


def positive(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return number


def mutation_manifest():
    """The canonical ordered set of source mutations required by release evidence."""
    return [
        (
            "provider-lifetime-guard", "lib.rs",
            "if l.binding.provider == id && (!node.present || node.phase == Phase::Inactive || node.restoring) { return Err(Error::Relied); }",
            "// Negative test: provider lifetime guard intentionally removed.",
        ),
        (
            "cleanup-stack-fifo", "effects.rs",
            "self.tokens.pop()",
            "if self.tokens.len() == 0 { None } else { Some(self.tokens.remove(0)) }",
        ),
        (
            "provision-conflict-guard", "lib.rs",
            "if d.provides && d.port == p && self.nodes[d.owner].present { return false; }",
            "// Negative test: registered provision conflict guard removed.",
        ),
        (
            "inverse-restores-wrong-cell", "resources.rs",
            "self.cells.set(inverse.index, inverse.before);",
            "self.cells.set(inverse.index, inverse.after);",
        ),
        (
            "compaction-drops-live-bindings", "lib.rs",
            "if self.links[i].live {",
            "if !self.links[i].live {",
        ),
        (
            "stage-loses-pending-admission", "episode.rs",
            "if self.in_flight { return true; }",
            "if self.in_flight { return false; }",
        ),
        (
            "support-ignores-provider", "progress.rs",
            "ok = ok && selected[p];",
            "ok = ok;",
        ),
        (
            "journal-restores-first-inverse", "history.rs",
            "let inverse = self.entries.pop().unwrap();",
            "let inverse = self.entries.remove(0);",
        ),
        (
            "episode-token-names-wrong-inverse", "witnessed.rs",
            "let token = self.journal.len();",
            "let token = 0;",
        ),
        (
            "child-inverse-retires-parent", "ownership.rs",
            "match kernel.retire(child) {",
            "match kernel.retire(self.actor) {",
        ),
        (
            "child-handle-ignores-episode-generation", "ownership.rs",
            "if kernel.episode_generation(self.actor) != Some(expected) {",
            "if false {",
        ),
        (
            "begin-reuses-episode-generation", "lib.rs",
            "node.generation += 1;",
            "node.generation += 0;",
        ),
        (
            "driver-skips-resource-recovery", "driver.rs",
            "let _restored = self.episodes[id].rollback();",
            "let _restored = true;",
        ),
        (
            "normal-form-ignores-retirement", "global.rs",
            "&& left.fibers[n].retired == right.fibers[n].retired",
            "&& true",
        ),
        (
            "renaming-leaves-stale-provider", "alpha.rs",
            "provider: (r.forward)(b.provider)",
            "provider: b.provider",
        ),
        (
            "dynamic-stage-discards-real-inverse", "canonical.rs",
            "machine.inverses[owner as int].push(yielded.1)),",
            "machine.inverses[owner as int].push(|s: S| s)),",
        ),
        (
            "iterator-fuel-does-not-decrease", "termination.rs",
            "&&& label.1 == control::Rule::Iter ==> after[label.0 as int] < before[label.0 as int]",
            "&&& label.1 == control::Rule::Iter ==> after[label.0 as int] <= before[label.0 as int]",
        ),
        (
            "program-copy-ignores-source", "program.rs",
            "Instruction::Copy{source,index,next} => (index,self.episode.read(source).unwrap(),next),",
            "Instruction::Copy{source:_,index,next} => (index,0,next),",
        ),
        (
            "atomic-landing-skips-target-check", "program.rs",
            "match self.kernel.leave_if_changed(id) {\n            Ok(()) => {\n                self.episodes[id].cancel();",
            "match Err::<(), Error>(Error::Changed) {\n            Ok(()) => {\n                self.episodes[id].cancel();",
        ),
        (
            "api-insertion-reuses-historical-name", "program_refinement.rs",
            "n == a.allocated && z.allocated == a.allocated+1",
            "n <= a.allocated && z.allocated == a.allocated+1",
        ),
        (
            "provision-inverse-ignores-domain", "mediated.rs",
            "undo: |x: IMap<K, V>| if x.dom().contains(key) { Some(x.remove(key)) } else { None }, next",
            "undo: |x: IMap<K, V>| Some(x.remove(key)), next",
        ),
        (
            "coeffect-independence-discards-outcome", "partial_independence.rs",
            "a.unwrap().outcome == b.unwrap().outcome\n            && mediated::partial_related",
            "true\n            && mediated::partial_related",
        ),
        (
            "interception-reverses-metadata-order", "contexts.rs",
            "{Some((c.providers[k])((m.merge)(k,mu,(c.carried)(k))))} else {None}",
            "{Some((c.providers[k])((m.merge)(k,(c.carried)(k),mu)))} else {None}",
        ),
        (
            "child-removal-ignores-retained-token", "child_history.rs",
            "==> kind(token) != Some(child)\n}",
            "==> kind(token) != Some(child) || a.control.fibers[child].retired\n}",
        ),
        (
            "iterator-lift-reverses-inverse-composition", "iterators.rs",
            "f::Tracked { value: tail.value, undo: f::compose(first.undo, tail.undo) }",
            "f::Tracked { value: tail.value, undo: f::compose(tail.undo, first.undo) }",
        ),
        (
            "iterator-run-discards-continuation", "iterators.rs",
            "run(family, yielded.next, (fuel - 1) as nat, current)",
            "run(family, None, (fuel - 1) as nat, current)",
        ),
        (
            "erasure-drops-parent-read", "deletion.rs",
            "&&& (rule == c::Rule::Insert ==> z.control.fibers[actor].parent != Some(removed))",
            "&&& (rule == c::Rule::Insert ==> true)",
        ),
        (
            "entangled-recovery-loses-restriction", "entangled.rs",
            "Action::Restriction { key } => state.remove(key),",
            "Action::Restriction { key: _ } => state,",
        ),
        (
            "normal-form-counts-phantom-stages", "program_refinement.rs",
            "(x.depths[n]-1) as nat).next < x.codes[n].len())",
            "(x.depths[n]-1) as nat).next <= x.codes[n].len())",
        ),
        (
            "model-allows-undeclared-provision", "preservation.rs",
            "&& z.tables[actor].dom().subset_of(a.control.fibers[actor].provisions)",
            "&& true",
        ),
        (
            "observational-local-is-uniform", "observational_algebra.rs",
            "        == (forall|s: S| #[trigger] eq((effect(input).undo)(effect(s).value), s)),",
            "        == eq((effect(input).undo)(effect(input).value), input),",
        ),
        (
            "dependent-operation-loses-outcome-fiber", "dependent_grammar.rs",
            "&&& (lib.outcomes)(a,y.outcome)",
            "&&& true",
        ),
        (
            "grammar-inverse-forgets-captured-provider", "grammar_lift.rs",
            "inverse:Inverse::Operation {provider,key,undo:y.undo}",
            "inverse:Inverse::Operation {provider:actor,key,undo:y.undo}",
        ),
        (
            'grammar-repeat-call-uses-fresh-token',
            'grammar_lift.rs',
            'first_call(a.history,actor,a.state.iterators[actor].unwrap(),a.state)',
            'a.history.len()',
        ),
        (
            'child-driver-removal-ignores-journals',
            'child_driver.rs',
            'if self.has_reference(id) {return Err(ChildDriverError::Retained);}',
            'if false && self.has_reference(id) {return Err(ChildDriverError::Retained);}',
        ),
        (
            'child-driver-skips-drift-diversion',
            'child_driver.rs',
            'if !has_target {\n                    proof {self.kernel.paper_observations(id);}',
            'if false && !has_target {\n                    proof {self.kernel.paper_observations(id);}',
        ),
        (
            'dependent-landing-drops-continuation',
            'dependent_lift.rs',
            'roots:a.roots,current:a.current.insert(actor,next),history:a.history.push(e)',
            'roots:a.roots,current:a.current.insert(actor,None),history:a.history.push(e)',
        ),
        (
            'grammar-inverse-origin-fifo-token',
            'grammar_ordering.rs',
            'token==tokens.last() && before==input && after==next',
            'token==tokens.first() && before==input && after==next',
        ),
        (
            "unload-state-map-forgets-actual-stack", "rule_frames.rs",
            "Source::Restoration{actor,tokens:a.accumulators[actor]}",
            "Source::Restoration{actor,tokens:Seq::empty()}",
        ),
        (
            'iterator-independence-discards-continuation', 'iterator_independence.rs',
            'q::continuation(|i:I,j:I|q::iterator_related(eq,family,i,j),a.next,b.next)',
            'true',
        ),
        (
            'indexed-model-forgets-inverse-token', 'indexed_ordering.rs',
            'local_model(s::Yield {state:out.state,inverse:a.history.len(),next:dl::marker(out.next)},receipt_history(a.history))',
            'local_model(s::Yield {state:out.state,inverse:0,next:dl::marker(out.next)},receipt_history(a.history))',
        ),
        (
            'mixed-removal-ignores-retention', 'mixed_grammar.rs',
            '&& ch::remove_unreferenced(kind(a.history),a.state,actor)',
            '&& true',
        ),
        (
            'mixed-child-inverse-skips-retirement', 'mixed_grammar.rs',
            'if s::registered(a,child) {Some(s::with_control(a,global::retire_fiber(a.control,child)))} else {None}',
            'if s::registered(a,child) {Some(a)} else {None}',
        ),
        (
            'grammar-recovery-discards-restriction', 'grammar_recovery.rs',
            'gl::Inverse::Provision {key}=>e::Action::Restriction {key},',
            'gl::Inverse::Provision {key:_}=>e::Action::Identity,',
        ),
        (
            'mixed-origin-skips-inverse-context', 'mixed_ordering.rs',
            'invokes(history,tokens.drop_last(),next,actor,token,before,after)',
            'invokes(history,tokens.drop_last(),input,actor,token,before,after)',
        ),
        (
            'mixed-recovery-child-corrupts-table', 'mixed_recovery.rs',
            'mx::Receipt::Child {..}=>e::Action::Identity',
            'mx::Receipt::Child {..}=>e::Action::Restriction {key:Port {key:0,realm:0}}',
        ),
        (
            'iterator-bridge-compares-failed-foreign-map', 'iterator_bridge.rs',
            'requires stable(eq,family,id,map),map(s).is_some(),',
            'requires stable(eq,family,id,map),map(s).is_none(),',
        ),
        (
            'mixed-transposition-ignores-parent-read', 'mixed_transposition.rs',
            'insertion_ready(lib,programs,b,id,parent,dependencies,provisions,root),parent!=Some(child),',
            'insertion_ready(lib,programs,b,id,parent,dependencies,provisions,root),',
        ),
        (
            'recovery-example-inverse-adds-again', 'recovery_examples.rs',
            'undo:|after:int|Some(after-amount)',
            'undo:|after:int|Some(after+amount)',
        ),
        (
            'mixed-transport-drops-new-receipt', 'mixed_transport.rs',
            'history:if g::landing(left,next,rule) {right.history.push(next.history.last())} else {right.history}',
            'history:right.history',
        ),
        (
            'observational-witness-discards-recovery', 'observational_grammar.rs',
            'operation_respects(eq,op) && operation_witness(eq,op)',
            'operation_respects(eq,op)',
        ),
        (
            'observational-journal-discards-commutation', 'observational_recovery.rs',
            'k!=j || forall|v:V| #[trigger] eq(k,f(g(v)),g(f(v)))',
            'true',
        ),
        (
            'mixed-retire-actor-read-bypass', 'mixed_orchestration.rs',
            'requires s::registered(a.state,id),s::registered(a.state,actor),id!=actor,',
            'requires s::registered(a.state,id),s::registered(a.state,actor),',
        ),
        (
            'mixed-remove-provider-read-bypass', 'mixed_orchestration.rs',
            'requires inv::well_formed(a.state),s::registered(a.state,id),a.state.control.fibers[id].phase==crate::Phase::Inactive,\n        id!=actor,g::run(lib,node,a.state,actor).is_some(),',
            'requires inv::well_formed(a.state),s::registered(a.state,id),\n        id!=actor,g::run(lib,node,a.state,actor).is_some(),',
        ),
        (
            'causal-suffix-history-bypass', 'causal_normalization.rs',
            'let moved=transport::transport(states.subrange(i+2,states.len() as int),labels.subrange(i+2,labels.len() as int),reverse);',
            'let moved=states.subrange(i+2,states.len() as int);',
        ),
        (
            'administrative-self-retire-bypass', 'administrative_orchestration.rs',
            '&& !(rule==r::Rule::Begin && external==r::Rule::Retire && actor==id)',
            '&& true',
        ),
        (
            'strict-journal-forgets-foreign-inverse', 'strict_journal.rs',
            'crosses(eq,journal(prefix),e.forward) && crosses(eq,journal(prefix),e.inverse)',
            'crosses(eq,journal(prefix),e.forward)',
        ),
        (
            'unload-captured-child-bypass',
            'unload_orchestration.rs',
            'external==r::Rule::Remove && id!=actor && no_child(a.history,a.state.accumulators[actor],id)',
            'external==r::Rule::Remove && id!=actor',
        ),
        (
            'isolated-history-counts-deleted-entry', 'isolated_deletion.rs',
            'g::owner(history[token as int-1].landed.receipt)==removed {0nat} else {1nat}',
            'g::owner(history[token as int-1].landed.receipt)==removed {1nat} else {1nat}',
        ),
        (
            'rewrite-receipt-correspondence-bypass',
            'rewrite_confluence.rs',
            'a.len()==z.len() && forall|i:int| 0<=i<a.len() ==> tr::related(a[i],z[i])',
            'a.len()==z.len() && forall|i:int| 0<=i<a.len() ==> a[i].state==z[i].state && a[i].roots==z[i].roots && a[i].current==z[i].current',
        ),
        (
            'iteration-forward-only-bypass', 'mixed_iteration_exchange.rs',
            '|| pi::value_independent(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x),(lib.apply)(b,y))',
            '|| pi::commutes(|u:U,v:U|eq((lib.key)(a),u,v),pi::value_forward((lib.apply)(a,x)),pi::value_forward((lib.apply)(b,y)))',
        ),
        (
            'entangled-loading-drops-pinning', 'entangled_loading.rs',
            'forall|owner:usize| gr::installed(state,owner) ==> gr::pinned(state,owner)',
            'true',
        ),
        (
            'shared-history-reuses-source-landing', 'shared_execution.rs',
            'g::land(lib,programs,target,actor,next.state.control.fibers[actor].phase)',
            'g::land(lib,programs,source,actor,next.state.control.fibers[actor].phase)',
        ),
        (
            'shared-outcome-stability-bypass', 'shared_replay.rs',
            '==> pi::value_independent(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x),(lib.apply)(b,y))',
            '==> (forall|f:m::PartialMap<U>,g:m::PartialMap<U>| #![trigger pi::value_generators((lib.apply)(a,x)).contains(f),pi::value_generators((lib.apply)(b,y)).contains(g)] pi::value_generators((lib.apply)(a,x)).contains(f) && pi::value_generators((lib.apply)(b,y)).contains(g) ==> pi::commutes(|u:U,v:U|eq((lib.key)(a),u,v),f,g))',
        ),
        (
            'mixed-driver-xor-skips-payload', 'mixed_driver.rs',
            'self.write_slot(provider,index,Some(value^mask));\n',
            'self.write_slot(provider,index,Some(value));\n',
        ),
        (
            'observational-runs-domain-bypass',
            'mixed_observational_runs.rs',
            '    &&& a.control==b.control\n    &&& forall|id:usize| s::registered(a,id) ==> {\n        &&& a.tables[id].dom()==b.tables[id].dom()\n        &&& forall|key:Port| a.tables[id].dom().contains(key) ==> eq(key,a.tables[id][key],b.tables[id][key])\n    }',
            '    &&& a.control==b.control\n    &&& forall|id:usize| s::registered(a,id) ==> {\n        &&& forall|key:Port| a.tables[id].dom().contains(key) ==> eq(key,a.tables[id][key],b.tables[id][key])\n    }',
        ),
        (
            'observational-receipts-projection-bypass',
            'mixed_observational_runs.rs',
            'requires exchange::mixed_names(left,right),m::partial_related(pi::context_eq(eq),exchange::inverse(left),exchange::inverse(right)),',
            'requires exchange::mixed_names(left,right),',
        ),
        (
            'observational-token-renaming-bypass',
            'mixed_observational_transport.rs',
            'Seq::new(source.len(),|i:int|token(h,source[i]))',
            'source',
        ),
        (
            'foreign-inverse-discards-reverse-witness',
            'foreign_unload.rs',
            'inverse:prior[token as int].forward,own:false',
            'inverse:identity(),own:false',
        ),
        (
            'external-input-forgets-parent-renaming',
            'external_inputs.rs',
            'actor:(rho.forward)(actor),parent:names::parent(rho,parent),dependencies,provisions,root:(h.forward)(root)',
            'actor:(rho.forward)(actor),parent,dependencies,provisions,root:(h.forward)(root)',
        ),
        (
            'fresh-history-name-support',
            'fresh_grammar.rs',
            '.union(ISet::new(|name:usize|exists|i:int|0<=i<a.history.len() && entry_names(action,a.history[i]).contains(name)))',
            '.union(ISet::empty())',
        ),
        (
            'fresh-landing-discards-allocation-choice',
            'fresh_semantics.rs',
            'landed:run(lib,programs(actor)(iterator),a.state,actor,choice).unwrap()',
            'landed:run(lib,programs(actor)(iterator),a.state,actor,None).unwrap()',
        ),
        (
            'allocation-child-provision-collision',
            'allocation_inputs.rs',
            'pub open spec fn key_b()->Port {Port {key:1,realm:0}}',
            'pub open spec fn key_b()->Port {Port {key:0,realm:0}}',
        ),
        (
            'fresh-driver-child-blueprint',
            'fresh_driver.rs',
            'super::Instruction::Child {blueprint,next,..}=>super::Instruction::Child {expected:draft.rows.len(),blueprint,next},',
            'super::Instruction::Child {blueprint:_,next,..}=>super::Instruction::Child {expected:draft.rows.len(),blueprint:0,next},',
        ),
        (
            'shared-unload-keeps-uncompressed-token',
            'shared_unload_execution.rs',
            'tokens.map(|_i:int,t:nat|index(history,offset,owner,t))',
            'tokens.map(|_i:int,t:nat|t)',
        ),
        (
            'fresh-equivariance-retains-literal-parent',
            'fresh_equivariance.rs',
            '==crate::mixed_transposition::insert(f::configuration(rho,h,a),(rho.forward)(actor),names::parent(rho,parent),dependencies,provisions,(h.forward)(root))',
            '==crate::mixed_transposition::insert(f::configuration(rho,h,a),(rho.forward)(actor),parent,dependencies,provisions,(h.forward)(root))',
        ),
        (
            'guarded-child-domain-success-only',
            'guarded_child_domains.rs',
            '            && p::project(left.state,keys)==p::project(right.state,keys)\n            ==> #[trigger] defined(left)==#[trigger] defined(right)',
            '            && p::project(left.state,keys)==p::project(right.state,keys)\n            && defined(left) && defined(right)\n            ==> #[trigger] defined(left)==#[trigger] defined(right)',
        ),
        (
            'admitted-fresh-generation-guard',
            'admitted_fresh_driver.rs',
            'if draft.kernel.episode_generation(actor)!=Some(self.generation) {return Err(AdmissionError::StaleAdmission);}',
            'let _unchecked_generation=draft.kernel.episode_generation(actor);',
        ),
        (
            'admitted-script-event-provenance',
            'admitted_script.rs',
            'events.push(ScriptEvent {action_index:i,effect});',
            'events.push(ScriptEvent {action_index:i+1,effect});',
        ),
        (
            'selective-recovery-forgets-owner-foreign-crossing',
            'selective_foreign_recovery.rs',
            '(!records[i].own || !call.own)',
            '(!records[i].own && !call.own)',
        ),
        (
            'providing-owner-publication-guard-bypass',
            'providing_owner_transport.rs',
            '        deletion::separated(source.state,owner),s::registered(source.state,actor),actor!=owner,',
            '        s::registered(source.state,actor),actor!=owner,',
        ),
        (
            'strict-batch-redo-guard-bypass',
            'strict_batch_recovery.rs',
            '        p::commutes(eq,foreign,redo),p::commutes(eq,foreign,undo),',
            '        p::commutes(eq,foreign,undo),',
        ),
        (
            'strict-batch-old-record-retraction',
            'strict_batch_recovery.rs',
            '        !fu::retracts(tables_equal(),fu::Pair {forward:old_events()[0].forward,inverse:old_events()[0].inverse,own:false},cut()),\n        m::run',
            '        fu::retracts(tables_equal(),fu::Pair {forward:old_events()[0].forward,inverse:old_events()[0].inverse,own:false},cut()),\n        m::run',
        ),
        (
            'orchestration-support-cycle-parent-blocks-removal',
            'orchestration_support_cycle.rs',
            't::insert(a2,2,Some(1),',
            't::insert(a2,2,Some(0),',
        ),
        (
            'old-receipt-current-domain-bypass',
            'old_receipt_support.rs',
            '        g::run(lib,programs(actor)(old.iterator),old.input,actor)==Some(old.landed),g::undo(old.landed.receipt,current).is_some(),',
            '        g::run(lib,programs(actor)(old.iterator),old.input,actor)==Some(old.landed),',
        ),
        (
            'old-journal-provider-guard-bypass',
            'old_journal_unload.rs',
            '        state.control.fibers[owner].phase!=Phase::Inactive,!r::relied(state.control,actor),',
            '        state.control.fibers[owner].phase!=Phase::Inactive,',
        ),
        (
            'old-journal-terminal-phase-bypass',
            'old_journal_closure.rs',
            '        target_proof::controls(z,out,owner),source_proof::separated(z.state,owner),z.state.control.fibers[owner].phase==Phase::Unloading,',
            '        target_proof::controls(z,out,owner),source_proof::separated(z.state,owner),',
        ),
        (
            'observational-permutation-forgets-commutation',
            'observational_permutation.rs',
            'witnessed(eq,effects),commuting(eq,p::returned(effects,x)),p::permutation(order,effects.len()),',
            'witnessed(eq,effects),p::permutation(order,effects.len()),',
        ),
        (
            'component-totality-drops-provision-obligation',
            'paper_invariants.rs',
            '==> provisions.subset_of(owned(it::run(family,Some(root),fuel,f::unit(input)).current.value).dom())',
            '==> true',
        ),
        (
            'functional-quotient-begin-own-root',
            'functional_quotient.rs',
            'r::Rule::Begin=>s::edit(b,n,Phase::Loading,z.control.fibers[n].committed,Some(b.effects[n]),Seq::empty()),',
            'r::Rule::Begin=>s::edit(b,n,Phase::Loading,z.control.fibers[n].committed,Some(a.effects[n]),Seq::empty()),',
        ),
        (
            'old-journal-own-as-foreign',
            'old_journal_interleaving.rs',
            '        0<=j<fu::catalog(actions.drop_last()).len(),fu::catalog(actions.drop_last())[j].own,\n        !fu::event(fu::catalog(actions.drop_last()),actions.last()).own,',
            '        0<=j<fu::catalog(actions.drop_last()).len(),fu::catalog(actions.drop_last())[j].own,',
        ),
        (
            'mixed-age-token-identity',
            'mixed_age_unload.rs',
            '        let token=tokens.last();let mapped=history::index(left,offset,owner,token);',
            '        let token=tokens.last();let mapped=token;',
        ),
        (
            'old-provision-without-installed-owner',
            'old_provision_support.rs',
            'current.control.fibers[owner].phase!=Phase::Inactive,!r::relied(current.control,actor),\n        g::undo(receipt::<U>(actor,key),current).is_some(),',
            '!r::relied(current.control,actor),\n        g::undo(receipt::<U>(actor,key),current).is_some(),',
        ),
        (
            'configuration-enabled-polarity',
            'configuration_entry.rs',
            '        !self.disabled\n',
            '        self.disabled\n',
        ),
        (
            'resolution-completion-missing-retirement',
            'resolution_completion_counterexample.rs',
            '    let a3=orchestration::retire(a2,0);',
            '    let a3=a2;',
        ),
        (
            'old-provision-journal-finishes-before-cut',
            'old_provision_journal_example.rs',
            'select:|_:()|if actor==2 && stage==1 {Some(2nat)}else{None}',
            'select:|_:()|None',
        ),
        (
            'internal-old-owner-capture',
            'internal_old_unload.rs',
            '        prefix.push(if g::landing(a,z,label.1) {fu::Action::Forward {call:fu::entry_pair(lib,programs,g::entry(lib,programs,a,label.0),owner)}} else {fu::Action::Identity})',
            '        prefix.push(if g::landing(a,z,label.1) {fu::Action::Forward {call:fu::entry_pair(lib,programs,g::entry(lib,programs,a,label.0),label.0)}} else {fu::Action::Identity})',
        ),
        (
            'derived-recovery-keeps-discarded-handle',
            'effect_realization.rs',
            'Some((heap.remove(child),parent))',
            'Some((heap.remove(child),child))',
        ),
        (
            'interface-outside-frame',
            'interface_observation.rs',
            'requires o::related_maps(observed(eq,keys,project),f,g),map_frame(keys,project,f),map_frame(keys,project,g),',
            'requires o::related_maps(observed(eq,keys,project),f,g),map_frame(keys,project,f),',
        ),
        (
            'internal-table-inactive-phase',
            'internal_table_unload.rs',
            's::registered(a.state,owner),a.state.control.fibers[owner].phase==Phase::Inactive,',
            's::registered(a.state,owner),true,',
        ),
        (
            'generalized-table-rejects-new-provision',
            'generalized_table_deletion.rs',
            'source_proof::table_node(node)\n    }',
            'source_proof::table_node(node) && (labels[i].0!=owner ==> replay::operational_mixed(node))\n    }',
        ),
        (
            'foreign-provision-target-domain',
            'foreign_provision_transport.rs',
            'requires s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],source.tables[actor].dom()==target.tables[actor].dom(),',
            'requires s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],',
        ),
        (
            'dependent-independence-discards-yield-stability',
            'dependent_independence.rs',
            '==> p::value_independent(|u:U,v:U|eq((l.key)(a),u,v),(l.apply)(a,x),(r.apply)(b,y))',
            '==> (forall|f:m::PartialMap<U>,g:m::PartialMap<U>| #![trigger p::value_generators((l.apply)(a,x)).contains(f),p::value_generators((r.apply)(b,y)).contains(g)] p::value_generators((l.apply)(a,x)).contains(f) && p::value_generators((r.apply)(b,y)).contains(g) ==> p::commutes(|u:U,v:U|eq((l.key)(a),u,v),f,g))',
        ),
        (
            'dynamic-insert-ignores-private-dependency',
            'dynamic_table_registry.rs',
            'actor!=owner && (rule==r::Rule::Insert ==> z.state.control.fibers[actor].dependencies.disjoint(a.state.control.fibers[owner].provisions))',
            'actor!=owner',
        ),
        (
            'strict-partial-quotient-ignores-inverse-word',
            'strict_partial_quotient.rs',
            '|input:s::State<U>|g::restore(a.history,a.state.accumulators[actor],input,actor)',
            '|input:s::State<U>|g::restore(a.history,Seq::empty(),input,actor)',
        ),
        (
            'strict-partial-quotient-per-forgets-symmetry',
            'strict_partial_quotient_per.rs',
            '&&& forall|x:S,y:S| #[trigger] eq(x,y) ==> eq(y,x)',
            '&&& true',
        ),
        (
            'strict-alias-ignores-static-primitive',
            'strict_partial_quotient_reflexive.rs',
            'requires inv::well_formed(a),d::permitted(lib,ISet::full(),ISet::full(),node),dep::run(lib,node,a,actor).is_some(),',
            'requires inv::well_formed(a),dep::run(lib,node,a,actor).is_some(),',
        ),
        (
            'paper-component-missing-leastness',
            'paper_components.rs',
            'it::paper_witnessed(|a:G,b:G|observed(eq,coeffects,c.dependencies.union(c.provisions),a,b),family,c.root)',
            'it::witnessed(|a:G,b:G|observed(eq,coeffects,c.dependencies.union(c.provisions),a,b),family,c.root)',
        ),
        (
            'paper-observation-active-accumulator-erased',
            'paper_observations.rs',
            '(Theta::Active {accumulator:g,committed:a},Theta::Active {accumulator:h,committed:b})=>a==b && o::related_maps(base,g,h),',
            '(Theta::Active {accumulator:g,committed:a},Theta::Active {accumulator:h,committed:b})=>a==b,',
        ),
        (
            'paper-confinement-wrong-read-registry',
            'paper_confinement.rs',
            '    &&& forall|m:N,k:K| p::registered(view,a,m) && d.contains(k)\n        ==> p::lookup(view,a,m,k)==p::lookup(view,b,m,k)',
            '    &&& forall|m:N,k:K| p::registered(view,b,m) && d.contains(k)\n        ==> p::lookup(view,a,m,k)==p::lookup(view,b,m,k)',
        ),
        (
            'foreign-child-owner-guard',
            'foreign_child_transport.rs',
            'actor!=owner && match programs(actor)(a.current[actor].unwrap())',
            'match programs(actor)(a.current[actor].unwrap())',
        ),
        (
            'paper-instantiation-captured-parent',
            'paper_instantiation.rs',
            'Some(state)=>Some(Landing {state,name:child,inverse:Receipt{child},next:body(child)}),',
            'Some(state)=>Some(Landing {state,name:child,inverse:Receipt{child:parent},next:body(child)}),',
        ),
        (
            'foreign-child-private-dependency-guard',
            'foreign_child_deletion.rs',
            'source_proof::table_node(node) || child::guard(programs,source[i],labels[i].0,owner)',
            'source_proof::table_node(node) || (labels[i].0!=owner && child::child_node(node))',
        ),
        (
            'paper-trace-child-dependencies',
            'paper_trace_independence.rs',
            'a.dependencies==b.dependencies && a.provisions==b.provisions && relation((left,a.root),(right,b.root))',
            'true && a.provisions==b.provisions && relation((left,a.root),(right,b.root))',
        ),
        (
            'cleanup-batch-ignores-lease-owner',
            'publication_cleanup.rs',
            'if entry.consumer!=Some(owner) {return Err(PublicationError::InvalidState);}',
            'if false {return Err(PublicationError::InvalidState);}',
        ),
        (
            'cleanup-commits-before-resource-validation',
            'cleanup_release.rs',
            '        let released=match registry.cleanup_batch(LeaseOwner {owner:id,generation},leases,publications) {\n            Ok(released)=>released,Err(e)=>return Err(CleanupReleaseError::Publication(e)),\n        };\n        if reservation {self.finish_reservation_cleanup(kernel,id).unwrap();}\n        else {self.finish_cleanup(kernel,id).unwrap();}',
            '        if reservation {self.finish_reservation_cleanup(kernel,id).unwrap();}\n        else {self.finish_cleanup(kernel,id).unwrap();}\n        let released=match registry.cleanup_batch(LeaseOwner {owner:id,generation},leases,publications) {\n            Ok(released)=>released,Err(e)=>return Err(CleanupReleaseError::Publication(e)),\n        };',
        ),
        (
            'cleanup-journal-discards-failed-inverse',
            'cleanup_journal.rs',
            'if outcome==RestoreOutcome::Failed {self.failed=true;}',
            'if outcome==RestoreOutcome::Failed {self.current=None;}',
        ),
        (
            'cleanup-queue-discards-retained-payload',
            'cleanup_queue.rs',
            'self.payloads[ticket.token]=retained;',
            'self.payloads[ticket.token]=None;',
        ),
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=positive, default=os.environ.get("CORDIS_NEGATIVE_JOBS", "1"),
                        help="independent mutation workers (default: CORDIS_NEGATIVE_JOBS or 1)")
    parser.add_argument("--threads", type=positive,
                        default=os.environ.get("CORDIS_NEGATIVE_THREADS"),
                        help="Verus threads per worker (default: share available CPU budget)")
    parser.add_argument("--cpu-budget", type=positive, default=os.environ.get("CORDIS_NEGATIVE_CPU_BUDGET"),
                        help="total CPU budget, capped to available CPUs (default: min(available CPUs, 2))")
    parser.add_argument("--timeout", type=positive, default=os.environ.get("CORDIS_NEGATIVE_TIMEOUT", "600"),
                        help="wall-clock seconds per subprocess (default: CORDIS_NEGATIVE_TIMEOUT or 600); timeout never counts as rejection")
    parser.add_argument("--keep-going", action="store_true",
                        help="collect every selected negative control after expected failures; writes diagnostic.json, never release evidence")
    args = parser.parse_args()
    try:
        budget = execution_budget(args.jobs, args.threads, args.cpu_budget)
    except ValueError as error:
        parser.error(str(error))
    supervisor = ProcessSupervisor()
    timeout = args.timeout
    binary, environment = toolchain()
    reports = ROOT / "target/proof-negative"
    reports.mkdir(parents=True, exist_ok=True)
    (reports / "report.json").unlink(missing_ok=True)
    mutations = mutation_manifest()
    diagnostic = MutationDiagnostics(mutations, reports) if args.keep_going else None
    try:
        return run_checks(binary, environment, reports, mutations, supervisor, budget, timeout,
                          keep_going=args.keep_going, diagnostic=diagnostic)
    except BaseException as error:
        # A signal or cleanup failure after the last mutation must not leave a
        # successful release report behind, including in the default mode.
        (reports / "report.json").unlink(missing_ok=True)
        if diagnostic is not None and not isinstance(error, MutationBatchError):
            status = "interrupted" if isinstance(error, (RunCancelled, KeyboardInterrupt)) else "failed"
            diagnostic.finish(status, error)
        if isinstance(error, RuntimeError):
            sys.exit(f"{error}; see {reports}")
        raise


def run_checks(binary, environment, reports, mutations, supervisor, budget, timeout, *,
               keep_going=False, diagnostic=None):
    jobs, threads = budget["jobs"], budget["threadsPerWorker"]
    with supervisor.signal_handlers(), tempfile.TemporaryDirectory(prefix="cordis-negative-") as temporary:
        temporary = Path(temporary)
        baseline = temporary / "baseline"
        shutil.copytree(ROOT / "crates/cordis-kernel/src", baseline)
        try:
            result = run_verus(binary, environment, baseline / "lib.rs", reports / "baseline", threads=budget["baselineThreads"],
                               timeout=timeout, supervisor=supervisor)
        except subprocess.TimeoutExpired:
            sys.exit(f"Unmodified kernel timed out; no proof evidence recorded; see {reports}")
        if result.returncode != 0:
            sys.exit(f"Unmodified kernel failed verification; see {reports / 'baseline.stderr.txt'}")
        baseline_json = json.loads(result.stdout)
        baseline_stats = baseline_json["verification-results"]
        if (not baseline_stats["success"] or baseline_stats["errors"] != 0
                or baseline_stats["verified"] == 0 or baseline_stats["encountered-vir-error"]
                or not baseline_stats["is-verifying-entire-crate"]):
            sys.exit("Unmodified kernel did not produce a successful, nonempty verification report")
        print(f"OK unmodified kernel: {baseline_stats['verified']} verified, 0 errors", flush=True)
        summary = {"verus": baseline_json["verus"], "baseline": baseline_stats,
                   "execution": {**budget, "timeoutSeconds": timeout},
                   "mutations": []}
        print(f"Checking {len(mutations)} mutations with {jobs} worker(s), {threads} Verus threads per worker", flush=True)
        summary["mutations"] = check_mutations(mutations, baseline, temporary, reports, binary,
                                              environment, jobs=jobs, threads=threads, timeout=timeout,
                                              supervisor=supervisor, keep_going=keep_going,
                                              diagnostic=diagnostic)
        supervisor.check()
        if not keep_going:
            (reports / "report.json").write_text(json.dumps(summary, indent=2) + "\n")
    # Signal handlers cancel the supervisor without throwing. Check again after
    # temporary-tree cleanup, which can receive a signal after the body check.
    supervisor.check()
    return 0


if __name__ == "__main__":
    sys.exit(main())
