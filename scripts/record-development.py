#!/usr/bin/env python3
"""Record fresh development checks; never substitute for release verification/v3."""

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import signal
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "docs/development-report.json"
SCHEMA = "cordis-verus.development/v1"
MARKER = "DEVELOPMENT CHECKS PASSED; full negative controls and release acceptance are separate."
WORKSPACE_BEGIN = "BEGIN WORKSPACE TESTS"
WORKSPACE_END = "END WORKSPACE TESTS"
VERIFIER_LOCK = Path("/tmp/cordis-local-verifier.lock")
FIXED_SCRIPTS = (
    "scripts/record-development.py", "scripts/check-development.sh",
    "scripts/record-verification.py", "scripts/check-paper-coverage.py",
    "scripts/verify.sh", "scripts/toolchain-env.sh", "scripts/install-verus.py",
    "scripts/package-check.py",
)
HARNESS_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def release_helpers():
    path = ROOT / "scripts/record-verification.py"
    # Execute the bytes that were read, without a potentially stale .pyc cache.
    original = path.read_bytes()
    spec = importlib.util.spec_from_file_location("release_record", path)
    module = importlib.util.module_from_spec(spec)
    exec(compile(original, str(path), "exec"), module.__dict__)
    if path.read_bytes() != original:
        raise RuntimeError("Source-hash helper changed while loading")
    return module


def source_hashes():
    hashes = release_helpers().source_hashes()
    # Generated evidence must not invalidate its own input fingerprint.
    hashes.pop("docs/development-report.json", None)
    return hashes


def workflow_binding(hashes):
    if any(name not in hashes for name in FIXED_SCRIPTS):
        raise RuntimeError("Missing fixed development workflow script")
    if hashes["scripts/record-development.py"] != HARNESS_SHA256:
        raise RuntimeError("Development recorder changed after it was loaded")
    return {name: hashes[name] for name in FIXED_SCRIPTS}


def parse_results(log):
    lines = log.splitlines()
    proofs = re.findall(r"^verification results:: (\d+) verified, (\d+) errors$", log, re.M)
    if (len(proofs) != 1 or int(proofs[0][0]) <= 0 or int(proofs[0][1]) != 0
            or lines.count(MARKER) != 1 or not lines or lines[-1] != MARKER):
        raise RuntimeError("Incomplete development checks or failed whole-crate proof")
    if lines.count(WORKSPACE_BEGIN) != 1 or lines.count(WORKSPACE_END) != 1:
        raise RuntimeError("Missing or ambiguous workspace test section")
    start, end = lines.index(WORKSPACE_BEGIN), lines.index(WORKSPACE_END)
    proof_line = f"verification results:: {proofs[0][0]} verified, 0 errors"
    if not (lines.index(proof_line) < start < end < len(lines) - 1):
        raise RuntimeError("Development check sections are out of order")
    tests = "\n".join(lines[start + 1:end])
    if re.search(r"test result: (?!ok\.)|test result: ok\.[^\n]*; [1-9][0-9]* failed;", tests):
        raise RuntimeError("Workspace tests failed")
    counts = release_helpers().test_counts(tests)
    # This number is a release-helper constant, not measured by this log parser.
    counts.pop("deterministicTraces", None)
    return {"verified": int(proofs[0][0]), "errors": 0, "wholeCrate": True,
            "compiled": True, "noCheating": True}, counts


def save_record(record):
    """A reader sees either a complete record or the preceding complete record."""
    RECORD.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=RECORD.parent,
                                         prefix=".development-report-", suffix=".tmp", delete=False) as stream:
            temporary = Path(stream.name)
            json.dump(record, stream, ensure_ascii=False, indent=2)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, RECORD)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


@contextmanager
def verifier_lease():
    # Unix-only pinned Verus platforms; serialize checks and evidence capture.
    with VERIFIER_LOCK.open("a") as lease:
        fcntl.flock(lease, fcntl.LOCK_EX)
        yield


class TerminationRequested(KeyboardInterrupt):
    """Turn CI/terminal stop signals into the same cleanup path as Ctrl-C."""


@contextmanager
def termination_signals(spawn=None):
    previous = {}
    def stop(signum, _frame):
        if spawn is not None and spawn["pending_spawn"]:
            # A process group cannot be cleaned up until Popen returns its pid.
            spawn["signal"] = signum
        else:
            raise TerminationRequested(f"received {signal.Signals(signum).name}")
    try:
        for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            previous[signum] = signal.getsignal(signum)
            signal.signal(signum, stop)
        yield
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)


def terminate_group(process):
    """Stop all descendants and reap the leader before the lease is released."""
    def send(sig):
        while True:
            try:
                os.killpg(process.pid, sig)
                return
            except ProcessLookupError:
                return
            except KeyboardInterrupt:
                continue
    try:
        send(signal.SIGTERM)
        process.wait(timeout=2)
    except BaseException:
        # Escalation is also required when a second interrupt arrives in cleanup.
        pass
    finally:
        # The shell may already have exited while a descendant ignored TERM.
        # With output redirected to a file, waiting on the leader cannot tell.
        send(signal.SIGKILL)
        while True:
            try:
                process.wait()
                break
            except KeyboardInterrupt:
                send(signal.SIGKILL)


def run_checks(command, environment, log):
    with log.open("w") as stream:
        spawn = {"pending_spawn": True, "signal": None}
        with termination_signals(spawn):
            process = subprocess.Popen(command, cwd=ROOT, env=environment, stdout=stream,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                spawn["pending_spawn"] = False
                if spawn["signal"] is not None:
                    raise TerminationRequested(f"received {signal.Signals(spawn['signal']).name} while spawning")
                return process.wait()
            except BaseException:
                terminate_group(process)
                raise


def failed_record(record, error):
    # Never retain passed proof/package fields after an interrupted final write.
    failed = {key: value for key, value in record.items()
              if key not in {"checkedAt", "host", "proof", "tests", "packages", "examples", "logSha256", "workflowSha256"}}
    failed.update(status="failed", failure=f"{type(error).__name__}: {error}", sha256={})
    return failed


def environment_for(offline):
    environment = os.environ.copy()
    unsupported = ("VERUS_Z3_PATH", "VERUS_EXTRA_ARGS", "RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER")
    if any(environment.get(name) for name in unsupported):
        raise RuntimeError("Custom compiler/verifier arguments are not supported by the development recorder")
    environment["CARGO_TERM_COLOR"] = "never"
    environment["CORDIS_VERUS_THREADS"] = "2"
    if offline:
        environment["CARGO_NET_OFFLINE"] = "true"
    return environment


def record_locked(record, offline, log):
    """Called with the global lease held through final validation and recording."""
    try:
        save_record(record)
        before = source_hashes()
        workflow = workflow_binding(before)
        environment = environment_for(offline)
        packages_path = ROOT / "target/release-artifacts/package-report.json"
        packages_path.unlink(missing_ok=True)
        print("Running development checks", flush=True)
        returncode = run_checks(record["command"], environment, log)
        if returncode:
            raise RuntimeError(f"Development checks exited {returncode}; see {record['log']}")
        proof, tests = parse_results(log.read_text())
        # A previous package report is removed before invoking the fixed workflow.
        packages = json.loads(packages_path.read_text())
        if source_hashes() != before:
            raise RuntimeError("Sources changed during checks; rerun before recording success")
        record.update(status="passed", checkedAt=datetime.now(timezone.utc).isoformat(),
                      host={"os": platform.system(), "architecture": platform.machine()},
                      proof=proof, tests=tests, packages=packages,
                      examples=sorted(p.stem for p in (ROOT / "crates/cordis/examples").glob("*.rs")),
                      logSha256=hashlib.sha256(log.read_bytes()).hexdigest(), sha256=before,
                      workflowSha256=workflow)
        save_record(record)
        print(f"Recorded development checks: {proof['verified']} proofs; {tests['total']} tests; "
              f"{tests['doctestTotal']} doctests. Full release acceptance remains separate.")
        return record
    except BaseException as error:
        save_record(failed_record(record, error))
        raise


def record_development(offline=False):
    command = ["./scripts/check-development.sh", *(["--offline"] if offline else [])]
    record = {"schema": SCHEMA, "status": "running", "releaseAcceptance": False,
              "fullNegativeControls": "not run by this command", "paperCompletion": False,
              "command": command, "log": "target/development/checks.log", "sha256": {}}
    started = False
    with termination_signals():
        try:
            # Invalidate stale success before hashing or preparing output paths.
            save_record(record)
            output = ROOT / "target/development"
            output.mkdir(parents=True, exist_ok=True)
            print("Waiting for local verifier lease; log: target/development/checks.log", flush=True)
            with verifier_lease():
                started = True
                return record_locked(record, offline, output / "checks.log")
        except BaseException as error:
            if not started:
                save_record(failed_record(record, error))
            raise


def check_record():
    before = source_hashes()
    record = json.loads(RECORD.read_text())
    if (record.get("schema") != SCHEMA or record.get("status") != "passed" or record.get("sha256") != before
            or record.get("releaseAcceptance") is not False or record.get("paperCompletion") is not False
            or record.get("fullNegativeControls") != "not run by this command"
            or record.get("command") not in (["./scripts/check-development.sh"], ["./scripts/check-development.sh", "--offline"])
            or record.get("workflowSha256") != workflow_binding(before)):
        raise RuntimeError("Missing, failed, or stale development record; run fresh checks")
    print(f"Development record matches {len(before)} files. Hash check only; no new proofs executed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true")
    parser.add_argument("--check", action="store_true", help="Check recorded hashes only, without running checks")
    args = parser.parse_args()
    if args.check:
        check_record()
    else:
        record_development(args.offline)


if __name__ == "__main__":
    main()
