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
NODE_BEGIN = "BEGIN NODE COMPATIBILITY TESTS"
NODE_END = "END NODE COMPATIBILITY TESTS"
VERIFIER_LOCK = Path("/tmp/cordis-local-verifier.lock")
FIXED_SCRIPTS = (
    "scripts/record-development.py", "scripts/check-development.sh",
    "scripts/record-verification.py", "scripts/check-paper-coverage.py",
    "scripts/verify.sh", "scripts/toolchain-env.sh", "scripts/install-verus.py",
    "scripts/package-check.py", "scripts/build-node.mjs", "scripts/build-node.sh",
    "scripts/check-npm-package.mjs", "scripts/sync-profile-types.mjs",
    "scripts/write-native-manifest.mjs", "scripts/package-native.mjs",
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
    counts["nodeCompatibility"] = parse_node_tests(lines, end)
    return {"verified": int(proofs[0][0]), "errors": 0, "wholeCrate": True,
            "compiled": True, "noCheating": True}, counts


def parse_node_tests(lines, workspace_end):
    if lines.count(NODE_BEGIN) != 1 or lines.count(NODE_END) != 1:
        raise RuntimeError("Missing or ambiguous Node compatibility test section")
    start, end = lines.index(NODE_BEGIN), lines.index(NODE_END)
    if not workspace_end < start < end < len(lines) - 1:
        raise RuntimeError("Node compatibility check sections are out of order")
    section = "\n".join(lines[start + 1:end])
    counts = {}
    for name in ("tests", "pass", "fail", "cancelled", "skipped", "todo"):
        matches = re.findall(r"^# " + name + r" (\d+)$", section, re.M)
        if len(matches) != 1:
            raise RuntimeError("Missing or ambiguous Node test summary: " + name)
        counts[name] = int(matches[0])
    if (counts["tests"] <= 0 or counts["pass"] != counts["tests"]
            or any(counts[name] for name in ("fail", "cancelled", "skipped", "todo"))
            or re.search(r"^\s*not ok\b|^Bail out!", section, re.M)):
        raise RuntimeError("Node compatibility tests failed, skipped, or incomplete")
    return {**counts, "behavioralTestsOnly": True, "upstreamDifferentialIncluded": False}


def node_build_evidence(path):
    build = json.loads(path.read_text())
    if build.get("schema") != "cordis-verus.node-build/v1":
        raise RuntimeError("Missing or unsupported Node build evidence")
    native_directory = ROOT / "packages/compat-cordis/native"
    manifest = json.loads((native_directory / "manifest.json").read_text())
    entries = manifest.get("artifacts", [])
    selected = [entry for entry in entries if isinstance(entry, dict)
                and entry.get("sha256") == build.get("artifactSha256")
                and entry.get("platform") == build.get("platform")
                and entry.get("architecture") == build.get("architecture")]
    if manifest.get("schema") != "cordis-verus.native-manifest/v1" or len(selected) != 1:
        raise RuntimeError("Node build evidence does not select exactly one native artifact")
    name = selected[0].get("file")
    if (not isinstance(name, str) or "\\" in name or name.startswith("/")
            or any(part in {"", ".", ".."} for part in name.split("/"))):
        raise RuntimeError("Node build evidence has an unsafe native artifact path")
    files = {"artifactSha256": "packages/compat-cordis/native/" + name,
             "cargoLockSha256": "Cargo.lock", "toolchainLockSha256": "toolchain.lock.json"}
    if any(build.get(key) != hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
           for key, name in files.items()):
        raise RuntimeError("Node build evidence does not match the native artifact and locks")
    if not all(isinstance(build.get(name), str) and build[name] for name in ("platform", "architecture", "node")):
        raise RuntimeError("Incomplete Node build environment evidence")
    # The generic SDK is exercised through a separately compiled addon. A
    # passing facade build is not evidence that this local test binary is fresh.
    fixture = build.get("interopFixture")
    fixture_path = "target/node-compat/interop-fixture.node"
    if (not isinstance(fixture, dict) or fixture.get("path") != fixture_path
            or fixture.get("sha256") != file_sha256(ROOT / fixture_path)):
        raise RuntimeError("Rust interop fixture evidence is missing or stale")
    if build.get("sourceHashes") != native_source_hashes():
        raise RuntimeError("Node build evidence has stale or incomplete native source hashes")
    return build


NPM_PACKAGES = {
    "compat-cordis": "@cordis-verus/compat-cordis",
    "compat-loader": "@cordis-verus/compat-loader",
    "compat-harness": "@cordis-verus/compat-harness",
}


def file_sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def distribution_inputs(names, directories, suffixes=None):
    paths = [ROOT / name for name in names]
    for name in directories:
        directory = ROOT / name
        if not directory.is_dir():
            raise RuntimeError("Missing distribution source directory: " + name)
        for parent, dirs, files in os.walk(directory):
            dirs[:] = [name for name in dirs if name not in {"node_modules", ".git", "target"}]
            if any((Path(parent) / name).is_symlink() for name in [*dirs, *files]):
                raise RuntimeError("Unexpected distribution source symlink")
            paths.extend(Path(parent) / name for name in files
                         if suffixes is None or Path(name).suffix in suffixes)
    return {path.relative_to(ROOT).as_posix(): file_sha256(path) for path in sorted(paths)}


def npm_source_hashes():
    return distribution_inputs(
        ["package.json", "package-lock.json", "LICENSE", "NOTICE", "scripts/check-npm-package.mjs"],
        ["packages/" + name for name in NPM_PACKAGES])


def native_source_hashes():
    return distribution_inputs(
        ["Cargo.toml", "Cargo.lock", "toolchain.lock.json", "scripts/build-node.sh",
         "scripts/build-node.mjs", "scripts/toolchain-env.sh", "scripts/write-native-manifest.mjs",
         "packages/compat-cordis/native-artifacts.js", "packages/compat-cordis/package.json"],
        ["crates/" + name for name in ("cordis-kernel", "cordis-driver", "cordis", "cordis-node")],
        {".rs", ".toml"})


def npm_distribution_evidence(path, build_path, node_build):
    """Validate fresh local artifacts; this function never invokes Node or npm."""
    report = json.loads(path.read_text())
    if (report.get("schema") != "cordis-verus.npm-package/v1" or report.get("status") != "passed"
            or report.get("offline") is not True or report.get("uploaded") is not False
            or report.get("registryPublishChecked") is not False
            or report.get("otherTargets") != "not validated"):
        raise RuntimeError("Missing or unsupported npm distribution evidence")
    target = report.get("testedTarget", {})
    host_platform = {"Darwin": "darwin", "Linux": "linux", "Windows": "win32"}.get(platform.system())
    host_arch = {"aarch64": "arm64", "arm64": "arm64", "x86_64": "x64", "AMD64": "x64"}.get(platform.machine())
    if (target.get("platform") != host_platform or target.get("architecture") != host_arch
            or any(target.get(name) != node_build.get(name)
                   for name in ("platform", "architecture", "node"))
            or not re.fullmatch(r"[1-9][0-9]*", str(target.get("nodeApi", "")))
            or not re.fullmatch(r"[1-9][0-9]*", str(target.get("nodeModuleAbi", "")))
            or type(target.get("driverAbi")) is not int or target["driverAbi"] <= 0):
        raise RuntimeError("npm distribution target does not match the current native build host")
    if (report.get("buildReportSha256") != file_sha256(build_path)
            or report.get("nativeArtifactSha256") != node_build.get("artifactSha256")
            or report.get("nativeSourceHashes") != node_build.get("sourceHashes")
            or report.get("nativeSourceHashes") != native_source_hashes()
            or report.get("sourceHashes") != npm_source_hashes()):
        raise RuntimeError("npm distribution input hashes are stale or incomplete")
    native_directory = ROOT / "packages/compat-cordis/native"
    manifest_path = native_directory / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    if (manifest.get("schema") != "cordis-verus.native-manifest/v1"
            or report.get("nativeManifestSha256") != file_sha256(manifest_path)
            or not isinstance(manifest.get("artifacts"), list)):
        raise RuntimeError("npm distribution native manifest is missing or stale")
    artifacts = manifest["artifacts"]
    selected = [entry for entry in artifacts if entry.get("target") == report.get("nativeTarget")]
    if (len(selected) != 1 or selected[0].get("sha256") != node_build["artifactSha256"]
            or selected[0].get("platform") != target["platform"]
            or selected[0].get("architecture") != target["architecture"]):
        raise RuntimeError("npm distribution native selection does not match the tested host")
    native_files = {"native/manifest.json"}
    native_binaries = set()
    for entry in artifacts:
        for field, hash_field in (("file", "sha256"), ("provenance", "provenanceSha256")):
            name = entry.get(field)
            if (not isinstance(name, str) or "\\" in name or name.startswith("/")
                    or any(part in {"", ".", ".."} for part in name.split("/"))
                    or entry.get(hash_field) != file_sha256(native_directory / name)):
                raise RuntimeError("npm distribution native artifact changed or has unsafe path")
            native_files.add("native/" + name)
            if field == "file":
                native_binaries.add("native/" + name)
        provenance = json.loads((native_directory / entry["provenance"]).read_text())
        if (entry is selected[0] and (provenance.get("build", {}).get("reportSha256") != file_sha256(build_path)
                or provenance.get("build", {}).get("sourceHashes") != node_build["sourceHashes"])):
            raise RuntimeError("npm distribution native provenance changed")
    packages = report.get("packages", [])
    if (not isinstance(packages, list) or len(packages) != len(NPM_PACKAGES)
            or any(not isinstance(item, dict) for item in packages)
            or {item.get("name") for item in packages} != set(NPM_PACKAGES.values())):
        raise RuntimeError("npm distribution must validate all three expected packages")
    manifests = {name: json.loads((ROOT / "packages" / directory / "package.json").read_text())
                 for directory, name in NPM_PACKAGES.items()}
    required = {"package.json", "index.js", "index.d.ts", "README.md", "LICENSE", "NOTICE"}
    for item in packages:
        filename = item.get("filename", "")
        files = item.get("files", [])
        if (not isinstance(filename, str) or not re.fullmatch(r"[A-Za-z0-9_.-]+\.tgz", filename)
                or item.get("version") != manifests[item["name"]].get("version")
                or not isinstance(files, list) or any(not isinstance(name, str) for name in files)
                or not required.issubset(files)
                or (item["name"] == NPM_PACKAGES["compat-loader"]
                    and not {"harness.js", "harness.d.ts", "module-graph.js"}.issubset(files))
                or (item["name"] == NPM_PACKAGES["compat-cordis"] and (not native_files.issubset(files)
                    or {name for name in files if name.endswith(".node")} != native_binaries))
                or item.get("sha256") != file_sha256(path.parent / filename)):
            raise RuntimeError("npm distribution package artifact is missing or changed")
    observation = report.get("observation", {})
    harness = report.get("harnessObservation", {})
    if (observation.get("binding", {}).get("abi") != target["driverAbi"]
            or observation.get("nativeManifestSha256") != report["nativeManifestSha256"]
            or observation.get("nativeTarget") != report["nativeTarget"]
            or set(observation.get("tests", [])) != {
                "native-manifest-selection", "default-core-only", "packed-native-load", "ESM-CJS-identity", "original-cordis-import", "JSON-loader-update", "Worker-artifact-load"}
            or harness.get("profile") != "harness"
            or set(harness.get("tests", [])) != {
                "scoped-original-import", "ESM-CJS-profile-identity", "native-harness-domain", "Service-class", "official-loader-adapter-export"}):
        raise RuntimeError("npm distribution smoke evidence is incomplete")
    return report


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
              if key not in {"checkedAt", "host", "proof", "tests", "packages", "examples", "logSha256", "workflowSha256", "nodeBuild", "npmDistribution", "npmDistributionReportSha256"}}
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
        node_build_path = ROOT / "target/node-compat/build.json"
        node_build_path.unlink(missing_ok=True)
        npm_path = ROOT / "target/release-artifacts/npm/package-report.json"
        npm_path.unlink(missing_ok=True)
        print("Running development checks", flush=True)
        returncode = run_checks(record["command"], environment, log)
        if returncode:
            raise RuntimeError(f"Development checks exited {returncode}; see {record['log']}")
        proof, tests = parse_results(log.read_text())
        # A previous package report is removed before invoking the fixed workflow.
        packages = json.loads(packages_path.read_text())
        node_build = node_build_evidence(node_build_path)
        npm_distribution = npm_distribution_evidence(npm_path, node_build_path, node_build)
        if source_hashes() != before:
            raise RuntimeError("Sources changed during checks; rerun before recording success")
        record.update(status="passed", checkedAt=datetime.now(timezone.utc).isoformat(),
                      host={"os": platform.system(), "architecture": platform.machine()},
                      proof=proof, tests=tests, packages=packages, nodeBuild=node_build,
                      npmDistribution=npm_distribution, npmDistributionReportSha256=file_sha256(npm_path),
                      examples=sorted(p.stem for p in (ROOT / "crates/cordis/examples").glob("*.rs")),
                      logSha256=hashlib.sha256(log.read_bytes()).hexdigest(), sha256=before,
                      workflowSha256=workflow)
        save_record(record)
        print(f"Recorded development checks: {proof['verified']} proofs; {tests['total']} tests; "
              f"{tests['doctestTotal']} doctests; {tests['nodeCompatibility']['tests']} Node behavioral tests. Full release acceptance remains separate.")
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
            or record.get("workflowSha256") != workflow_binding(before)
            or record.get("tests", {}).get("nodeCompatibility", {}).get("behavioralTestsOnly") is not True
            or record.get("nodeBuild", {}).get("schema") != "cordis-verus.node-build/v1"):
        raise RuntimeError("Missing, failed, or stale development record; run fresh checks")
    npm_path = ROOT / "target/release-artifacts/npm/package-report.json"
    build_path = ROOT / "target/node-compat/build.json"
    build = node_build_evidence(build_path)
    npm = npm_distribution_evidence(npm_path, build_path, build)
    if (record.get("nodeBuild") != build or record.get("npmDistribution") != npm
            or record.get("npmDistributionReportSha256") != file_sha256(npm_path)):
        raise RuntimeError("Missing, failed, or stale development npm distribution record")
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
