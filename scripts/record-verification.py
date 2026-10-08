#!/usr/bin/env python3
"""Run fresh release-quality checks and record their evidence and source hashes.

--check only detects stale/missing files in an existing record. It does not
substitute for executing proofs or tests. No network publication is performed.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / "docs/verification-report.json"
SCHEMA = "cordis-verus.verification/v3"
SHARDS_ENV = "CORDIS_FULL_NEGATIVE_SHARDS"
EXCLUDED = {".git", ".tools", "target", "upstream", "reference", "__pycache__", "node_modules"}


def helper(filename, name):
    path = ROOT / "scripts" / filename
    original = path.read_bytes()
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    exec(compile(original, str(path), "exec"), module.__dict__)
    if path.read_bytes() != original:
        raise RuntimeError("Validation helper changed while loading: " + filename)
    return module


def required_negative_names():
    return [item[0] for item in helper("check-negative.py", "release_negative_checks").mutation_manifest()]


def execution_helpers():
    # This module defines its release-helper imports lazily. Loading only the
    # process/lease helpers here does not recurse into record-verification.py.
    return helper("record-development.py", "release_execution_helpers")


def run_checks(command, environment, log):
    checks = helper("check-negative.py", "release_process_supervisor")
    # The full negative runner owns its own subprocess groups. Give its signal
    # handler time to stop those groups before forcibly stopping the outer job.
    with checks.ProcessSupervisor(terminate_grace=3).signal_handlers() as supervisor, log.open("w") as stream:
        process = supervisor.start(command, cwd=ROOT, env=environment, stdout=stream,
                                   stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
        completed = False
        try:
            while True:
                supervisor.check()
                try:
                    process.wait(timeout=0.1)
                    break
                except subprocess.TimeoutExpired:
                    continue
            supervisor.check()
            completed = True
        finally:
            supervisor.finish(process, terminate=not completed)
    # Restore the enclosing signal handler before the last cancellation check:
    # a signal received during finish must not turn into a successful exit.
    supervisor.check()
    return process.returncode


def environment_for(offline=False, negative_shards=None):
    environment = os.environ.copy()
    unsupported = ("VERUS_Z3_PATH", "VERUS_EXTRA_ARGS", "RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER")
    if any(environment.get(name) for name in unsupported):
        raise RuntimeError("Custom compiler/verifier overrides are not supported by the release recorder")
    # Ambient configuration must never turn the default local gate into a
    # collected-evidence run. Only the explicit recorder option selects it.
    environment.pop(SHARDS_ENV, None)
    if negative_shards is not None:
        directory = Path(negative_shards).resolve(strict=True)
        if not directory.is_dir():
            raise RuntimeError("Full negative shards input must be a directory")
        environment[SHARDS_ENV] = str(directory)
    environment["CARGO_TERM_COLOR"] = "never"
    environment["CORDIS_VERUS_THREADS"] = "2"
    environment["CARGO_NET_OFFLINE"] = "true" if offline else environment.get("CARGO_NET_OFFLINE", "false")
    return environment


def validate_negative_report(proof, expected_names):
    """A release record must contain every current control in canonical order."""
    if not expected_names or len(set(expected_names)) != len(expected_names):
        raise RuntimeError("Negative-control manifest is empty or has duplicate names")
    baseline = proof.get("baseline", {})
    if (baseline.get("success") is not True or type(baseline.get("errors")) is not int or baseline["errors"] != 0
            or type(baseline.get("verified")) is not int or baseline["verified"] <= 0
            or baseline.get("encountered-vir-error") is not False
            or baseline.get("is-verifying-entire-crate") is not True):
        raise RuntimeError("Full-crate positive proof evidence is incomplete")
    mutations = proof.get("mutations", [])
    if [item.get("name") for item in mutations] != expected_names:
        raise RuntimeError("Negative controls differ from the current ordered manifest")
    for item in mutations:
        result = item.get("verification-results", {})
        if (item.get("compiles") is not True or result.get("success") is not False
                or result.get("encountered-vir-error") is not False
                or result.get("is-verifying-entire-crate") is not True
                or type(result.get("verified")) is not int or result["verified"] <= 0
                or type(result.get("errors")) is not int or result["errors"] <= 0):
            raise RuntimeError("Incomplete negative proof evidence: " + item["name"])


def source_hashes():
    result = {}
    for directory, dirs, files in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in EXCLUDED and not (Path(directory) / d).is_symlink()]
        for name in files:
            path = Path(directory) / name
            rel = path.relative_to(ROOT).as_posix()
            if (path == RECORD or path.is_symlink() or name in {"verus-release.json", ".DS_Store"}
                    or rel.startswith("packages/compat-cordis/native/")):
                continue
            if path.suffix not in {".rs", ".toml", ".lock", ".md", ".json", ".py", ".sh", ".yml", ".yaml", ".js", ".mjs", ".cjs", ".ts", ".tsx"} and name not in {"LICENSE", "LICENSE.upstream", "NOTICE", ".gitignore", ".gitattributes", ".editorconfig"}:
                continue
            result[rel] = hashlib.sha256(path.read_bytes()).hexdigest()
    return dict(sorted(result.items()))


def test_counts(log):
    suites, doctests = {}, {}
    current = None
    for line in log.splitlines():
        # The extracted-package checks repeat suites; the main workspace run is
        # before the negative controls. Record its numbers only.
        if "OK unmodified kernel:" in line:
            break
        match = re.search(r"Running tests/(\w+)\.rs", line)
        if match:
            current = (suites, "kernel" if match[1] == "lifecycle" else match[1])
        elif "Running unittests src/lib.rs" in line:
            crate_match = re.search(r"/(cordis(?:_[a-z]+)*)-[0-9a-f]+", line)
            crate = crate_match[1] if crate_match else "cordis"
            label = {"cordis_kernel": "kernel_unit", "cordis": "host_unit"}.get(crate, crate + "_unit")
            current = (suites, label)
        elif "Doc-tests " in line:
            current = (doctests, line.split("Doc-tests ", 1)[1].strip())
        match = re.search(r"test result: ok\. (\d+) passed; 0 failed;", line)
        if match and current:
            current[0][current[1]] = int(match[1])
            current = None
    if not suites or not sum(suites.values()):
        raise RuntimeError("No successful workspace test suites found")
    return {"suites": suites, "total": sum(suites.values()), "doctests": doctests,
            "doctestTotal": sum(doctests.values()), "deterministicTraces": 8232}


def record_release(offline=False, upstream=False, negative_shards=None):
    # Invalidate previous success before waiting for the verifier lease or
    # preparing new evidence. A failed invocation cannot reuse old negatives.
    RECORD.parent.mkdir(parents=True, exist_ok=True)
    state = {"schema": SCHEMA, "status": "running", "sha256": {}}
    RECORD.write_text(json.dumps(state, indent=2) + "\n")
    try:
        runtime = execution_helpers()
        with runtime.termination_signals(), runtime.verifier_lease():
            return record_locked(offline, upstream, negative_shards)
    except BaseException as error:
        RECORD.write_text(json.dumps({"schema": SCHEMA, "status": "failed",
                                     "failure": f"{type(error).__name__}: {error}", "sha256": {}}, indent=2) + "\n")
        raise


def record_locked(offline, upstream, negative_shards):
    (ROOT / "target/proof-negative/report.json").unlink(missing_ok=True)
    (ROOT / "target/release-artifacts/package-report.json").unlink(missing_ok=True)
    before = source_hashes()
    output = ROOT / "target/validation"
    output.mkdir(parents=True, exist_ok=True)
    commands = [["./scripts/quality.sh", *(["--offline"] if offline else [])]]
    if upstream:
        commands.append(["python3", "scripts/check-upstream.py"])
    environment = environment_for(offline, negative_shards)
    logs = []
    for index, command in enumerate(commands):
        log = output / ("quality.log" if index == 0 else "upstream.log")
        print("Running " + " ".join(command) + "; log: " + str(log), flush=True)
        returncode = run_checks(command, environment, log)
        if returncode:
            raise RuntimeError(f"Check failed ({returncode}); see {log}")
        logs.append(log.relative_to(ROOT).as_posix())
    after = source_hashes()
    if after != before:
        raise RuntimeError("Sources changed during validation; rerun to obtain consistent evidence")
    proof = json.loads((ROOT / "target/proof-negative/report.json").read_text())
    packages = json.loads((ROOT / "target/release-artifacts/package-report.json").read_text())
    validate_negative_report(proof, required_negative_names())
    report = {
        "schema": "cordis-verus.verification/v3", "status": "passed",
        "checkedAt": datetime.now(timezone.utc).isoformat(),
        "host": {"os": platform.system(), "architecture": platform.machine()},
        "verus": proof["verus"], "proof": proof["baseline"],
        "tests": test_counts((output / "quality.log").read_text()),
        "negativeControls": proof["mutations"],
        "negativeExecution": proof.get("execution", {"jobs": 1}),
        "examples": sorted(p.stem for p in (ROOT / "crates/cordis/examples").glob("*.rs")),
        "packages": packages,
        "upstreamCheck": "passed" if upstream else "not requested",
        "ci": ("GitHub Actions; this report describes the current workflow run"
               if os.environ.get("GITHUB_ACTIONS") == "true"
               else "local execution; GitHub Actions was not used for this record"),
        "commands": commands, "logs": logs,
        "paperCoverage": {
            "ledger": "docs/paper-obligations.json",
            "numberedItems": 81,
            "completionClaimed": False,
            "gate": "python3 scripts/check-paper-coverage.py --require-complete",
        },
        "proofBoundary": "Verified executable Kernel/resource protocols and fixed closed-program drivers construct actual source histories with authentic journals, fresh allocation, single-admission landing Divert and first-error atomicity. Actions execute synchronously at landing; arbitrary callbacks and Future internals are outside this simulation. Effect laws include observational witnesses, iterator bisimulation and actual-inverse permutation recovery. The actual dependent least grammar derives strict monoid and continuation independence for arbitrary unrelated index and outcome types from primitive/key laws; this is not the unguarded total-domain statement. Conditional dependent/child nine-rule interpretations establish typed successful-prefix safety, receipt provenance, retention and lifecycle/provider ordering. Function-valued field simulation permits different roots, continuations and accumulator lengths under a total table-only primitive profile. A separate strict partial refinement uses the actual arbitrary-index mixed run/restore functions and a legal-input PER with equal controls; for Table instructions it constructs all nine target rules and whole finite traces, preserving None/Some domains. Least grammar self/alias witnesses and PER algebra are checked; this relation is stronger than original pure table observation and does not cover the full Child quotient. Guarded exchanges and finite suffix transport support normalization and joinability of descendants of one trace, not arbitrary-schedule confluence. Constructive deletion profiles cover isolated owners and fixed-registry shared-key owners with separated private provisions, authentic compressed receipts and new foreign Unload. An actual-state induction unifies all Table landings, new foreign Provision and arbitrary-age/position foreign Table Unloads; its landing catalogue supplies provenance only. Real guard/domain proofs construct the full target execution and final owner recovery from empty-origin history. Dynamic foreign Insert/Remove now compose in the same Table induction; each inserted dependency avoids private owner provisions, original source guards derive target legality, and removed actors retain authentic historical inputs/receipts. An arbitrary-carrier/index outside-frame theorem lifts total and strict partial local function, inverse and continuation relations to all keys and supplies the existing Model field API. Definition 23 has both abstract location-heap realizations, including actual in-place inverse versus separate derived discard. Definitions48/58 now have conditional arbitrary-carrier component and full function-field/execution interfaces, retaining least strong witnesses, actual total accumulators and finite/infinite episodes. They do not construct recursive Gamma or establish actual strict-program membership. Definition52 now has a conditional typed local-editor interpretation with the full Component gate, actual fresh-name continuation and same-child strict retirement. Per-key value fibers constrain all input projections. Definition55 separately records literal and symmetric read interpretations; recursive Gamma and the total lift remain explicit obligations. Definition 63 is separated from the stronger implementation invariant; component completion totality is separated from a current-state Active-table check. The exact six-field configuration entry is formalized with verified edit frames; the host leaf projection requires an explicit module URL resolver. Original Unit counterexamples, model-scoped Child obstructions and unrestricted recursive-context representation issues remain explicit. Foreign Child landings and arbitrary-age mixed Table/Child journals now compose with dynamic deletion, with actual target restore domains, compressed tokens and final owner recovery derived. Owner Child, owner consumers, internal owner Unload, dynamic canonical form, strict-partial versus full-context alignment and arbitrary async host refinement remain open. See the 81-item ledger and module contracts for exact premises. Passing quality checks does not establish paper-wide completion.",
        "sha256": before,
    }
    RECORD.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(f"Recorded {report['proof']['verified']} verified / 0 errors; {report['tests']['total']} tests; {report['tests']['doctestTotal']} doctests; {len(before)} source hashes.")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true", help="Use cached package dependencies")
    parser.add_argument("--upstream", action="store_true", help="Also check local locked research inputs")
    parser.add_argument("--check", action="store_true", help="Check the existing record for stale sources only")
    parser.add_argument("--negative-shards", type=Path,
                        help="Collect all complete-crate negative shards from this directory; default runs every control locally")
    args = parser.parse_args()
    if args.check and args.negative_shards is not None:
        parser.error("--negative-shards requires a new release validation run, not --check")
    if args.check:
        before = source_hashes()
        record = json.loads(RECORD.read_text())
        if record.get("schema") != SCHEMA or record.get("status") != "passed":
            sys.exit("No successful current-format verification record; run fresh validation")
        recorded = record["sha256"]
        changed = sorted(key for key in before.keys() | recorded.keys() if before.get(key) != recorded.get(key))
        if changed:
            sys.exit("Verification record is stale: " + ", ".join(changed))
        print(f"Record matches {len(before)} source files. This is a hash check, not a new verification run.")
        return
    record_release(args.offline, args.upstream, args.negative_shards)


if __name__ == "__main__":
    main()
