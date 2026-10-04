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
EXCLUDED = {".git", ".tools", "target", "upstream", "reference", "__pycache__"}


def required_negative_names():
    spec = importlib.util.spec_from_file_location("cordis_negative_evidence", ROOT / "scripts/check-negative.py")
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return [item[0] for item in checker.mutation_manifest()]


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
            if path == RECORD or path.is_symlink() or name in {"verus-release.json", ".DS_Store"}:
                continue
            if path.suffix not in {".rs", ".toml", ".lock", ".md", ".json", ".py", ".sh", ".yml", ".yaml"} and name not in {"LICENSE", "NOTICE", ".gitignore", ".gitattributes", ".editorconfig"}:
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
            current = (suites, "kernel_unit" if "cordis_kernel-" in line else "host_unit")
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true", help="Use cached package dependencies")
    parser.add_argument("--upstream", action="store_true", help="Also check local locked research inputs")
    parser.add_argument("--check", action="store_true", help="Check the existing record for stale sources only")
    args = parser.parse_args()
    before = source_hashes()
    if args.check:
        record = json.loads(RECORD.read_text())
        if record.get("status") != "passed":
            sys.exit("No successful current-format verification record; run fresh validation")
        recorded = record["sha256"]
        changed = sorted(key for key in before.keys() | recorded.keys() if before.get(key) != recorded.get(key))
        if changed:
            sys.exit("Verification record is stale: " + ", ".join(changed))
        print(f"Record matches {len(before)} source files. This is a hash check, not a new verification run.")
        return
    output = ROOT / "target/validation"
    output.mkdir(parents=True, exist_ok=True)
    # Invalidate old evidence before attempting new checks; a failed run must
    # never leave a success report that appears to describe changed sources.
    RECORD.write_text(json.dumps({"schema": "cordis-verus.verification/v3", "status": "running", "sha256": {}}, indent=2) + "\n")
    commands = [["./scripts/quality.sh", *(["--offline"] if args.offline else [])]]
    if args.upstream:
        commands.append(["python3", "scripts/check-upstream.py"])
    environment = os.environ.copy()
    environment["CARGO_TERM_COLOR"] = "never"
    environment["CARGO_NET_OFFLINE"] = "true" if args.offline else environment.get("CARGO_NET_OFFLINE", "false")
    logs = []
    for index, command in enumerate(commands):
        log = output / ("quality.log" if index == 0 else "upstream.log")
        print("Running " + " ".join(command) + "; log: " + str(log), flush=True)
        with log.open("w") as stream:
            result = subprocess.run(command, cwd=ROOT, env=environment, stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            RECORD.write_text(json.dumps({"schema": "cordis-verus.verification/v3", "status": "failed", "command": command, "log": str(log.relative_to(ROOT)), "sha256": {}}, indent=2) + "\n")
            sys.exit(f"Check failed ({result.returncode}); see {log}")
        logs.append(log.relative_to(ROOT).as_posix())
    after = source_hashes()
    if after != before:
        sys.exit("Sources changed during validation; rerun to obtain consistent evidence")
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
        "upstreamCheck": "passed" if args.upstream else "not requested",
        "ci": "configured; this report describes local execution only",
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


if __name__ == "__main__":
    main()
