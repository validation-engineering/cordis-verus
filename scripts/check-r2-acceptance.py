#!/usr/bin/env python3
"""Frozen R2 profile acceptance: development, two real paths and strict selected mutations.

This is not release acceptance, full negative regression or paper-wide completion.
Reports live under ignored target/. --check revalidates evidence without running proofs.
"""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "target/r2-acceptance"
SCHEMA = "cordis-verus.r2-acceptance/v1"
PROFILE = "managed-production/v1"
NODE_CASE = "R2 acceptance: dynamic publication, retained object, failed cleanup and stale retry"
NATIVE_RESULT = {"stages": ["loaded", "blocked", "retained", "drained", "recovered", "updated", "saved", "released"],
                 "initial": 10, "updated": 15, "restored": 10}
CASES = (
    "r2-issued-confirms-before-restore", "r2-issued-reuses-real-attempt",
    "r2-host-object-substitution", "r2-host-dispatch-ignores-ticket",
    "r2-managed-return-omits-effects", "r2-managed-drops-continuation",
    "r2-config-roundtrip-accepts-changed-tree", "r2-config-skips-default",
    "r2-native-confuses-control-stutter", "r2-node-confuses-control-stutter",
    "r2-host-finishes-pending-claim", "r2-config-substitutes-insert-origin",
)

def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def module(name, filename):
    path = ROOT / "scripts" / filename
    code = path.read_bytes()
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    exec(compile(code, str(path), "exec"), value.__dict__)
    require(path.read_bytes() == code, "helper changed while loading")
    return value


def review():
    checker = module("r2_plan", "check-paper-refinement.py")
    plan = json.loads((ROOT / checker.PLAN).read_text())
    ledger = json.loads((ROOT / checker.LEDGER).read_text())
    checker.validate(plan, ledger)
    scope = plan["r2Acceptance"]
    require(scope["profile"] == PROFILE and scope["originalPaperEquivalent"] is False,
            "R2 acceptance requires its explicit interpretation")
    require(scope["selectedNegativeControls"] == list(CASES), "R2 mutation selection changed")
    require(plan["milestones"][2]["status"] == "complete", "R2 semantic review is incomplete")
    return scope


def runtime_evidence(log):
    native = re.findall(r"^R2_NATIVE_ACCEPTANCE (.+)$", log, re.M)
    require(len(native) == 1 and json.loads(native[0]) == NATIVE_RESULT,
            "missing or incomplete native production scenario")
    node = re.findall(r"^ok [0-9]+ - " + re.escape(NODE_CASE) + r"(?:\r)?$", log, re.M)
    require(len(node) == 1, "missing passing Node production scenario")
    return {"native": NATIVE_RESULT, "node": NODE_CASE}


def selection(h):
    manifest = json.loads((ROOT / "scripts/negative-controls.scoped.candidate.json").read_text())
    h.validate_manifest(manifest)
    h.validate_canonical_cases(manifest, ROOT)
    h.preflight(manifest, ROOT / "crates/cordis-kernel/src")
    indexed = {case["name"]: case for case in manifest["cases"]}
    return [indexed[name] for name in CASES]


def save(report, directory=OUTPUT):
    directory.mkdir(parents=True, exist_ok=True)
    temporary = directory / "report.json.tmp"
    temporary.write_text(json.dumps(report, indent=2) + "\n")
    temporary.replace(directory / "report.json")


def check_development(dev, h, expected=None):
    dev.check_record()
    record = json.loads(dev.RECORD.read_text())
    log_path = ROOT / record["log"]
    require(h.digest(log_path) == record["logSha256"], "development log changed")
    proof, tests = dev.parse_results(log_path.read_text())
    require(proof == record["proof"] and tests == record["tests"], "development results changed")
    require("r2_production" in record["examples"], "production example was not included")
    evidence = {"recordSha256": h.digest(dev.RECORD), "logSha256": record["logSha256"],
                "proof": proof, "runtime": runtime_evidence(log_path.read_text())}
    if expected is not None:
        require(evidence == expected, "development evidence no longer matches R2 acceptance")
    return evidence


def validate_cases(report, cases, h, directory):
    require([row["name"] for row in report["cases"]] == list(CASES), "missing or reordered R2 mutations")
    source = directory / "baseline"
    require(h.source_hashes(source) == report["kernelSha256"], "baseline source changed")
    h.verify_tool_artifacts(report["tool"])
    for row, case in zip(report["cases"], cases):
        require(row["status"] == "passed" and row["case"] == case, "incomplete or changed mutation")
        mutated = directory / case["name"]
        require(h.source_hashes(mutated) == row["mutatedSourceSha256"], "mutant changed")
        for name, kind, tree in (("positive", "selected", source), ("compile", "compile", mutated), ("negative", "selected", mutated)):
            artifact = directory / (case["name"] + "-compile.rlib")
            command = h.command(report["tool"]["binary"], tree, kind,
                                case["targets"] if kind == "selected" else (), 2, artifact,
                                expected_failures=case["expectedFailures"] if kind == "selected" else ())
            require(row[name]["command"] == command, "mutation invocation changed")
        h.validate_positive(row["positive"], directory, entire=False, expected_tool=report["tool"],
                            targets=case["targets"], expected_failures=case["expectedFailures"])
        artifact = directory / (case["name"] + "-compile.rlib")
        require(row["compile"].get("artifactSha256") == h.digest(artifact)
                and row["compile"].get("artifactBytes") == artifact.stat().st_size, "compiled artifact changed")
        h.validate_compile(row["compile"], directory, artifact)
        h.validate_rejection(row["negative"], directory, case, mutated, report["tool"])
        # Bind the complete mutated tree to exactly the canonical single edit.
        expected = dict(report["kernelSha256"])
        mutation = case["mutation"]
        raw = (source / mutation["file"]).read_text()
        require(raw.count(mutation["old"]) == 1, "ambiguous canonical mutation")
        expected[mutation["file"]] = h.digest_bytes(raw.replace(mutation["old"], mutation["new"], 1).encode())
        require(row["mutatedSourceSha256"] == expected, "mutation altered unreviewed source")


def check():
    dev = module("r2_development", "record-development.py")
    h = module("r2_negatives", "check-negative-scoped.py")
    report = json.loads((OUTPUT / "report.json").read_text())
    require(report.get("schema") == SCHEMA and report.get("status") == "passed", "R2 acceptance is incomplete")
    require(report.get("profile") == PROFILE and report.get("scope") == review(), "R2 scope changed")
    require(report.get("paperCompletion") is False and report.get("releaseAcceptance") is False
            and report.get("fullNegativeControls") == "not_run" and report.get("scopedCalibration") == "not_run",
            "R2 evidence overstates its scope")
    require(report["sourceSha256"] == dev.source_hashes(), "R2 source fingerprint is stale")
    require(report["kernelSha256"] == h.source_hashes(ROOT / "crates/cordis-kernel/src"), "kernel source changed")
    check_development(dev, h, report["development"])
    directory = OUTPUT / h.relative(report["evidenceDirectory"])
    require(directory.parent == OUTPUT and not directory.is_symlink(), "invalid evidence directory")
    validate_cases(report, selection(h), h, directory)
    print("R2 acceptance matches the current source, development evidence and 12 strict selected controls. Hash/evidence check only.")


def run_locked_source(offline):
    dev = module("r2_development", "record-development.py")
    h = module("r2_negatives", "check-negative-scoped.py")
    scope = review()
    cases = selection(h)
    report = {"schema": SCHEMA, "status": "running", "profile": PROFILE, "scope": scope,
              "paperCompletion": False, "releaseAcceptance": False, "fullNegativeControls": "not_run",
              "scopedCalibration": "not_run", "cases": []}
    # Invalidate any old success before checking the new source.
    save(report)
    try:
        before = dev.source_hashes()
        # Diagnose precise selected-contract expectations before the expensive
        # whole-kernel/runtime/package workflow. Final acceptance still requires
        # both on this unchanged source; selected positives alone cannot pass it.
        report["sourceSha256"] = before
        binary, environment, tool = h.tools_for(ROOT)
        report["tool"] = tool
        kernel = h.source_hashes(ROOT / "crates/cordis-kernel/src")
        report["kernelSha256"] = kernel
        # Use a new directory; never reuse positives or mutate the working tree.
        directory = Path(tempfile.mkdtemp(prefix="evidence-", dir=OUTPUT))
        report["evidenceDirectory"] = directory.name
        baseline = directory / "baseline"
        shutil.copytree(ROOT / "crates/cordis-kernel/src", baseline)
        require(h.source_hashes(baseline) == kernel, "source changed during snapshot")
        def invoke(label, tree, kind, targets=(), failures=()):
            artifact = directory / (label + ".rlib")
            h.verify_tool_artifacts(tool)
            command = h.command(binary, tree, kind, targets, 2, artifact, expected_failures=failures)
            result = h.run(command, environment, directory / label, 600)
            h.verify_tool_artifacts(tool)
            return result, artifact
        for case in cases:
            name = case["name"]
            print("R2 selected control: " + name, flush=True)
            row = {"name": name, "case": case}
            report["cases"].append(row)
            row["positive"], _ = invoke(name + "-positive", baseline, "selected", case["targets"], case["expectedFailures"])
            h.validate_positive(row["positive"], directory, entire=False, expected_tool=tool,
                                targets=case["targets"], expected_failures=case["expectedFailures"])
            mutated = directory / name
            row["mutatedSourceSha256"] = h.mutate(case, baseline, mutated)
            row["compile"], artifact = invoke(name + "-compile", mutated, "compile")
            h.validate_compile(row["compile"], directory, artifact)
            row["negative"], _ = invoke(name + "-mutant", mutated, "selected", case["targets"], case["expectedFailures"])
            h.validate_rejection(row["negative"], directory, case, mutated, tool)
            require(h.source_hashes(mutated) == row["mutatedSourceSha256"]
                    and h.source_hashes(baseline) == kernel and dev.source_hashes() == before,
                    "sources changed during selected checks")
            row["status"] = "passed"
            save(report)
        validate_cases(report, cases, h, directory)
        dev.record_development(offline)
        report["development"] = check_development(dev, h)
        require(dev.source_hashes() == before, "sources changed during development")
        h.verify_tool_artifacts(tool)
        report["status"] = "passed"
        report["checkedAt"] = datetime.now(timezone.utc).isoformat()
        save(report)
        print("R2 acceptance passed: " + str(OUTPUT / "report.json"), flush=True)
    except BaseException as error:
        report.update(status="failed", failure=f"{type(error).__name__}: {error}")
        save(report)
        raise


def run(offline):
    dev = module("r2_signals", "record-development.py")
    with dev.termination_signals():
        run_locked_source(offline)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.check:
        check()
    else:
        run(args.offline)

if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, KeyError, OSError) as error:
        sys.exit(f"R2 acceptance failed: {error}")
