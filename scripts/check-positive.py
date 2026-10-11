#!/usr/bin/env python3
"""Verify and compile the complete kernel once, retaining structured evidence."""

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = "cordis-verus.positive-proof/v1"
COMMAND = ["./scripts/verify.sh", "--num-threads", "2", "--triggers-mode", "silent", "--output-json", "--time"]
ARTIFACT = "target/verus/libcordis_kernel.rlib"


def module(filename, name):
    path = ROOT / "scripts" / filename
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), "exec"), result.__dict__)
    return result


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inputs():
    installer = module("install-verus.py", "positive_installer")
    directory = ROOT / ".tools" / installer.LOCK["verus"]["assets"][installer.platform_key()]["directory"]
    files = sorted(p for p in directory.iterdir() if p.is_file() and
                   (p.name in {"verus", "rust_verify", "z3", "version.json", "vstd.vir"}
                    or p.suffix in {".rlib", ".dylib", ".so"}))
    if not {"verus", "rust_verify", "z3", "vstd.vir"}.issubset({p.name for p in files}):
        raise RuntimeError("Missing pinned verifier, solver or proof libraries")
    return {"sourceHashes": module("record-verification.py", "positive_sources").source_hashes(),
            "toolHashes": {p.name: digest(p) for p in files}}


def validate_stats(stats):
    if (stats.get("success") is not True or type(stats.get("errors")) is not int or stats["errors"] != 0
            or type(stats.get("verified")) is not int or stats["verified"] <= 0
            or stats.get("encountered-vir-error") is not False
            or stats.get("encountered-error") is not False
            or stats.get("is-verifying-entire-crate") is not True):
        raise RuntimeError("Incomplete full-crate positive proof")


def validate(record, *, sources, lock):
    """Portable validation; read_evidence also checks the actual output files."""
    if (record.get("schema") != SCHEMA or record.get("status") != "passed"
            or type(record.get("returncode")) is not int or record["returncode"] != 0
            or record.get("command") != COMMAND or record.get("compiled") is not True
            or record.get("noCheating") is not True):
        raise RuntimeError("Missing compiled, no-cheating whole-kernel proof evidence")
    validate_stats(record.get("proof", {}))
    verus = record.get("verus", {})
    if verus.get("version") != lock["verus"]["version"] or verus.get("commit") != lock["verus"]["commit"]:
        raise RuntimeError("Positive proof does not use the pinned Verus version")
    if not sources or record.get("sourceHashes") != sources:
        raise RuntimeError("Positive proof sources differ from the quality run")
    artifact = record.get("artifact", {})
    hashes = [record.get("stdoutSha256"), record.get("stderrSha256"), artifact.get("sha256")]
    tools = record.get("toolHashes", {})
    if not {"verus", "rust_verify", "z3", "vstd.vir"}.issubset(tools):
        raise RuntimeError("Missing positive proof tool fingerprints")
    hashes.extend(tools.values())
    if any(not isinstance(value, str) or len(value) != 64 or any(c not in "0123456789abcdef" for c in value) for value in hashes):
        raise RuntimeError("Invalid positive proof fingerprints")
    if artifact.get("path") != ARTIFACT or type(artifact.get("bytes")) is not int or artifact["bytes"] <= 0:
        raise RuntimeError("Missing compiled kernel artifact")


def read_evidence(*, sources):
    output = ROOT / "target/positive-proof"
    record = json.loads((output / "report.json").read_text())
    validate(record, sources=sources, lock=json.loads((ROOT / "toolchain.lock.json").read_text()))
    for name in ("stdout", "stderr"):
        path = output / (name + (".json" if name == "stdout" else ".txt"))
        if digest(path) != record[name + "Sha256"]:
            raise RuntimeError("Positive proof output changed: " + name)
    raw = json.loads((output / "stdout.json").read_text())
    if raw.get("verification-results") != record["proof"] or raw.get("verus") != record["verus"]:
        raise RuntimeError("Positive proof summary differs from raw verifier output")
    artifact = ROOT / ARTIFACT
    if artifact.is_symlink() or artifact.stat().st_size != record["artifact"]["bytes"] or digest(artifact) != record["artifact"]["sha256"]:
        raise RuntimeError("Compiled kernel artifact changed")
    if inputs() != {"sourceHashes": sources, "toolHashes": record["toolHashes"]}:
        raise RuntimeError("Positive proof sources or toolchain changed")
    return record


def main():
    output = ROOT / "target/positive-proof"
    output.mkdir(parents=True, exist_ok=True)
    path = output / "report.json"
    record = {"schema": SCHEMA, "status": "running", "command": COMMAND}
    path.write_text(json.dumps(record, indent=2) + "\n")
    artifact = ROOT / ARTIFACT
    artifact.unlink(missing_ok=True)
    started = time.monotonic()
    try:
        if any(os.environ.get(name) for name in ("VERUS_Z3_PATH", "VERUS_EXTRA_ARGS", "RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER")):
            raise RuntimeError("Custom compiler/verifier overrides are not supported")
        before = inputs()
        with (output / "stdout.json").open("w") as stdout, (output / "stderr.txt").open("w") as stderr:
            # Stay in the enclosing recorder's process group for cancellation.
            process = subprocess.run(COMMAND, cwd=ROOT, stdout=stdout, stderr=stderr, stdin=subprocess.DEVNULL)
        if process.returncode:
            raise RuntimeError(f"Verus exited {process.returncode}; see target/positive-proof/stderr.txt")
        raw = json.loads((output / "stdout.json").read_text())
        record.update(status="passed", returncode=process.returncode, compiled=True, noCheating=True,
                      proof=raw.get("verification-results", {}), verus=raw.get("verus", {}), **before,
                      stdoutSha256=digest(output / "stdout.json"), stderrSha256=digest(output / "stderr.txt"),
                      artifact={"path": ARTIFACT, "bytes": artifact.stat().st_size, "sha256": digest(artifact)},
                      elapsedSeconds=round(time.monotonic() - started, 3))
        path.write_text(json.dumps(record, indent=2) + "\n")
        read_evidence(sources=before["sourceHashes"])
    except BaseException as error:
        path.write_text(json.dumps({"schema": SCHEMA, "status": "failed", "command": COMMAND,
                                    "failure": f"{type(error).__name__}: {error}"}, indent=2) + "\n")
        raise
    print(f"verification results:: {record['proof']['verified']} verified, 0 errors", flush=True)


if __name__ == "__main__":
    main()
