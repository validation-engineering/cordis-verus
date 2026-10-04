#!/usr/bin/env python3
"""Opt-in selected-proof mutation evidence. Never accepted as v3 release evidence.

This separate v2 entrypoint leaves full-mode and v3 release validation intact.
All verifier invocations use fresh temporary source trees; the project is read-only.
"""

import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
MANIFEST_SCHEMA = "cordis-verus.scoped-negative-manifest/v2"
REPORT_SCHEMA = "cordis-verus.scoped-negative-report/v2"
CRATE = "cordis_negative"
VERIFIER_LOCK = Path("/tmp/cordis-local-verifier.lock")
CONTRACTS = (
    "postcondition not satisfied", "precondition not satisfied", "assertion failed",
    "invariant not satisfied", "possible arithmetic underflow/overflow", "decreases not satisfied",
)
CONTRACT_VARIANTS = {
    "invariant not satisfied before loop": "invariant not satisfied",
    "invariant not satisfied at end of loop body": "invariant not satisfied",
    "invariant not satisfied at beginning of loop": "invariant not satisfied",
}
BASE_FLAGS = ["--crate-name", CRATE, "--crate-type=lib", "--edition=2021", "--no-cheating",
              "--output-json", "--triggers-mode", "silent", "--time", "--multiple-errors", "0"]
RESOURCE = re.compile(r"rlimit|resource.limit|timed? out|timeout|solver.*unknown|\bunknown\b|"
                      r"internal compiler error|panicked at|segmentation fault|killed by|out of memory", re.I)
SUMMARY = re.compile(r"error: aborting due to [1-9][0-9]* previous errors?(?:;.*)?$")
IDENT = r"[A-Za-z_][A-Za-z_0-9]*"
MODULE = re.compile(IDENT + r"(?:::" + IDENT + r")*\Z")


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def digest(path):
    with Path(path).open("rb") as source:
        result = hashlib.sha256()
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


HARNESS_SHA256 = digest(__file__)

def fingerprint(value):
    return digest_bytes(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def keys(value, expected, label):
    require(type(value) is dict and set(value) == set(expected), f"{label}: missing or unknown fields")


def relative(value):
    require(type(value) is str and value and "\\" not in value, "invalid relative path")
    path = PurePosixPath(value)
    require(not path.is_absolute() and ".." not in path.parts and str(path) == value,
            "invalid relative path")
    return value


def safe_file(root, name):
    path = root / relative(name)
    require(path.is_file() and path.resolve().is_relative_to(root.resolve()), "missing or escaping file")
    require(not any((root / Path(*Path(name).parts[:i])).is_symlink()
                    for i in range(1, len(Path(name).parts) + 1)), "symlink is not evidence")
    return path


def source_hashes(root):
    result = {}
    for path in sorted(root.rglob("*")):
        require(not path.is_symlink(), "source snapshot contains a symlink")
        if path.is_file():
            result[path.relative_to(root).as_posix()] = digest(path)
    require("lib.rs" in result, "source snapshot has no lib.rs")
    return result


def selectors(targets):
    require(type(targets) is list and targets, "at least one explicit target required")
    flags, seen = [], set()
    for target in targets:
        require(type(target) is dict, "invalid target")
        extra = ["function"] if "function" in target else []
        if target.get("kind") == "root":
            keys(target, ["kind", "timingModule"] + extra, "root target")
            require(type(target["timingModule"]) is str, "root timing module must be explicit")
            flag = ("--verify-root",)
        else:
            keys(target, ["kind", "path", "descendants"] + extra, "module target")
            require(target["kind"] == "module" and type(target["path"]) is str
                    and MODULE.fullmatch(target["path"]) and type(target["descendants"]) is bool,
                    "invalid module target")
            flag = ("--verify-module" if target["descendants"] else "--verify-only-module", target["path"])
        require(flag not in seen, "duplicate target")
        seen.add(flag)
        flags.extend(flag)
        if extra:
            require(len(targets) == 1 and type(target["function"]) is str
                    and MODULE.fullmatch(target["function"])
                    and target["function"].startswith(CRATE + "::")
                    and not target.get("descendants", False),
                    "single-function selection needs one exact module and full function name")
            # Pinned Verus lists functions relative to the selected module;
            # timing JSON keeps the full crate/module/type path.
            prefix = CRATE + ("::" + target["path"] if target["kind"] == "module" else "") + "::"
            require(target["function"].startswith(prefix), "function is not in the named module")
            flags.extend(["--verify-function", target["function"].removeprefix(prefix)])
    return flags


def covered(module, targets, function=None):
    # Type methods belong to the verifier's timing module, not a path guessed
    # by splitting Kernel::retire. A single-function target excludes siblings.
    return any(((target["kind"] == "root" and module == target["timingModule"]) or
                (target["kind"] == "module" and (module == target["path"] or
                 (target["descendants"] and module.startswith(target["path"] + "::")))))
               and ("function" not in target or function == target["function"])
               for target in targets)


def validate_manifest(manifest):
    keys(manifest, ["schema", "negativeMode", "cases"], "manifest")
    require(manifest["schema"] == MANIFEST_SCHEMA and manifest["negativeMode"] == "scoped-negative",
            "not a scoped-negative manifest")
    require(type(manifest["cases"]) is list and manifest["cases"], "empty manifest")
    names = []
    for case in manifest["cases"]:
        keys(case, ["name", "mutation", "targets", "expectedFailures", "selectionRationale"], "case")
        require(type(case["name"]) is str and re.fullmatch(r"[a-z][a-z0-9-]*", case["name"]), "invalid name")
        names.append(case["name"])
        mutation = case["mutation"]
        keys(mutation, ["file", "old", "new"], "mutation")
        relative(mutation["file"])
        require(mutation["file"].endswith(".rs") and type(mutation["old"]) is str and mutation["old"]
                and type(mutation["new"]) is str and mutation["old"] != mutation["new"], "invalid mutation")
        selectors(case["targets"])
        require(type(case["selectionRationale"]) is str and case["selectionRationale"].strip(), "rationale required")
        require(type(case["expectedFailures"]) is list and case["expectedFailures"], "expected failure required")
        seen = set()
        for failure in case["expectedFailures"]:
            keys(failure, ["function", "module", "file", "diagnosticKind", "uniqueSourceAnchor"], "expected failure")
            require(type(failure["function"]) is str and MODULE.fullmatch(failure["function"])
                    and failure["function"].startswith(CRATE + "::") and type(failure["module"]) is str
                    and covered(failure["module"], case["targets"], failure["function"]),
                    "expected function is outside explicit targets")
            relative(failure["file"])
            require(failure["file"].endswith(".rs"), "expected diagnostic file must be Rust source")
            require(failure["diagnosticKind"] in CONTRACTS and type(failure["uniqueSourceAnchor"]) is str
                    and failure["uniqueSourceAnchor"].strip(), "invalid expected failure")
            key = fingerprint(failure)
            require(key not in seen, "duplicate expected failure")
            seen.add(key)
        require(len({(failure["module"], failure["function"]) for failure in case["expectedFailures"]}) == 1,
                "requires exactly one expected failing function per case")
    require(len(names) == len(set(names)), "duplicate case")


def parse_json(text):
    # Duplicate object keys must not silently alter an audited manifest or result.
    def pairs(values):
        out = {}
        for key, value in values:
            require(key not in out, f"duplicate JSON key: {key}")
            out[key] = value
        return out
    return json.loads(text, object_pairs_hook=pairs)


def load_json(path):
    return parse_json(Path(path).read_text())


def diagnostics(stderr):
    # Primary errors are column-zero. A source excerpt containing 'error:' is data.
    lines, result = stderr.splitlines(), []
    for index, line in enumerate(lines):
        # Ignore rendered source excerpts, but include indented diagnostic prose.
        if not re.match(r"\s*(?:[0-9]+)?\s*\|", line):
            require(not RESOURCE.search(line), "resource/unknown/frontend failure is not contract evidence")
        if not line.startswith("error"):
            continue
        if SUMMARY.fullmatch(line):
            continue
        kind = CONTRACT_VARIANTS.get(line[7:], line[7:])
        require(line.startswith("error: ") and kind in CONTRACTS, f"unaccepted error: {line}")
        span = None
        for following in lines[index + 1:]:
            if following.startswith(("error", "note:", "warning:")):
                break
            match = re.match(r"\s*--> (.*):([0-9]+):([0-9]+)\s*$", following)
            if match:
                span = (match[1], int(match[2]), int(match[3]))
                break
        require(span is not None, "contract error has no primary source span")
        result.append((kind, *span))
    return result


def output(record, directory):
    require(type(record["timedOut"]) is bool and not record["timedOut"], "timed out: no evidence")
    require(type(record["interrupted"]) is bool and not record["interrupted"], "interrupted: no evidence")
    require(type(record["returncode"]) is int, "invalid process return code")
    data = {}
    for field in ("stdout", "stderr"):
        path = safe_file(directory, record[field])
        require(digest(path) == record[field + "Sha256"], "raw output changed")
        data[field] = path.read_text()
    return data


def result_data(record, directory, expected_tool=None):
    raw = output(record, directory)
    try:
        value = parse_json(raw["stdout"])
        stats = value["verification-results"]
        require(type(stats) is dict and stats["encountered-vir-error"] is False,
                "frontend error: no evidence")
        require(type(stats["verified"]) is int and stats["verified"] >= 0
                and type(stats["errors"]) is int and stats["errors"] >= 0, "invalid proof counts")
        if expected_tool:
            require(value["verus"]["version"] == expected_tool["version"]
                    and value["verus"]["commit"] == expected_tool["commit"], "wrong Verus version")
    except (ValueError, TypeError, KeyError) as error:
        raise RuntimeError("missing or malformed verification results") from error
    return value, stats, diagnostics(raw["stderr"])


def validate_positive(record, directory, *, entire, expected_tool=None, targets=None, expected_failures=None):
    value, stats, errors = result_data(record, directory, expected_tool)
    require(record["returncode"] == 0 and stats["verified"] > 0 and stats["errors"] == 0 and not errors
            and stats["is-verifying-entire-crate"] is entire, "positive baseline failed or has wrong scope")
    if entire:
        require(stats.get("success") is True and stats.get("encountered-error", False) is False,
                "whole positive baseline is incomplete")
    else:
        require(stats.get("encountered-error") is False and stats.get("success", True) is True,
                "selected positive baseline is incomplete")
        require(not failed_functions(value), "selected positive has failed timed proofs")
        timed = timed_functions(value)
        if targets is not None:
            require(all(any(covered(module, [target], function) for function, (module, _) in timed.items())
                        for target in targets), "a selected target has no timed proof: typo, empty scope, or unsupported output")
            require(all(covered(module, targets, function) for function, (module, _) in timed.items()),
                    "proof ran outside declared targets")
        if expected_failures is not None:
            require(all(timed.get(item["function"]) == (item["module"], True) for item in expected_failures),
                    "expected failure function was not proved in selected positive baseline")
    return stats


def timed_functions(value):
    """Return actual work/failures, never success=true zero-work placeholders.

    Pinned Verus lists every function in the selected module even with a
    --verify-function filter. Zero rlimit AND zero microseconds on a successful
    entry do not establish that its proof ran.
    """
    try:
        modules = value["times-ms"]["smt"]["smt-run-module-times"]
        require(type(modules) is list and modules, "no timed proof attribution")
        result, seen = {}, set()
        for module in modules:
            require(type(module["module"]) is str, "unsupported timing module encoding")
            for function in module["function-breakdown"]:
                require(type(function["success"]) is bool, "invalid timed proof result")
                name = function["function"]
                require(type(name) is str and name not in seen, "ambiguous timed function attribution")
                seen.add(name)
                require(type(function["time-micros"]) is int and function["time-micros"] >= 0
                        and type(function["rlimit"]) is int and function["rlimit"] >= 0,
                        "missing or invalid proof work attribution")
                if not function["success"] or function["time-micros"] > 0 or function["rlimit"] > 0:
                    result[name] = (module["module"], function["success"])
        return result
    except (TypeError, KeyError) as error:
        raise RuntimeError("no timed proof attribution") from error


def failed_functions(value):
    return {function for function, (_, success) in timed_functions(value).items() if not success}


def validate_rejection(record, directory, case, source, expected_tool=None, *, diagnostic_source=None):
    value, stats, errors = result_data(record, directory, expected_tool)
    require(record["returncode"] == 1 and stats["errors"] > 0
            and stats.get("encountered-error") is True and stats.get("success", False) is False
            and stats["is-verifying-entire-crate"] is False, "not a selected contract rejection")
    expected = case["expectedFailures"]
    require(failed_functions(value) == {item["function"] for item in expected}, "unexpected failed function set")
    timed = timed_functions(value)
    require(all(timed.get(item["function"]) == (item["module"], False) for item in expected),
            "failed function belongs to a different module")
    require(all(covered(module, case["targets"], function) for function, (module, _) in timed.items()),
            "proof ran outside declared targets")
    # Verus counts failed verification functions, not individual stderr errors.
    # One function can emit several reviewed pre/post/assertion diagnostics.
    require(stats["errors"] == len(failed_functions(value)), "unexpected failed-function count")
    require(len(errors) == len(expected), "unexpected diagnostic count")
    unmatched = list(errors)
    for item in expected:
        text = safe_file(source, item["file"]).read_text()
        anchor = item["uniqueSourceAnchor"]
        require(text.count(anchor) == 1, "expected diagnostic anchor is stale or ambiguous")
        start = text.index(anchor)
        end = start + len(anchor)
        lines = text.splitlines(keepends=True)
        def inside(line, column):
            if not (1 <= line <= len(lines) and 1 <= column <= len(lines[line - 1].rstrip("\r\n")) + 1):
                return False
            position = sum(len(part) for part in lines[:line - 1]) + column - 1
            return start <= position < end
        diagnostic_source = source if diagnostic_source is None else diagnostic_source
        matching = [error for error in unmatched if error[0] == item["diagnosticKind"]
                    and Path(error[1]).resolve() == (diagnostic_source / item["file"]).resolve()
                    and inside(error[2], error[3])]
        require(len(matching) == 1, "contract diagnostic does not match its reviewed anchor")
        unmatched.remove(matching[0])
    return stats


def command(binary, source, kind, targets, threads, artifact):
    result = [str(binary), str(source / "lib.rs"), *BASE_FLAGS, "--num-threads", str(threads)]
    if kind == "compile":
        require(not targets, "compile must be whole crate")
        result += ["--no-verify", "--compile", "-o", str(artifact)]
    elif kind == "selected":
        result += selectors(targets)
    else:
        require(kind == "whole" and not targets, "invalid command scope")
    return result


@contextmanager
def verifier_lease():
    """Serialize local verifier work; lock wait is not verifier wall time."""
    started = time.monotonic()
    with VERIFIER_LOCK.open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        yield round(time.monotonic() - started, 3)


def terminate_group(process):
    """Kill/reap the entire verifier group before releasing its resource lease."""
    def send(sig):
        try:
            os.killpg(process.pid, sig)
        except ProcessLookupError:
            pass
    send(signal.SIGTERM)
    try:
        return process.communicate(timeout=2)
    except BaseException:
        send(signal.SIGKILL)
        # A second interrupt must not leave the solver group alive. The group
        # has already received KILL; keep reaping rather than releasing the lock.
        while True:
            try:
                return process.communicate()
            except KeyboardInterrupt:
                send(signal.SIGKILL)


def run(command_line, environment, prefix, timeout):
    with verifier_lease() as waited:
        started = time.monotonic()
        process = subprocess.Popen(command_line, env=environment, text=True, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True)
        timed_out, interrupted = False, False
        try:
            stdout, stderr = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            stdout, stderr = terminate_group(process)
        except BaseException:
            interrupted = True
            stdout, stderr = terminate_group(process)
        elapsed = round(time.monotonic() - started, 3)
    stdout_path = prefix.with_suffix(".stdout.json")
    stderr_path = prefix.with_suffix(".stderr.txt")
    stdout_path.write_text(stdout)
    stderr_path.write_text(stderr)
    return {"command": command_line, "returncode": process.returncode, "timedOut": timed_out,
            "interrupted": interrupted, "elapsedSeconds": elapsed, "lockWaitSeconds": waited,
            "stdout": stdout_path.name, "stdoutSha256": digest(stdout_path),
            "stderr": stderr_path.name, "stderrSha256": digest(stderr_path)}


def validate_compile(record, directory, artifact):
    raw = output(record, directory)
    require(record["returncode"] == 0 and not diagnostics(raw["stderr"]), "whole mutant compilation failed")
    require(artifact.is_file() and artifact.stat().st_size > 0, "compiler did not emit an artifact")
    record["artifactSha256"] = digest(artifact)
    record["artifactBytes"] = artifact.stat().st_size


def mutate(case, original, destination):
    shutil.copytree(original, destination)
    path = safe_file(destination, case["mutation"]["file"])
    text = path.read_text()
    require(text.count(case["mutation"]["old"]) == 1, "mutation anchor is stale or ambiguous")
    path.write_text(text.replace(case["mutation"]["old"], case["mutation"]["new"]))
    return source_hashes(destination)


def preflight(manifest, baseline):
    """Reject stale anchors before any expensive proof process is launched."""
    for case in manifest["cases"]:
        mutation = case["mutation"]
        original = safe_file(baseline, mutation["file"]).read_text()
        require(original.count(mutation["old"]) == 1, "mutation anchor is stale or ambiguous")
        for expected in case["expectedFailures"]:
            text = safe_file(baseline, expected["file"]).read_text()
            if expected["file"] == mutation["file"]:
                text = text.replace(mutation["old"], mutation["new"])
            require(text.count(expected["uniqueSourceAnchor"]) == 1, "expected diagnostic anchor is stale or ambiguous")


def tools_for(project):
    spec = importlib.util.spec_from_file_location("pinned_installer", project / "scripts/install-verus.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    lock = module.LOCK
    tool_dir = project / ".tools" / lock["verus"]["assets"][module.platform_key()]["directory"]
    binary = (tool_dir / "verus").resolve()
    environment = os.environ.copy()
    cargo = Path(environment.get("CARGO_HOME", str(Path.home() / ".cargo"))) / "bin"
    environment["PATH"] = str(cargo) + os.pathsep + environment.get("PATH", "")
    environment["RUSTUP_TOOLCHAIN"] = lock["rust"]["channel"]
    require(not any(environment.get(name) for name in ("VERUS_Z3_PATH", "RUSTFLAGS", "RUSTC_WRAPPER",
                                                       "RUSTC_WORKSPACE_WRAPPER", "VERUS_EXTRA_ARGS")),
            "custom verifier/compiler environment is unsupported")
    paths = [tool_dir / name for name in ("verus", "rust_verify", "z3", "vstd.vir", "libvstd.rlib", "libverus_builtin.rlib")]
    paths += sorted(tool_dir.glob("*.dylib")) + sorted(tool_dir.glob("*.so"))
    for path in paths:
        require(path.is_file(), "missing pinned tool artifact")
    rust = subprocess.run([str(cargo / "rustup"), "run", lock["rust"]["channel"], "rustc", "-vV"],
                          env=environment, text=True, capture_output=True, timeout=30, check=True).stdout
    tool = {"binary": str(binary), "version": lock["verus"]["version"], "commit": lock["verus"]["commit"],
            "lock": lock, "files": {path.name: digest(path) for path in paths},
            "artifactPaths": {path.name: str(path.resolve()) for path in paths}, "rustc": rust}
    return binary, environment, tool


def verify_tool_artifacts(tool):
    """A long run must not silently use replacements at the same pinned path."""
    require(type(tool.get("files")) is dict and tool["files"]
            and type(tool.get("artifactPaths")) is dict
            and set(tool["files"]) == set(tool["artifactPaths"]), "missing tool artifact binding")
    require(tool["artifactPaths"].get("verus") == tool["binary"], "wrong verifier artifact binding")
    for name, expected in tool["files"].items():
        path = Path(tool["artifactPaths"][name])
        require(path.is_absolute() and path.is_file() and digest(path) == expected,
                "tool artifact changed during verification")


def validate_canonical_cases(manifest, project):
    script = project / "scripts/check-negative.py"
    original = script.read_bytes()
    spec = importlib.util.spec_from_file_location("canonical_negatives", script)
    module = importlib.util.module_from_spec(spec)
    exec(compile(original, str(script), "exec"), module.__dict__)
    require(script.read_bytes() == original, "canonical harness changed while loading")
    mutations = module.mutation_manifest()
    require(len({item[0] for item in mutations}) == len(mutations), "duplicate canonical control")
    expected = [(name, {"file": file, "old": old, "new": new}) for name, file, old, new in mutations]
    actual = [(case["name"], case["mutation"]) for case in manifest["cases"]]
    require(actual == expected, "cases must cover every canonical mutation in exact order")
    return len(mutations)


def binding(source, manifest, tool, threads, timeout, canonical_manifest_sha256=None):
    return {"sourceSha256": fingerprint(source_hashes(source)), "manifestSha256": fingerprint(manifest),
            "toolSha256": fingerprint(tool), "verifierPath": tool["binary"], "harnessSha256": HARNESS_SHA256,
            "canonicalManifestSha256": canonical_manifest_sha256,
            "flags": BASE_FLAGS, "threads": threads, "timeoutSeconds": timeout}


def validate_record_command(record, kind, targets, run_binding, *, source_name):
    argv = record.get("command")
    require(type(argv) is list and all(type(arg) is str for arg in argv) and len(argv) > 2,
            "missing invocation command")
    source = Path(argv[1]).parent
    require(Path(argv[0]).is_absolute() and argv[0] == run_binding["verifierPath"]
            and source.is_absolute() and source.name == source_name
            and Path(argv[1]).name == "lib.rs", "invalid invocation paths")
    artifact = Path(argv[-1]) if kind == "compile" else source / "unused.rlib"
    require(argv == command(argv[0], source, kind, targets, run_binding["threads"], artifact),
            "invocation flags or selected targets changed")
    return source


def validate_calibration(path, expected_binding, manifest, baseline, canonical_count):
    report = load_json(path)
    keys(report, ["schema", "negativeMode", "purpose", "status", "is-verifying-entire-crate", "claim",
                  "canonicalControlCount", "selectedControlCount", "binding", "manifest", "tool", "calibration",
                  "wholePositive", "cases"], "passed calibration report")
    require(report.get("schema") == REPORT_SCHEMA and report.get("negativeMode") == "scoped-negative"
            and report.get("purpose") == "calibration" and report.get("status") == "passed"
            and report.get("is-verifying-entire-crate") is False, "not passed scoped calibration evidence")
    require(report.get("binding") == expected_binding, "stale calibration binding: recalibrate explicitly")
    require(report.get("manifest") == manifest, "calibration manifest mismatch")
    require(type(report["canonicalControlCount"]) is int and type(report["selectedControlCount"]) is int
            and report["canonicalControlCount"] == canonical_count
            and canonical_count == report["selectedControlCount"] == len(manifest["cases"]),
            "calibration control counts do not match explicit scope")
    require(fingerprint(report.get("tool")) == expected_binding["toolSha256"]
            and fingerprint(manifest) == expected_binding["manifestSha256"]
            and fingerprint(source_hashes(baseline)) == expected_binding["sourceSha256"],
            "calibration payload does not match its binding")
    require([case.get("name") for case in report.get("cases", [])] == [case["name"] for case in manifest["cases"]],
            "calibration cases incomplete or reordered")
    # Calibration is a trusted local audit artifact, not a signature. Hash all raw
    # logs and recheck strict positive/failure results; source and tool identities
    # are bound above. Diagnostic paths belonged to the saved temporary snapshot.
    directory = path.parent
    baseline_path = validate_record_command(report["wholePositive"], "whole", (), expected_binding, source_name="baseline")
    validate_positive(report["wholePositive"], directory, entire=True, expected_tool=report["tool"])
    with tempfile.TemporaryDirectory(prefix="cordis-calibration-replay-") as temp:
        for case, result in zip(manifest["cases"], report["cases"]):
            keys(result, ["name", "targets", "is-verifying-entire-crate", "selectedPositive", "mutantSourceSha256",
                          "wholeCompile", "selectedMutant"], "passed calibration case")
            require(result.get("targets") == case["targets"] and result.get("is-verifying-entire-crate") is False,
                    "calibration scope changed")
            require(validate_record_command(result["selectedPositive"], "selected", case["targets"], expected_binding,
                                            source_name="baseline") == baseline_path,
                    "selected positive used a different baseline tree")
            validate_positive(result["selectedPositive"], directory, entire=False, expected_tool=report["tool"],
                              targets=case["targets"], expected_failures=case["expectedFailures"])
            old_source = validate_record_command(result["wholeCompile"], "compile", (), expected_binding,
                                                 source_name=case["name"])
            require(validate_record_command(result["selectedMutant"], "selected", case["targets"], expected_binding,
                                            source_name=case["name"]) == old_source,
                    "compiled and verified different mutant trees")
            compile_raw = output(result["wholeCompile"], directory)
            require(result["wholeCompile"]["returncode"] == 0 and not diagnostics(compile_raw["stderr"])
                    and type(result["wholeCompile"]["artifactBytes"]) is int
                    and result["wholeCompile"]["artifactBytes"] > 0
                    and re.fullmatch(r"[0-9a-f]{64}", result["wholeCompile"]["artifactSha256"]),
                    "calibration compilation failed")
            reconstructed = Path(temp) / case["name"]
            hashes = mutate(case, baseline, reconstructed)
            require(fingerprint(hashes) == result.get("mutantSourceSha256"), "calibration mutant source mismatch")
            validate_rejection(result["selectedMutant"], directory, case, reconstructed, report["tool"],
                               diagnostic_source=old_source)
    return {"reportSha256": digest(path), "bindingSha256": fingerprint(expected_binding)}


def execute(manifest, baseline, workspace, report_dir, binary, environment, tool, run_binding,
            *, purpose, canonical_count, threads=1, timeout=600, runner=run, calibration=None,
            canonical_file=None):
    require(type(canonical_count) is int and canonical_count == len(manifest["cases"]),
            "run must cover all canonical controls")
    report = {"schema": REPORT_SCHEMA, "negativeMode": "scoped-negative", "purpose": purpose,
              "status": "running", "is-verifying-entire-crate": False,
              "claim": "Only the explicitly selected proofs rejected these compiling mutations.",
              "canonicalControlCount": canonical_count, "selectedControlCount": len(manifest["cases"]),
              "binding": run_binding, "manifest": manifest, "tool": tool, "calibration": calibration,
              "wholePositive": None, "cases": []}
    report_path = report_dir / "scoped-report.json"
    def save():
        report_path.write_text(json.dumps(report, indent=2) + "\n")
    def invoke(label, source, kind, targets=()):
        artifact = workspace / (label + ".rlib")
        require(digest(__file__) == HARNESS_SHA256 == run_binding["harnessSha256"],
                "scoped harness changed during verification")
        if canonical_file is not None:
            require(digest(canonical_file) == run_binding["canonicalManifestSha256"],
                    "canonical harness changed during verification")
        require(str(binary) == run_binding["verifierPath"], "unbound verifier invocation")
        if kind == "compile":
            require(not artifact.exists(), "compilation artifact is not fresh")
        verify_tool_artifacts(tool)
        cmd = command(binary, source, kind, targets, threads, artifact)
        record = runner(cmd, environment, report_dir / label, timeout)
        verify_tool_artifacts(tool)
        require(digest(__file__) == HARNESS_SHA256, "scoped harness changed during verification")
        if canonical_file is not None:
            require(digest(canonical_file) == run_binding["canonicalManifestSha256"],
                    "canonical harness changed during verification")
        return record, artifact
    save()
    expected_source = source_hashes(baseline)
    try:
        whole, _ = invoke("whole-positive", baseline, "whole")
        report["wholePositive"] = whole
        validate_positive(whole, report_dir, entire=True, expected_tool=tool)
        require(source_hashes(baseline) == expected_source, "positive source changed during verification")
        save()
        for case in manifest["cases"]:
            name = case["name"]
            result = {"name": name, "targets": case["targets"], "is-verifying-entire-crate": False}
            report["cases"].append(result)
            positive, _ = invoke(name + "-positive", baseline, "selected", case["targets"])
            result["selectedPositive"] = positive
            validate_positive(positive, report_dir, entire=False, expected_tool=tool, targets=case["targets"],
                              expected_failures=case["expectedFailures"])
            require(source_hashes(baseline) == expected_source, "selected positive source changed")
            mutated = workspace / name
            mutant_hashes = mutate(case, baseline, mutated)
            result["mutantSourceSha256"] = fingerprint(mutant_hashes)
            compiled, artifact = invoke(name + "-compile", mutated, "compile")
            result["wholeCompile"] = compiled
            validate_compile(compiled, report_dir, artifact)
            require(source_hashes(mutated) == mutant_hashes, "mutant source changed during compilation")
            require(source_hashes(baseline) == expected_source, "baseline changed during mutant compilation")
            failed, _ = invoke(name + "-mutant", mutated, "selected", case["targets"])
            result["selectedMutant"] = failed
            validate_rejection(failed, report_dir, case, mutated, tool)
            require(source_hashes(mutated) == mutant_hashes, "mutant source changed during verification")
            require(source_hashes(baseline) == expected_source, "baseline changed during mutant verification")
            save()
        report["status"] = "passed"
        save()
        return report
    except BaseException as error:
        report["status"] = "failed"
        report["failure"] = str(error)
        save()
        raise


def positive(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--negative-mode", choices=["scoped-negative"], required=True)
    parser.add_argument("--action", choices=["calibrate", "check"], required=True)
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--report-dir", type=Path, required=True)
    parser.add_argument("--calibration", type=Path)
    parser.add_argument("--threads", type=positive, default=1)
    parser.add_argument("--timeout", type=positive, default=600)
    args = parser.parse_args()
    require((args.action == "check") == (args.calibration is not None),
            "check requires calibration; calibrate must not reuse one")
    project = args.project_root.resolve()
    reports = args.report_dir.resolve()
    require(not reports.is_relative_to(project), "scoped reports must be outside the project")
    require(not reports.exists(), "report directory must be new; never overwrite evidence")
    manifest = load_json(args.manifest)
    validate_manifest(manifest)
    canonical_file = project / "scripts/check-negative.py"
    canonical_sha = digest(canonical_file)
    count = validate_canonical_cases(manifest, project)
    require(digest(canonical_file) == canonical_sha, "canonical harness changed while validating")
    binary, environment, tool = tools_for(project)
    source = project / "crates/cordis-kernel/src"
    before = source_hashes(source)
    reports.mkdir(parents=True)
    with tempfile.TemporaryDirectory(prefix="cordis-scoped-negative-") as temporary:
        workspace = Path(temporary)
        baseline = workspace / "baseline"
        shutil.copytree(source, baseline)
        require(source_hashes(baseline) == before == source_hashes(source), "source changed while snapshotting")
        preflight(manifest, baseline)
        run_binding = binding(baseline, manifest, tool, args.threads, args.timeout,
                              canonical_sha)
        calibration = (validate_calibration(args.calibration.resolve(), run_binding, manifest, baseline, count)
                       if args.calibration else None)
        execute(manifest, baseline, workspace, reports, binary, environment, tool, run_binding,
                purpose="calibration" if args.action == "calibrate" else "check", canonical_count=count,
                threads=args.threads, timeout=args.timeout, calibration=calibration,
                canonical_file=canonical_file)
    print(f"Passed selected-proof evidence only: {reports / 'scoped-report.json'}")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        sys.exit(f"Scoped-negative check failed: {error}")
