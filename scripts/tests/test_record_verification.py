"""Release quality is independent of full negative regression evidence."""
import copy
from contextlib import contextmanager, nullcontext, redirect_stdout, redirect_stderr
import io
import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time
from types import SimpleNamespace
import unittest
import tempfile
from unittest.mock import patch
from evidence_fixtures import LOCK, positive, quality_log, release

SCRIPT = Path(__file__).resolve().parents[1] / "record-verification.py"
SPEC = importlib.util.spec_from_file_location("verification_record", SCRIPT)
RECORD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RECORD)
RUNTIME = RECORD.execution_helpers()
POSITIVE = RECORD.positive_helpers()


def report(names):
    positive = {"success": True, "errors": 0, "verified": 40,
                "encountered-vir-error": False, "is-verifying-entire-crate": True}
    negative = {**positive, "success": False, "errors": 1, "verified": 39}
    return {"baseline": positive, "mutations": [
        {"name": name, "compiles": True, "verification-results": negative.copy()} for name in names
    ]}


class CompleteRecordTests(unittest.TestCase):
    def test_accepts_every_control_in_manifest_order(self):
        names = RECORD.required_negative_names()
        self.assertGreater(len(names), 5)
        RECORD.validate_negative_report(report(names), names)

    def test_rejects_missing_duplicate_extra_and_reordered_controls(self):
        expected = ["first", "second", "third", "fourth", "fifth", "sixth"]
        for recorded in [expected[:5], expected + ["extra"], expected[:-1] + ["first"], list(reversed(expected))]:
            with self.subTest(recorded=recorded), self.assertRaisesRegex(RuntimeError, "manifest"):
                RECORD.validate_negative_report(report(recorded), expected)

    def test_rejects_partial_or_failed_positive_baseline(self):
        original = report(["one"])
        for change in [{"success": False}, {"errors": 1}, {"errors": False}, {"verified": 0}, {"verified": True}, {"verified": "40"},
                       {"encountered-vir-error": True}, {"is-verifying-entire-crate": False}]:
            candidate = copy.deepcopy(original)
            candidate["baseline"].update(change)
            with self.subTest(change=change), self.assertRaisesRegex(RuntimeError, "positive"):
                RECORD.validate_negative_report(candidate, ["one"])

    def test_rejects_uncompiled_or_nonconclusive_control_stats(self):
        original = report(["one"])
        for change in [{"success": True}, {"errors": 0}, {"verified": 0}, {"verified": True}, {"verified": "40"},
                       {"encountered-vir-error": True}, {"is-verifying-entire-crate": False}]:
            candidate = copy.deepcopy(original)
            candidate["mutations"][0]["verification-results"].update(change)
            with self.subTest(change=change), self.assertRaisesRegex(RuntimeError, "negative"):
                RECORD.validate_negative_report(candidate, ["one"])
        original["mutations"][0]["compiles"] = False
        with self.assertRaisesRegex(RuntimeError, "negative"):
            RECORD.validate_negative_report(original, ["one"])

    def test_rejects_empty_or_ambiguous_manifest(self):
        for expected in [[], ["same", "same"]]:
            with self.subTest(expected=expected), self.assertRaisesRegex(RuntimeError, "manifest"):
                RECORD.validate_negative_report(report(expected), expected)


class NativeEvidenceInputTests(unittest.TestCase):
    def test_hashes_javascript_types_and_locks_but_not_node_modules_or_binaries(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            fixtures = ["packages/compat-cordis/runtime.js", "packages/compat-cordis/index.cjs",
                        "packages/compat-cordis/index.d.ts", "scripts/build-node.mjs",
                        "tests/node-compat/lifecycle.test.mjs", "tests/node-compat/types.tsx",
                        "package-lock.json", "node_modules/vendor/index.js",
                        "packages/compat-cordis/node_modules/vendor/index.js",
                        "packages/compat-cordis/native/cordis.node", "target/node-compat/build.json",
                        "packages/compat-cordis/native/manifest.json",
                        "packages/compat-cordis/native/provenance/darwin-arm64-napi8.json",
                        "docs/development-report.json", "docs/verification-report.json"]
            for name in fixtures:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(name)
            with patch.object(RECORD, "ROOT", root):
                hashes = RECORD.source_hashes()
            self.assertEqual(set(hashes), set(fixtures[:7]))

    def test_unit_test_counts_keep_all_workspace_crates_separate(self):
        lines = []
        for name, count in (("cordis", 2), ("cordis_kernel", 3), ("cordis_driver", 5), ("cordis_node", 7)):
            lines.extend([f"Running unittests src/lib.rs (target/debug/deps/{name}-abc012)",
                          f"test result: ok. {count} passed; 0 failed;"])
        counts = RECORD.test_counts("\n".join(lines))
        self.assertEqual(counts["suites"], {"host_unit": 2, "kernel_unit": 3, "cordis_driver_unit": 5, "cordis_node_unit": 7})
        self.assertEqual(counts["total"], 17)



class ReleaseRecordingTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="cordis-release-record-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.record = self.root / "docs/verification-report.json"
        self.record.parent.mkdir()
        self.record.write_text(json.dumps({"schema": RECORD.SCHEMA, "status": "passed", "sha256": {}}))
        self.proof = self.root / "target/positive-proof/report.json"
        self.proof.parent.mkdir(parents=True)
        self.proof.write_text(json.dumps(report(["old"])))
        self.packages = self.root / "target/release-artifacts/package-report.json"
        self.packages.parent.mkdir(parents=True)
        self.packages.write_text('{"stale": true}')
        (self.root / "crates/cordis/examples").mkdir(parents=True)
        (self.root / "crates/cordis/examples/demo.rs").write_text("fn main() {}\n")
        self.input = self.root / "input.rs"
        self.input.write_text("source")
        self.events = []
        self.addCleanup(patch.stopall)
        patch.object(RECORD, "ROOT", self.root).start()
        patch.object(RECORD, "RECORD", self.record).start()
        (self.root / "toolchain.lock.json").write_text(json.dumps(LOCK))
        self.node = release()["nodeBuild"]
        self.npm = release()["npmDistribution"]
        patch.object(RECORD, "positive_helpers", return_value=SimpleNamespace(
            validate=POSITIVE.validate, read_evidence=lambda **_: json.loads(self.proof.read_text()))).start()
        patch.object(RECORD, "execution_helpers", return_value=SimpleNamespace(
            verifier_lease=self.lease, termination_signals=nullcontext, parse_results=RUNTIME.parse_results,
            node_build_evidence=lambda _: self.node, npm_distribution_evidence=lambda *_: self.npm,
            file_sha256=lambda _: "a" * 64)).start()
        patch.dict(os.environ, {}, clear=True).start()

    @contextmanager
    def lease(self):
        self.events.append("lock")
        try:
            yield
        finally:
            self.events.append("unlock")

    def successful_checks(self, command, environment, log):
        self.assertEqual(self.events, ["lock"])
        self.assertEqual(json.loads(self.record.read_text())["status"], "running")
        self.assertFalse(self.proof.exists(), "old positive evidence must be removed")
        self.assertFalse(self.packages.exists(), "old package evidence must be removed")
        self.assertEqual(environment["CORDIS_VERUS_THREADS"], "2")
        self.assertNotIn("CORDIS_FULL_NEGATIVE_SHARDS", environment)
        evidence = positive(RECORD.source_hashes())
        self.proof.write_text(json.dumps(evidence))
        self.packages.write_text('{"fresh": true}')
        log.write_text(quality_log(RECORD.QUALITY_MARKER))
        return 0

    def run_record(self, **options):
        with redirect_stdout(io.StringIO()):
            return RECORD.record_release(**options)

    def test_default_gate_ignores_inherited_shard_selection_and_records_fresh_proof(self):
        with patch.dict(os.environ, {"CORDIS_FULL_NEGATIVE_SHARDS": "/stale/artifacts", "CORDIS_VERUS_THREADS": "99"}):
            with patch.object(RECORD, "run_checks", side_effect=self.successful_checks) as checks:
                recorded = self.run_record(offline=True)
        self.assertEqual(recorded["status"], "passed")
        self.assertEqual(recorded["commands"], [["./scripts/quality.sh", "--offline"]])
        self.assertEqual(recorded["negativeControls"], RECORD.NEGATIVE_POLICY)
        self.assertNotIn("CORDIS_FULL_NEGATIVE_SHARDS", checks.call_args.args[1])
        self.assertEqual(checks.call_args.args[1]["CARGO_NET_OFFLINE"], "true")
        self.assertEqual(self.events, ["lock", "unlock"])
        self.assertEqual(recorded["tests"]["total"], 4)
        self.assertEqual(recorded["ci"], "local execution; GitHub Actions was not used for this record")

    def test_ci_record_identifies_actual_github_actions_execution(self):
        with patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}), \
                patch.object(RECORD, "run_checks", side_effect=self.successful_checks):
            recorded = self.run_record()
        self.assertEqual(recorded["ci"], "GitHub Actions; this report describes the current workflow run")

    def test_zero_exit_without_new_positive_proof_cannot_reuse_the_previous_report(self):
        def incomplete(_command, _environment, log):
            self.assertFalse(self.proof.exists())
            log.write_text("quality omitted proof output")
            self.packages.write_text('{"fresh": true}')
            return 0
        with patch.object(RECORD, "run_checks", side_effect=incomplete), self.assertRaises(FileNotFoundError):
            self.run_record()
        self.assertEqual(json.loads(self.record.read_text())["status"], "failed")
        self.assertFalse(self.proof.exists())
        self.assertEqual(self.events, ["lock", "unlock"])

    def test_failed_command_invalidates_old_success_and_does_not_reuse_positive_report(self):
        with patch.object(RECORD, "run_checks", return_value=17), self.assertRaisesRegex(RuntimeError, "17"):
            self.run_record()
        failed = json.loads(self.record.read_text())
        self.assertEqual(failed["status"], "failed")
        self.assertEqual(failed["sha256"], {})
        self.assertNotIn("negativeControls", failed)
        self.assertFalse(self.proof.exists())
        self.assertFalse(self.packages.exists())

    def test_interrupt_releases_lease_and_cannot_retain_a_passed_record(self):
        with patch.object(RECORD, "run_checks", side_effect=KeyboardInterrupt), self.assertRaises(KeyboardInterrupt):
            self.run_record()
        self.assertEqual(json.loads(self.record.read_text())["status"], "failed")
        self.assertEqual(self.events, ["lock", "unlock"])
        self.assertFalse(self.proof.exists())

    def test_changed_sources_reject_otherwise_successful_run(self):
        def changed(*args):
            result = self.successful_checks(*args)
            self.input.write_text("changed")
            return result
        with patch.object(RECORD, "run_checks", side_effect=changed), self.assertRaisesRegex(RuntimeError, "Sources changed"):
            self.run_record()
        self.assertEqual(json.loads(self.record.read_text())["status"], "failed")

    def test_partial_positive_proof_is_rejected(self):
        def partial(*args):
            result = self.successful_checks(*args)
            evidence = json.loads(self.proof.read_text())
            evidence["proof"]["is-verifying-entire-crate"] = False
            self.proof.write_text(json.dumps(evidence))
            return result
        with patch.object(RECORD, "run_checks", side_effect=partial), self.assertRaisesRegex(RuntimeError, "positive"):
            self.run_record()
        self.assertEqual(json.loads(self.record.read_text())["status"], "failed")

    def test_missing_runtime_sections_fail_despite_successful_proof(self):
        def incomplete(*args):
            result = self.successful_checks(*args)
            args[2].write_text("verification results:: 40 verified, 0 errors\n" + RECORD.QUALITY_MARKER + "\n")
            return result
        with patch.object(RECORD, "run_checks", side_effect=incomplete), self.assertRaisesRegex(RuntimeError, "workspace"):
            self.run_record()
        self.assertEqual(json.loads(self.record.read_text())["status"], "failed")

    def test_custom_verifier_environment_is_rejected(self):
        with patch.dict(os.environ, {"VERUS_EXTRA_ARGS": "--no-verify"}), \
                patch.object(RECORD, "run_checks") as checks, self.assertRaisesRegex(RuntimeError, "overrides"):
            self.run_record()
        checks.assert_not_called()
        self.assertEqual(json.loads(self.record.read_text())["status"], "failed")

    def test_cli_rejects_legacy_shard_selection_instead_of_silently_ignoring_it(self):
        with patch.object(sys, "argv", ["record-verification.py", "--offline"]), patch.object(RECORD, "record_release") as run:
            RECORD.main()
        run.assert_called_once_with(True, False)
        with patch.object(sys, "argv", ["record-verification.py", "--negative-shards", "input"]), \
                patch.object(RECORD, "record_release") as run, redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as error:
            RECORD.main()
        self.assertEqual(error.exception.code, 2)
        run.assert_not_called()


class CheckScriptRoutingTests(unittest.TestCase):
    def test_ambient_shard_selection_cannot_add_negatives_or_skip_positive_tests(self):
        with tempfile.TemporaryDirectory(prefix="cordis-check-routing-") as temporary:
            root = Path(temporary)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copyfile(SCRIPT.parent / "check.sh", scripts / "check.sh")
            (scripts / "toolchain-env.sh").write_text('CORDIS_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"\n')
            (scripts / "verify.sh").write_text('#!/usr/bin/env bash\nprintf "verify %s\\n" "$*" >> "$TRACE"\n')
            (scripts / "verify.sh").chmod(0o755)
            binary = root / "bin"
            binary.mkdir()
            (binary / "cargo").write_text('#!/usr/bin/env bash\nprintf "cargo %s\\n" "$*" >> "$TRACE"\n')
            (binary / "cargo").chmod(0o755)
            for name in ("check-positive.py", "check-negative.py", "negative-shards.py"):
                (scripts / name).write_text("import json,os,sys\nwith open(os.environ['TRACE'],'a') as output:\n"
                                          "    output.write(json.dumps(sys.argv)+'\\n')\n")
            examples = root / "crates/cordis/examples"
            examples.mkdir(parents=True)
            (examples / "demo.rs").write_text("fn main() {}")
            for shards in (None, root / "full shards"):
                with self.subTest(shards=shards):
                    trace = root / "trace"
                    trace.unlink(missing_ok=True)
                    environment = {**os.environ, "PATH": str(binary) + os.pathsep + os.environ["PATH"], "TRACE": str(trace)}
                    environment.pop("CORDIS_FULL_NEGATIVE_SHARDS", None)
                    environment.pop("CORDIS_VERUS_THREADS", None)
                    if shards:
                        environment["CORDIS_FULL_NEGATIVE_SHARDS"] = str(shards)
                    subprocess.run(["bash", str(scripts / "check.sh")], env=environment, check=True, capture_output=True, text=True)
                    lines = trace.read_text().splitlines()
                    self.assertEqual(len(lines), 4)
                    self.assertEqual(json.loads(lines[0]), ["scripts/check-positive.py"])
                    self.assertEqual(lines[1:], ["cargo test --workspace --all-features --locked",
                                                "cargo run --locked -p cordis-kernel --example semantic_context",
                                                "cargo run --locked --all-features -p cordis-verus --example demo"])


@unittest.skipUnless(os.name == "posix", "supported Verus platforms are POSIX")
class ReleaseProcessTests(unittest.TestCase):
    def test_cancellation_during_finish_cannot_return_success_from_release_command(self):
        checks = RECORD.helper("check-negative.py", "release_finish_race_test")
        class CancelAfterCleanup(checks.ProcessSupervisor):
            def finish(self, process, *, terminate=False):
                super().finish(process, terminate=terminate)
                self.cancel()

        with tempfile.TemporaryDirectory(prefix="cordis-release-finish-") as temporary:
            with patch.object(RECORD, "helper", return_value=SimpleNamespace(ProcessSupervisor=CancelAfterCleanup)), \
                    self.assertRaises(checks.RunCancelled):
                RECORD.run_checks([sys.executable, "-c", "pass"], os.environ.copy(), Path(temporary) / "checks.log")

    def test_cancellation_allows_nested_negative_supervisor_to_reap_its_process_group(self):
        with tempfile.TemporaryDirectory(prefix="cordis-release-process-") as temporary:
            root = Path(temporary)
            ready = root / "ready"
            fake = root / "fake-verus"
            fake.write_text(f"#!{sys.executable}\n" + """import os,signal,sys,time
from pathlib import Path
child=os.fork()
if child==0:
    signal.signal(signal.SIGTERM,signal.SIG_IGN)
    while True: time.sleep(10)
def stop(_signal,_frame):
    os.kill(child,signal.SIGKILL)
    os.waitpid(child,0)
    sys.exit(143)
signal.signal(signal.SIGTERM,stop)
Path(os.environ['READY']).write_text(f'{os.getpid()} {child}')
while True: time.sleep(10)
""")
            fake.chmod(0o755)
            source = root / "lib.rs"
            source.write_text("test source")
            negative = root / "negative.py"
            negative.write_text(f"""import importlib.util,os
from pathlib import Path
spec=importlib.util.spec_from_file_location('checks',{str(SCRIPT.parent / 'check-negative.py')!r})
checks=importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
with checks.ProcessSupervisor().signal_handlers() as supervisor:
    checks.run_verus({str(fake)!r},os.environ.copy(),Path({str(source)!r}),Path({str(root / 'stage')!r}),supervisor=supervisor)
""")
            wrapper = root / "release.py"
            wrapper.write_text(f"""import importlib.util,os,sys
from pathlib import Path
spec=importlib.util.spec_from_file_location('record',{str(SCRIPT)!r})
record=importlib.util.module_from_spec(spec)
spec.loader.exec_module(record)
try:
    record.run_checks([sys.executable,{str(negative)!r}],os.environ.copy(),Path({str(root / 'checks.log')!r}))
except RuntimeError:
    raise SystemExit(7)
raise AssertionError('signal did not cancel the release recorder')
""")
            process = subprocess.Popen([sys.executable, str(wrapper)], env={**os.environ, "READY": str(ready)},
                                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            try:
                deadline = time.monotonic() + 8
                while (not ready.exists() or not ready.stat().st_size) and time.monotonic() < deadline:
                    time.sleep(0.02)
                self.assertTrue(ready.exists(), "nested process did not start")
                leader, child = map(int, ready.read_text().split())
                process.send_signal(signal.SIGTERM)
                time.sleep(0.05)
                process.send_signal(signal.SIGTERM)
                stdout, stderr = process.communicate(timeout=8)
                self.assertEqual(process.returncode, 7, stdout + stderr)
                for pid in (leader, child):
                    with self.assertRaises(ProcessLookupError):
                        os.kill(pid, 0)
                metadata = json.loads((root / "stage.meta.json").read_text())
                self.assertEqual(metadata["status"], "cancelled",
                                 json.dumps(metadata, indent=2) + "\n" + (root / "checks.log").read_text())
            finally:
                if process.poll() is None:
                    process.kill()
                    process.wait()

if __name__ == "__main__":
    unittest.main()
