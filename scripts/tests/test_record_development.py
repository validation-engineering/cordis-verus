"""Development evidence regressions; no compiler or verifier processes are run."""
from contextlib import contextmanager
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import MagicMock, call, patch

SCRIPT = Path(__file__).parents[1] / "record-development.py"
PROJECT = SCRIPT.parent.parent
spec = importlib.util.spec_from_file_location("development_record", SCRIPT)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class DevelopmentEvidenceTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="cordis-development-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for name in module.FIXED_SCRIPTS:
            destination = self.root / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(PROJECT / name, destination)
        (self.root / "crates/cordis/examples").mkdir(parents=True)
        (self.root / "crates/cordis/examples/demo.rs").write_text("fn main() {}\n")
        self.record = self.root / "docs/development-report.json"
        self.record.parent.mkdir()
        self.record.write_text(json.dumps({"schema": module.SCHEMA, "status": "passed", "sha256": {"stale": "old"}}))
        self.packages = self.root / "target/release-artifacts/package-report.json"
        self.packages.parent.mkdir(parents=True)
        self.npm_report = self.root / "target/release-artifacts/npm/package-report.json"
        self.npm_report.parent.mkdir(parents=True)
        self.node_build = self.root / "target/node-compat/build.json"
        self.node_build.parent.mkdir(parents=True)
        self.native_artifact = self.root / "packages/compat-cordis/native/cordis.node"
        self.native_artifact.parent.mkdir(parents=True)
        self.native_artifact.write_bytes(b"native-test-artifact")
        self.interop_fixture = self.root / "target/node-compat/interop-fixture.node"
        self.interop_fixture.write_bytes(b"custom-rust-factory-addon")
        self.interop_source = self.root / "crates/cordis-node/examples/interop_fixture.rs"
        self.interop_source.parent.mkdir(parents=True)
        self.interop_source.write_text("// independently compiled Rust factory fixture\n")
        self.cordis_source = self.root / "crates/cordis/src/runtime.rs"
        self.cordis_source.parent.mkdir(parents=True)
        self.cordis_source.write_text("// actual typed Runtime dependency\n")
        (self.root / "Cargo.lock").write_text("test cargo lock")
        (self.root / "toolchain.lock.json").write_text("test toolchain lock")
        for name in ("Cargo.toml", "package.json", "package-lock.json", "LICENSE", "NOTICE"):
            (self.root / name).write_text("test " + name)
        for name in ("cordis-kernel", "cordis-driver", "cordis", "cordis-node", "cordis-plugin-api"):
            directory = self.root / "crates" / name
            directory.mkdir(parents=True, exist_ok=True)
            (directory / "Cargo.toml").write_text("test " + name)
        for directory, name in module.NPM_PACKAGES.items():
            package = self.root / "packages" / directory
            package.mkdir(parents=True, exist_ok=True)
            (package / "package.json").write_text(json.dumps({"name": name, "version": "0.1.0"}))
            for filename in ("index.js", "index.d.ts", "README.md", "native-artifacts.js"):
                (package / filename).write_text("test " + filename)
        self.events = []
        self.addCleanup(patch.stopall)
        patch.object(module, "ROOT", self.root).start()
        patch.object(module, "RECORD", self.record).start()
        patch.object(module, "verifier_lease", self.lease).start()
        patch.dict(os.environ, {}, clear=True).start()

    @contextmanager
    def lease(self):
        self.events.append("lock")
        try:
            yield
        finally:
            self.events.append("unlock")

    def log(self):
        return "\n".join([
            "verification results:: 2227 verified, 0 errors",
            module.WORKSPACE_BEGIN,
            "Running tests/lifecycle.rs (target/lifecycle)",
            "test result: ok. 4 passed; 0 failed;",
            "Doc-tests cordis", "test result: ok. 2 passed; 0 failed;",
            module.WORKSPACE_END,
            module.NODE_BEGIN,
            "TAP version 13", "1..3", "# tests 3", "# suites 0",
            "# pass 3", "# fail 0", "# cancelled 0", "# skipped 0", "# todo 0",
            module.NODE_END,
            "Running tests/lifecycle.rs (extracted/lifecycle)",
            "test result: ok. 99 passed; 0 failed;",
            module.MARKER,
        ])

    def successful_checks(self, command, environment, log):
        self.assertFalse(self.packages.exists(), "a stale package report survived preflight")
        self.assertFalse(self.node_build.exists(), "a stale Node build report survived preflight")
        self.assertFalse(self.npm_report.exists(), "a stale npm distribution report survived preflight")
        self.assertEqual(command, ["./scripts/check-development.sh", "--offline"])
        self.assertEqual(environment["CORDIS_VERUS_THREADS"], "2")
        self.assertEqual(environment["CARGO_NET_OFFLINE"], "true")
        self.assertEqual(json.loads(self.record.read_text())["status"], "running")
        log.write_text(self.log())
        self.packages.write_text(json.dumps({"registry_publish_checked": False, "packages": ["fresh"]}))
        files = {"artifactSha256": self.native_artifact, "cargoLockSha256": self.root / "Cargo.lock",
                 "toolchainLockSha256": self.root / "toolchain.lock.json"}
        host_platform = {"Darwin": "darwin", "Linux": "linux", "Windows": "win32"}[module.platform.system()]
        host_arch = {"aarch64": "arm64", "arm64": "arm64", "x86_64": "x64", "AMD64": "x64"}[module.platform.machine()]
        build = {"schema": "cordis-verus.node-build/v1", "platform": host_platform,
                 "interopFixture": {"path": "target/node-compat/interop-fixture.node",
                                    "sha256": module.file_sha256(self.interop_fixture)},
                 "architecture": host_arch, "node": "v22.22.0", "sourceHashes": module.native_source_hashes(),
                 **{name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in files.items()}}
        extension = {"darwin": ".dylib", "linux": ".so", "win32": ".dll"}[host_platform]
        build["dynamicFixtures"] = {}
        for version in ("v1", "v2", "fail"):
            relative = "target/node-compat/dynamic-fixture-" + version + extension
            artifact = self.root / relative
            artifact.write_bytes(("dynamic " + version).encode())
            build["dynamicFixtures"][version] = {"path": relative, "sha256": module.file_sha256(artifact)}
        self.node_build.write_text(json.dumps(build))
        native_target = host_platform + "-" + host_arch + ("-gnu" if host_platform == "linux" else "") + "-napi8"
        native_provenance = "provenance/" + native_target + ".json"
        provenance_path = self.native_artifact.parent / native_provenance
        provenance_path.parent.mkdir(exist_ok=True)
        provenance_path.write_text(json.dumps({"build": {"reportSha256": module.file_sha256(self.node_build),
                                                        "sourceHashes": build["sourceHashes"]}}))
        manifest_path = self.native_artifact.parent / "manifest.json"
        manifest_path.write_text(json.dumps({"schema": "cordis-verus.native-manifest/v1", "artifacts": [{
            "target": native_target, "platform": host_platform, "architecture": host_arch,
            "file": "cordis.node", "sha256": build["artifactSha256"], "provenance": native_provenance,
            "provenanceSha256": module.file_sha256(provenance_path)}]}))
        manifest_hash = module.file_sha256(manifest_path)
        packages = []
        for directory, name in module.NPM_PACKAGES.items():
            filename = directory + "-0.1.0.tgz"
            archive = self.npm_report.parent / filename
            archive.write_bytes(("test archive: " + name).encode())
            packages.append({"name": name, "version": "0.1.0", "filename": filename,
                             "sha256": module.file_sha256(archive),
                             "files": ["package.json", "index.js", "index.d.ts", "README.md", "LICENSE", "NOTICE", "native/cordis.node", "native/manifest.json", "native/" + native_provenance] + (["harness.js", "harness.d.ts", "module-graph.js", "process.js", "process.d.ts", "process-entry.js", "domain-entry.js"] if directory == "compat-loader" else [])})
        self.npm_report.write_text(json.dumps({
            "schema": "cordis-verus.npm-package/v1", "status": "passed", "offline": True, "uploaded": False,
            "registryPublishChecked": False, "otherTargets": "not validated", "packages": packages,
            "testedTarget": {"platform": host_platform, "architecture": host_arch, "node": "v22.22.0",
                             "nodeApi": "10", "nodeModuleAbi": "127", "driverAbi": 1},
            "nativeManifestSha256": manifest_hash, "nativeTarget": native_target,
            "buildReportSha256": module.file_sha256(self.node_build), "nativeArtifactSha256": build["artifactSha256"],
            "nativeSourceHashes": build["sourceHashes"], "sourceHashes": module.npm_source_hashes(),
            "observation": {"binding": {"abi": 1}, "nativeManifestSha256": manifest_hash, "nativeTarget": native_target,
                            "tests": ["native-manifest-selection", "default-core-only", "packed-native-load", "ESM-CJS-identity",
                "original-cordis-import", "JSON-loader-update", "Worker-artifact-load", "Process-native-artifact-load", "Rust-module-in-place-reload"]},
            "harnessObservation": {"profile": "harness", "tests": ["scoped-original-import", "ESM-CJS-profile-identity",
                "native-harness-domain", "Service-class", "official-loader-adapter-export"]},
        }))
        return 0

    def read_record(self):
        return json.loads(self.record.read_text())

    def assert_failed(self):
        record = self.read_record()
        self.assertEqual(record["status"], "failed")
        self.assertEqual(record["sha256"], {})
        self.assertFalse(record["releaseAcceptance"])
        self.assertFalse(record["paperCompletion"])
        for name in ("proof", "tests", "packages", "checkedAt", "workflowSha256", "nodeBuild", "npmDistribution", "npmDistributionReportSha256"):
            self.assertNotIn(name, record)

    def test_counts_workspace_without_repeated_package_suites(self):
        proof, tests = module.parse_results(self.log())
        self.assertEqual(proof["verified"], 2227)
        self.assertEqual(tests["total"], 4)
        self.assertEqual(tests["doctestTotal"], 2)
        self.assertNotIn("deterministicTraces", tests)
        self.assertEqual(tests["nodeCompatibility"]["tests"], 3)
        self.assertTrue(tests["nodeCompatibility"]["behavioralTestsOnly"])
        self.assertFalse(tests["nodeCompatibility"]["upstreamDifferentialIncluded"])

    def test_rejects_failed_missing_ambiguous_or_incomplete_checks(self):
        variants = [self.log().replace("0 errors", "1 errors"),
                    self.log().replace("2227 verified", "0 verified"),
                    self.log().replace(module.MARKER, ""),
                    self.log().replace(module.WORKSPACE_BEGIN, ""),
                    self.log() + "\nverification results:: 1 verified, 0 errors",
                    self.log() + "\n" + module.MARKER,
                    self.log().replace(module.WORKSPACE_END, module.WORKSPACE_END + "\n" + module.WORKSPACE_END),
                    self.log().replace("4 passed; 0 failed;", "4 passed; 1 failed;"),
                    self.log().replace("test result: ok. 4 passed", "test result: FAILED. 4 passed"),
                    self.log().replace(module.WORKSPACE_BEGIN, "temporary").replace(module.WORKSPACE_END, module.WORKSPACE_BEGIN).replace("temporary", module.WORKSPACE_END)]
        for log in variants:
            with self.subTest(log=log), self.assertRaises(RuntimeError):
                module.parse_results(log)

    def test_rejects_missing_failed_cancelled_or_skipped_node_tests(self):
        variants = [self.log().replace(module.NODE_BEGIN, ""),
                    self.log().replace(module.NODE_END, module.NODE_END + "\n" + module.NODE_END),
                    self.log().replace("# tests 3", "# tests 0"),
                    self.log().replace("# pass 3", "# pass 2"),
                    self.log().replace("# fail 0", "# fail 1"),
                    self.log().replace("# cancelled 0", "# cancelled 1"),
                    self.log().replace("# skipped 0", "# skipped 1"),
                    self.log().replace("# todo 0", "# todo 1"),
                    self.log().replace("# pass 3", "# pass 3\n# pass 3"),
                    self.log().replace("TAP version 13", "TAP version 13\nnot ok 1 - failed"),
                    self.log().replace("TAP version 13", "TAP version 13\nBail out! crashed")]
        for log in variants:
            with self.subTest(log=log), self.assertRaisesRegex(RuntimeError, "Node"):
                module.parse_results(log)

    def test_native_build_evidence_must_match_current_artifact(self):
        def corrupted(command, environment, log):
            result = self.successful_checks(command, environment, log)
            self.native_artifact.write_bytes(b"replaced native binary")
            return result
        with patch.object(module, "run_checks", side_effect=corrupted), self.assertRaisesRegex(RuntimeError, "Node build evidence"):
            module.record_development(offline=True)
        self.assert_failed()

    def test_native_build_evidence_uses_manifest_selection_in_prebuilt_bundle(self):
        with patch.object(module, "run_checks", side_effect=self.successful_checks):
            module.record_development(offline=True)
        manifest_path = self.native_artifact.parent / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        entry = manifest["artifacts"][0]
        entry["file"] = "prebuilds/" + entry["target"] + "/cordis.node"
        destination = self.native_artifact.parent / entry["file"]
        destination.parent.mkdir(parents=True)
        self.native_artifact.rename(destination)
        manifest_path.write_text(json.dumps(manifest))
        self.assertEqual(module.node_build_evidence(self.node_build)["artifactSha256"], module.file_sha256(destination))
        entry["file"] = "../escape.node"
        manifest_path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(RuntimeError, "unsafe native artifact"):
            module.node_build_evidence(self.node_build)

    def test_interop_fixture_evidence_cannot_be_missing_changed_or_redirected(self):
        mutations = {
            "missing fixture": lambda build: build.pop("interopFixture"),
            "missing digest": lambda build: build["interopFixture"].pop("sha256"),
            "stale digest": lambda build: build["interopFixture"].update(sha256="stale"),
            "other addon": lambda build: build["interopFixture"].update(path="packages/compat-cordis/native/cordis.node"),
            "path escape": lambda build: build["interopFixture"].update(path="../elsewhere.node"),
        }
        for label, mutate in mutations.items():
            def corrupted(command, environment, log):
                result = self.successful_checks(command, environment, log)
                build = json.loads(self.node_build.read_text())
                mutate(build)
                self.node_build.write_text(json.dumps(build))
                return result
            with self.subTest(label=label), patch.object(module, "run_checks", side_effect=corrupted), \
                 self.assertRaisesRegex(RuntimeError, "Rust interop fixture"):
                module.record_development(offline=True)
            self.assert_failed()

    def test_dynamic_fixture_evidence_cannot_be_missing_changed_or_redirected(self):
        mutations = {
            "missing map": lambda build: build.pop("dynamicFixtures"),
            "missing version": lambda build: build["dynamicFixtures"].pop("v2"),
            "unexpected version": lambda build: build["dynamicFixtures"].update(extra={}),
            "missing digest": lambda build: build["dynamicFixtures"]["v1"].pop("sha256"),
            "stale digest": lambda build: build["dynamicFixtures"]["v2"].update(sha256="stale"),
            "path escape": lambda build: build["dynamicFixtures"]["fail"].update(path="../elsewhere.dylib"),
            "other version": lambda build: build["dynamicFixtures"]["v2"].update(path=build["dynamicFixtures"]["v1"]["path"]),
            "missing file": lambda build: (self.root / build["dynamicFixtures"]["v1"]["path"]).unlink(),
            "changed file": lambda build: (self.root / build["dynamicFixtures"]["v2"]["path"]).write_bytes(b"replaced native plugin"),
        }
        for label, mutate in mutations.items():
            def corrupted(command, environment, log):
                result = self.successful_checks(command, environment, log)
                build = json.loads(self.node_build.read_text())
                mutate(build)
                self.node_build.write_text(json.dumps(build))
                return result
            with self.subTest(label=label), patch.object(module, "run_checks", side_effect=corrupted), \
                 self.assertRaisesRegex(RuntimeError, "Dynamic Rust fixture"):
                module.record_development(offline=True)
            self.assert_failed()

    def test_hash_check_rejects_changed_dynamic_plugin_without_running_a_process(self):
        with patch.object(module, "run_checks", side_effect=self.successful_checks):
            module.record_development(offline=True)
        build = json.loads(self.node_build.read_text())
        artifact = self.root / build["dynamicFixtures"]["v2"]["path"]
        artifact.write_bytes(b"changed dynamic code")
        with patch.object(module, "run_checks") as run, self.assertRaisesRegex(RuntimeError, "Dynamic Rust fixture"):
            module.check_record()
        run.assert_not_called()

    def test_node_build_evidence_binds_the_custom_factory_source(self):
        with patch.object(module, "run_checks", side_effect=self.successful_checks):
            module.record_development(offline=True)
        build = json.loads(self.node_build.read_text())
        name = self.interop_source.relative_to(self.root).as_posix()
        self.assertEqual(build["sourceHashes"][name], module.file_sha256(self.interop_source))
        build["sourceHashes"].pop(name)
        self.node_build.write_text(json.dumps(build))
        with self.assertRaisesRegex(RuntimeError, "incomplete native source hashes"):
            module.node_build_evidence(self.node_build)

    def test_changed_cordis_rust_or_manifest_invalidates_native_build_and_distribution(self):
        with patch.object(module, "run_checks", side_effect=self.successful_checks):
            module.record_development(offline=True)
        build = json.loads(self.node_build.read_text())
        for path in (self.cordis_source, self.root / "crates/cordis/Cargo.toml"):
            name = path.relative_to(self.root).as_posix()
            self.assertEqual(build["sourceHashes"][name], module.file_sha256(path))
            original = path.read_bytes()
            try:
                path.write_bytes(original + b"changed typed Rust dependency\n")
                with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, "stale or incomplete native source"):
                    module.node_build_evidence(self.node_build)
                with self.subTest(distribution=name), self.assertRaisesRegex(RuntimeError, "npm distribution input hashes"):
                    module.npm_distribution_evidence(self.npm_report, self.node_build, build)
            finally:
                path.write_bytes(original)
        self.assertEqual(module.node_build_evidence(self.node_build), build)

    def test_hash_check_rejects_changed_custom_addon_without_running_a_process(self):
        with patch.object(module, "run_checks", side_effect=self.successful_checks):
            module.record_development(offline=True)
        self.interop_fixture.write_bytes(b"different custom addon")
        with patch.object(module.subprocess, "Popen", side_effect=AssertionError("hash check must not run checks")), \
             self.assertRaisesRegex(RuntimeError, "Rust interop fixture"):
            module.check_record()

    def test_hash_check_requires_the_local_custom_addon(self):
        with patch.object(module, "run_checks", side_effect=self.successful_checks):
            module.record_development(offline=True)
        self.interop_fixture.unlink()
        with self.assertRaises(FileNotFoundError):
            module.check_record()

    def test_previous_node_build_report_cannot_be_reused(self):
        self.node_build.write_text('{"old":true}')
        def missing(command, environment, log):
            result = self.successful_checks(command, environment, log)
            self.node_build.unlink()
            return result
        with patch.object(module, "run_checks", side_effect=missing), self.assertRaises(FileNotFoundError):
            module.record_development(offline=True)
        self.assert_failed()

    def test_previous_npm_report_cannot_be_reused(self):
        self.npm_report.write_text('{"status":"passed","old":true}')
        def missing(command, environment, log):
            result = self.successful_checks(command, environment, log)
            self.npm_report.unlink()
            return result
        with patch.object(module, "run_checks", side_effect=missing), self.assertRaises(FileNotFoundError):
            module.record_development(offline=True)
        self.assert_failed()

    def test_npm_evidence_rejects_incomplete_promoted_or_stale_report(self):
        mutations = {
            "status": lambda report: report.update(status="failed"),
            "publish": lambda report: report.update(registryPublishChecked=True),
            "upload": lambda report: report.update(uploaded=True),
            "online": lambda report: report.update(offline=False),
            "platform claim": lambda report: report.update(otherTargets="validated"),
            "two packages": lambda report: report["packages"].pop(),
            "duplicate package": lambda report: report["packages"].__setitem__(1, report["packages"][0]),
            "native source": lambda report: report.update(nativeSourceHashes={}),
            "package source": lambda report: report.update(sourceHashes={}),
            "build hash": lambda report: report.update(buildReportSha256="stale"),
            "artifact hash": lambda report: report.update(nativeArtifactSha256="stale"),
            "manifest hash": lambda report: report.update(nativeManifestSha256="stale"),
            "native target": lambda report: report.update(nativeTarget="not-the-host"),
            "installed manifest": lambda report: report["observation"].update(nativeManifestSha256="stale"),
            "SDK addon included": lambda report: report["packages"][0]["files"].append("native/custom.node"),
            "missing manifest": lambda report: report["packages"][0]["files"].remove("native/manifest.json"),
            "wrong host": lambda report: report["testedTarget"].update(platform="other"),
            "wrong Node": lambda report: report["testedTarget"].update(node="v0.0.0"),
            "wrong ABI": lambda report: report["testedTarget"].update(driverAbi=2),
            "missing smoke": lambda report: report["harnessObservation"].update(tests=[]),
            "missing adapter smoke": lambda report: report["harnessObservation"]["tests"].remove("official-loader-adapter-export"),
            "missing adapter file": lambda report: next(item for item in report["packages"] if item["name"] == "@cordis-verus/compat-loader")["files"].remove("harness.js"),
            "missing process smoke": lambda report: report["observation"]["tests"].remove("Process-native-artifact-load"),
            "missing Rust module smoke": lambda report: report["observation"]["tests"].remove("Rust-module-in-place-reload"),
            "missing process entry": lambda report: next(item for item in report["packages"] if item["name"] == "@cordis-verus/compat-loader")["files"].remove("process-entry.js"),
            "missing module graph": lambda report: next(item for item in report["packages"] if item["name"] == "@cordis-verus/compat-loader")["files"].remove("module-graph.js"),
            "missing native": lambda report: report["packages"][0]["files"].remove("native/cordis.node"),
            "wrong version": lambda report: report["packages"][0].update(version="9.0.0"),
            "path escape": lambda report: report["packages"][0].update(filename="../escape.tgz"),
        }
        for label, mutate in mutations.items():
            def corrupted(command, environment, log):
                result = self.successful_checks(command, environment, log)
                report = json.loads(self.npm_report.read_text())
                mutate(report)
                self.npm_report.write_text(json.dumps(report))
                return result
            with self.subTest(label=label), patch.object(module, "run_checks", side_effect=corrupted), \
                 self.assertRaisesRegex(RuntimeError, "npm distribution"):
                module.record_development(offline=True)
            self.assert_failed()

    def test_npm_tarball_tampering_cannot_pass_or_survive_hash_check(self):
        with patch.object(module, "run_checks", side_effect=self.successful_checks):
            module.record_development(offline=True)
        archive = self.npm_report.parent / "compat-loader-0.1.0.tgz"
        archive.write_bytes(b"changed")
        with self.assertRaisesRegex(RuntimeError, "npm distribution package artifact"):
            module.check_record()

    def test_hash_check_rejects_removed_or_changed_saved_npm_evidence(self):
        with patch.object(module, "run_checks", side_effect=self.successful_checks):
            module.record_development(offline=True)
        original = self.read_record()
        for field in ("npmDistribution", "npmDistributionReportSha256"):
            record = dict(original)
            record.pop(field)
            self.record.write_text(json.dumps(record))
            with self.subTest(field=field), self.assertRaisesRegex(RuntimeError, "stale development npm"):
                module.check_record()

    def test_evidence_is_excluded_but_all_workflow_scripts_are_bound(self):
        before = module.source_hashes()
        self.record.write_text('{"status":"running"}\n')
        self.assertEqual(before, module.source_hashes())
        self.assertNotIn("docs/development-report.json", before)
        self.assertEqual(module.workflow_binding(before), {name: before[name] for name in module.FIXED_SCRIPTS})
        changed = dict(before); changed.pop("scripts/verify.sh")
        with self.assertRaisesRegex(RuntimeError, "Missing fixed"):
            module.workflow_binding(changed)
        changed = dict(before); changed["scripts/record-development.py"] = "changed"
        with self.assertRaisesRegex(RuntimeError, "recorder changed"):
            module.workflow_binding(changed)

    def test_fresh_success_is_development_only_and_hash_check_runs_no_process(self):
        self.packages.write_text('{"old":true}')
        with patch.object(module, "run_checks", side_effect=self.successful_checks) as runner:
            result = module.record_development(offline=True)
            self.assertEqual(runner.call_count, 1)
        self.assertEqual(result["status"], "passed")
        self.assertFalse(result["releaseAcceptance"])
        self.assertEqual(result["fullNegativeControls"], "not run by this command")
        self.assertFalse(result["paperCompletion"])
        self.assertEqual(result["tests"]["total"], 4)
        self.assertEqual(result["packages"]["packages"], ["fresh"])
        self.assertEqual(result["npmDistribution"]["status"], "passed")
        self.assertEqual(len(result["npmDistribution"]["packages"]), 3)
        self.assertEqual(self.events, ["lock", "unlock"])
        with patch.object(module.subprocess, "Popen", side_effect=AssertionError("hash check must not run checks")):
            module.check_record()

    def test_hash_check_rejects_promoted_release_or_changed_workflow(self):
        with patch.object(module, "run_checks", side_effect=self.successful_checks):
            module.record_development(offline=True)
        original = self.read_record()
        for name, value in (("releaseAcceptance", True), ("paperCompletion", True),
                            ("fullNegativeControls", "passed"), ("command", ["./scripts/quality.sh"]),
                            ("workflowSha256", {})):
            changed = dict(original); changed[name] = value
            self.record.write_text(json.dumps(changed))
            with self.subTest(name=name), self.assertRaisesRegex(RuntimeError, "stale development"):
                module.check_record()

    def test_source_hashing_failure_invalidates_old_success(self):
        with patch.object(module, "source_hashes", side_effect=OSError("unreadable source")), \
             patch.object(module, "run_checks") as runner, self.assertRaises(OSError):
            module.record_development()
        runner.assert_not_called()
        self.assert_failed()

    def test_unsupported_environment_invalidates_old_success(self):
        with patch.dict(os.environ, {"VERUS_EXTRA_ARGS": "--verify-only-module one"}), \
             patch.object(module, "run_checks") as runner, self.assertRaisesRegex(RuntimeError, "Custom compiler"):
            module.record_development()
        runner.assert_not_called()
        self.assert_failed()

    def test_source_change_during_checks_rejects_success(self):
        def changed(command, environment, log):
            result = self.successful_checks(command, environment, log)
            (self.root / "scripts/verify.sh").write_text("changed workflow")
            return result
        with patch.object(module, "run_checks", side_effect=changed), self.assertRaisesRegex(RuntimeError, "Sources changed"):
            module.record_development(offline=True)
        self.assert_failed()

    def test_previous_package_report_cannot_be_reused(self):
        self.packages.write_text('{"old":true}')
        def missing(_command, _environment, log):
            log.write_text(self.log())
            return 0
        with patch.object(module, "run_checks", side_effect=missing), self.assertRaises(FileNotFoundError):
            module.record_development()
        self.assert_failed()

    def test_nonzero_process_cannot_pass_even_with_complete_log(self):
        def rejected(command, environment, log):
            self.successful_checks(command, environment, log)
            return 1
        with patch.object(module, "run_checks", side_effect=rejected), self.assertRaisesRegex(RuntimeError, "exited 1"):
            module.record_development(offline=True)
        self.assert_failed()

    def test_interrupt_while_waiting_for_lease_records_failure(self):
        @contextmanager
        def interrupted():
            raise KeyboardInterrupt()
            yield
        with patch.object(module, "verifier_lease", interrupted), patch.object(module, "run_checks") as runner, \
             self.assertRaises(KeyboardInterrupt):
            module.record_development()
        runner.assert_not_called()
        self.assert_failed()

    def test_interrupt_after_success_save_removes_passed_fields(self):
        save = module.save_record
        def interrupt(record):
            save(record)
            if record["status"] == "passed":
                raise KeyboardInterrupt()
        with patch.object(module, "save_record", side_effect=interrupt), \
             patch.object(module, "run_checks", side_effect=self.successful_checks), self.assertRaises(KeyboardInterrupt):
            module.record_development(offline=True)
        self.assert_failed()

    def interrupted_process(self, failures):
        process = MagicMock(); process.pid = 12345
        values = iter(failures)
        def wait(*_args, **_kwargs):
            value = next(values)
            if isinstance(value, BaseException):
                self.events.append(type(value).__name__)
                raise value
            self.events.append("reaped")
            return value
        process.wait.side_effect = wait
        def kill(_pid, sig):
            self.assertNotIn("unlock", self.events)
            self.events.append("TERM" if sig == module.signal.SIGTERM else "KILL")
        return process, kill

    def test_interrupt_kills_group_and_reaps_before_lease_release(self):
        process, kill = self.interrupted_process([KeyboardInterrupt(), 0, -9])
        with patch.object(module.subprocess, "Popen", return_value=process) as popen, \
             patch.object(module.os, "killpg", side_effect=kill) as signals, self.assertRaises(KeyboardInterrupt):
            module.record_development()
        self.assertTrue(popen.call_args.kwargs["start_new_session"])
        self.assertEqual(signals.call_args_list, [call(12345, module.signal.SIGTERM), call(12345, module.signal.SIGKILL)])
        # KILL is still sent if the shell exits after TERM: descendants may remain.
        self.assertEqual(self.events, ["lock", "KeyboardInterrupt", "TERM", "reaped", "KILL", "reaped", "unlock"])
        self.assert_failed()

    def test_timeout_escalates_and_reaps_before_releasing_lease(self):
        process, kill = self.interrupted_process([subprocess.TimeoutExpired("checks", 1),
                                                 subprocess.TimeoutExpired("checks", 2), -9])
        with patch.object(module.subprocess, "Popen", return_value=process), \
             patch.object(module.os, "killpg", side_effect=kill), self.assertRaises(subprocess.TimeoutExpired):
            module.record_development()
        self.assertEqual(self.events, ["lock", "TimeoutExpired", "TERM", "TimeoutExpired", "KILL", "reaped", "unlock"])
        self.assert_failed()

    def test_repeated_interrupts_cannot_release_a_live_group(self):
        process, kill = self.interrupted_process([KeyboardInterrupt(), KeyboardInterrupt(), KeyboardInterrupt(), -9])
        with patch.object(module.subprocess, "Popen", return_value=process), \
             patch.object(module.os, "killpg", side_effect=kill), self.assertRaises(KeyboardInterrupt):
            module.record_development()
        self.assertEqual(self.events, ["lock", "KeyboardInterrupt", "TERM", "KeyboardInterrupt", "KILL",
                                      "KeyboardInterrupt", "KILL", "reaped", "unlock"])
        self.assert_failed()

    def test_process_creation_failure_records_failure(self):
        with patch.object(module.subprocess, "Popen", side_effect=OSError("cannot spawn")), self.assertRaises(OSError):
            module.record_development()
        self.assertEqual(self.events, ["lock", "unlock"])
        self.assert_failed()

    def test_term_signal_uses_cleanup_and_restores_handlers(self):
        previous = {sig: module.signal.getsignal(sig) for sig in (module.signal.SIGINT, module.signal.SIGTERM, module.signal.SIGHUP)}
        process = MagicMock(); process.pid = 12345
        calls = 0
        def wait(*_args, **_kwargs):
            nonlocal calls
            calls += 1
            if calls == 1:
                module.signal.getsignal(module.signal.SIGTERM)(module.signal.SIGTERM, None)
            self.events.append("reaped")
            return -9
        process.wait.side_effect = wait
        with patch.object(module.subprocess, "Popen", return_value=process), \
             patch.object(module.os, "killpg") as kill, self.assertRaises(module.TerminationRequested):
            module.record_development()
        self.assertEqual(kill.call_args_list, [call(12345, module.signal.SIGTERM), call(12345, module.signal.SIGKILL)])
        self.assertEqual(self.events, ["lock", "reaped", "reaped", "unlock"])
        self.assertEqual({sig: module.signal.getsignal(sig) for sig in previous}, previous)
        self.assert_failed()

    def test_signal_during_spawn_is_deferred_until_child_pid_can_be_reaped(self):
        process = MagicMock(); process.pid = 12345; process.wait.return_value = -9
        def spawn(*_args, **_kwargs):
            module.signal.getsignal(module.signal.SIGTERM)(module.signal.SIGTERM, None)
            self.events.append("spawn returned")
            return process
        with patch.object(module.subprocess, "Popen", side_effect=spawn), \
             patch.object(module.os, "killpg") as kill, self.assertRaisesRegex(module.TerminationRequested, "while spawning"):
            module.record_development()
        self.assertEqual(kill.call_args_list, [call(12345, module.signal.SIGTERM), call(12345, module.signal.SIGKILL)])
        self.assertEqual(process.wait.call_count, 2)
        self.assertEqual(self.events, ["lock", "spawn returned", "unlock"])
        self.assert_failed()

    def test_interrupted_initial_invalidation_cannot_leave_old_passed(self):
        original = module.save_record
        calls = 0
        def save(record):
            nonlocal calls
            calls += 1
            if calls == 1:
                raise KeyboardInterrupt()
            original(record)
        with patch.object(module, "save_record", side_effect=save), \
             patch.object(module, "run_checks") as runner, self.assertRaises(KeyboardInterrupt):
            module.record_development()
        runner.assert_not_called()
        self.assert_failed()

    def test_atomic_save_leaves_no_temporary_report(self):
        module.save_record({"schema": module.SCHEMA, "status": "running"})
        self.assertEqual(self.read_record()["status"], "running")
        self.assertEqual(list(self.record.parent.glob(".development-report-*.tmp")), [])


if __name__ == "__main__":
    unittest.main()
