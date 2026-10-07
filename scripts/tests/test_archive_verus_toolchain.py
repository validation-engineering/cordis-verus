"""Offline recovery tests for immutable Verus Actions provenance and ZIP bytes."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import stat
import tempfile
import unittest
from unittest import mock
import warnings
import zipfile

SCRIPT = Path(__file__).resolve().parents[1] / "archive-verus-toolchain.py"
SPEC = importlib.util.spec_from_file_location("archive_verus_toolchain", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class RecoveryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="verus-recovery-test ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.payload = b"exact original release ZIP bytes"
        self.digest = hashlib.sha256(self.payload).hexdigest()
        self.platform = "arm64-macos"
        self.member = "verus-arm64-macos.zip"
        self.manifest = {
            "schema_version": 1,
            "repository": "verus-lang/verus",
            "run_id": 12,
            "commit": "a" * 40,
            "artifacts": {self.platform: {"id": 34, "name": "verus-arm64-macos", "member": self.member}},
        }
        self.lock = {"verus": {"version": "pinned", "commit": "a" * 40,
                               "assets": {self.platform: {"archive": "verus-pinned-arm64-macos.zip",
                                                          "sha256": self.digest}}}}
        self.run = {"id": 12, "head_sha": "a" * 40, "status": "completed", "conclusion": "success",
                    "repository": {"full_name": "verus-lang/verus"}}
        self.artifact = {"id": 34, "name": "verus-arm64-macos", "expired": False,
                         "workflow_run": {"id": 12, "head_sha": "a" * 40},
                         "created_at": "2026-10-04T00:00:00Z", "expires_at": "2027-01-02T00:00:00Z"}

    def wrapper(self, path, entries=None):
        entries = [(self.member, self.payload)] if entries is None else entries
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as archive:
                for name, contents in entries:
                    archive.writestr(name, contents)

    def test_manifest_covers_exact_locked_platforms_and_commit(self):
        MODULE.validate_manifest(self.manifest, self.lock)
        for replacement in ({"commit": "b" * 40}, {"repository": "other/verus"},
                            {"schema_version": 2}, {"run_id": 0}, {"artifacts": {}}):
            with self.subTest(replacement=replacement):
                with self.assertRaises(MODULE.RecoveryError):
                    MODULE.validate_manifest(dict(self.manifest, **replacement), self.lock)

    def test_manifest_rejects_arbitrary_members_and_output_paths(self):
        for member in ("../verus-arm64-macos.zip", "inner/verus-arm64-macos.zip", "verus-x86-linux.zip"):
            with self.subTest(member=member):
                manifest = copy.deepcopy(self.manifest)
                manifest["artifacts"][self.platform]["member"] = member
                with self.assertRaises(MODULE.RecoveryError):
                    MODULE.validate_manifest(manifest, self.lock)
        lock = copy.deepcopy(self.lock)
        lock["verus"]["assets"][self.platform]["archive"] = "../outside.zip"
        with self.assertRaises(MODULE.RecoveryError):
            MODULE.validate_manifest(self.manifest, lock)

    def test_run_requires_success_and_exact_repository_run_commit(self):
        MODULE.validate_run(self.run, self.manifest)
        for replacement in ({"id": 13}, {"head_sha": "b" * 40}, {"status": "in_progress"},
                            {"conclusion": "failure"}, {"repository": {"full_name": "other/verus"}}):
            with self.subTest(replacement=replacement):
                with self.assertRaises(MODULE.RecoveryError):
                    MODULE.validate_run(dict(self.run, **replacement), self.manifest)

    def test_artifact_requires_exact_identity_run_commit_and_unexpired(self):
        expected = self.manifest["artifacts"][self.platform]
        MODULE.validate_artifact(self.artifact, expected, self.manifest)
        for replacement in ({"id": 35}, {"name": "other"}, {"expired": True}, {"expired": None},
                            {"workflow_run": {"id": 13, "head_sha": "a" * 40}},
                            {"workflow_run": {"id": 12, "head_sha": "b" * 40}}):
            with self.subTest(replacement=replacement):
                with self.assertRaises(MODULE.RecoveryError):
                    MODULE.validate_artifact(dict(self.artifact, **replacement), expected, self.manifest)

    def test_only_exact_member_is_copied_without_extracting_other_entries(self):
        wrapper = self.root / "wrapper.zip"
        destination = self.root / "original.zip"
        self.wrapper(wrapper, [("../../outside", b"ignored"), (self.member, self.payload)])
        size = MODULE.recover_member(wrapper, self.member, destination, self.digest)
        self.assertEqual(destination.read_bytes(), self.payload)
        self.assertEqual(size, len(self.payload))
        self.assertFalse((self.root.parent / "outside").exists())
        self.assertEqual({path.name for path in self.root.iterdir()}, {"wrapper.zip", "original.zip"})

    def test_checksum_mismatch_leaves_existing_destination_untouched(self):
        wrapper = self.root / "wrapper.zip"
        destination = self.root / "original.zip"
        destination.write_bytes(b"old archive")
        self.wrapper(wrapper, [(self.member, b"changed bytes")])
        with self.assertRaisesRegex(MODULE.RecoveryError, "checksum mismatch"):
            MODULE.recover_member(wrapper, self.member, destination, self.digest)
        self.assertEqual(destination.read_bytes(), b"old archive")
        self.assertFalse(list(self.root.glob("*.partial")))

    def test_missing_duplicate_or_symlink_member_is_rejected(self):
        wrapper = self.root / "wrapper.zip"
        symlink = zipfile.ZipInfo(self.member)
        symlink.create_system = 3
        symlink.external_attr = (stat.S_IFLNK | 0o777) << 16
        for entries in ([("elsewhere.zip", self.payload)],
                        [(self.member, self.payload), (self.member, self.payload)],
                        [(symlink, self.payload)]):
            with self.subTest(entries=repr(entries)):
                self.wrapper(wrapper, entries)
                with self.assertRaises(MODULE.RecoveryError):
                    MODULE.recover_member(wrapper, self.member, self.root / "output.zip", self.digest)
                self.assertFalse((self.root / "output.zip").exists())

    def test_recovery_emits_source_bound_provenance_and_original_archive_name(self):
        output = self.root / "output"

        def api(endpoint):
            return self.run if "/actions/runs/" in endpoint else self.artifact

        def download(repository, artifact_id, path):
            self.assertEqual((repository, artifact_id), ("verus-lang/verus", 34))
            self.wrapper(path)

        with mock.patch.object(MODULE, "github_json", side_effect=api):
            with mock.patch.object(MODULE, "download_artifact", side_effect=download):
                with mock.patch("builtins.print"):
                    result = MODULE.recover(self.manifest, self.lock, output)
        archive = self.lock["verus"]["assets"][self.platform]["archive"]
        self.assertEqual((output / archive).read_bytes(), self.payload)
        provenance = json.loads((output / "provenance.json").read_text())
        self.assertEqual(provenance, result)
        self.assertEqual(provenance["commit"], self.manifest["commit"])
        self.assertEqual(provenance["artifacts"][self.platform]["sha256"], self.digest)
        self.assertEqual(provenance["artifacts"][self.platform]["id"], 34)
        self.assertEqual(provenance["artifacts"][self.platform]["bytes"], len(self.payload))
        self.assertEqual({path.name for path in output.iterdir()}, {archive, "provenance.json"})
        self.assertFalse(list(self.root.glob("verus-recovery-*")))

    def test_one_invalid_platform_publishes_no_partial_recovery(self):
        output = self.root / "output"
        manifest = copy.deepcopy(self.manifest)
        manifest["artifacts"]["x86-linux"] = {"id": 35, "name": "verus-x86-linux", "member": "verus-x86-linux.zip"}
        lock = copy.deepcopy(self.lock)
        lock["verus"]["assets"]["x86-linux"] = {"archive": "verus-pinned-x86-linux.zip", "sha256": self.digest}

        def recover(platform, expected, asset, source, staging):
            if platform == "x86-linux":
                raise MODULE.RecoveryError("wrong bytes")
            archive = staging / asset["archive"]
            archive.write_bytes(self.payload)
            return platform, archive, {}

        with mock.patch.object(MODULE, "github_json", return_value=self.run):
            with mock.patch.object(MODULE, "recover_platform", side_effect=recover):
                with self.assertRaisesRegex(MODULE.RecoveryError, "wrong bytes"):
                    MODULE.recover(manifest, lock, output)
        self.assertFalse(output.exists())
        self.assertFalse(list(self.root.glob("verus-recovery-*")))

    def test_existing_output_is_rejected_before_network_access(self):
        output = self.root / "output"
        output.mkdir()
        for populated in (False, True):
            with self.subTest(populated=populated):
                if populated:
                    (output / "provenance.json").write_text("existing evidence")
                    (output / "extra.zip").write_bytes(b"unrelated archive")
                with mock.patch.object(MODULE, "github_json") as api:
                    with self.assertRaisesRegex(MODULE.RecoveryError, "output already exists"):
                        MODULE.recover(self.manifest, self.lock, output)
                api.assert_not_called()
                if populated:
                    self.assertEqual((output / "provenance.json").read_text(), "existing evidence")
                    self.assertEqual((output / "extra.zip").read_bytes(), b"unrelated archive")

    def test_final_directory_rename_failure_leaves_no_partial_output(self):
        output = self.root / "output"

        def recover(platform, expected, asset, source, staging):
            archive = staging / asset["archive"]
            archive.write_bytes(self.payload)
            return platform, archive, {}

        with mock.patch.object(MODULE, "github_json", return_value=self.run):
            with mock.patch.object(MODULE, "recover_platform", side_effect=recover):
                with mock.patch.object(Path, "rename", side_effect=OSError("simulated publication failure")):
                    with self.assertRaisesRegex(OSError, "simulated publication"):
                        MODULE.recover(self.manifest, self.lock, output)
        self.assertFalse(output.exists())
        self.assertFalse(list(self.root.glob("verus-recovery-*")))


if __name__ == "__main__":
    unittest.main()
