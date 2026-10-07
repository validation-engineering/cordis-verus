"""Pinned archive recovery and safe toolchain replacement, without network access."""
import contextlib
import hashlib
import importlib.util
import io
from pathlib import Path
import stat
import subprocess
import tempfile
import unittest
from unittest import mock
import zipfile

SCRIPT = Path(__file__).resolve().parents[1] / "install-verus.py"
SPEC = importlib.util.spec_from_file_location("install_verus", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class InstallerTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="cordis-verus-installer-test ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.downloads = self.root / "downloads"
        self.downloads.mkdir()
        self.payload = b"original pinned archive bytes"
        self.asset = {
            "archive": "verus-pinned.zip",
            "directory": "verus-test",
            "sha256": hashlib.sha256(self.payload).hexdigest(),
            "url": "https://upstream.invalid/verus.zip",
            "mirror_url": "https://mirror.invalid/verus.zip",
        }
        self.archive = self.downloads / self.asset["archive"]
        self.diagnostics = io.StringIO()
        diagnostics_context = contextlib.redirect_stderr(self.diagnostics)
        diagnostics_context.__enter__()
        self.addCleanup(diagnostics_context.__exit__, None, None, None)

    def downloader(self, responses):
        def download(*arguments):
            self.assertEqual(arguments[0], "curl")
            self.assertIn("--fail", arguments)
            self.assertEqual(arguments[arguments.index("--proto") + 1], "=https")
            response = responses[arguments[-1]]
            partial = Path(arguments[arguments.index("--output") + 1])
            if isinstance(response, BaseException):
                partial.write_bytes(b"interrupted transfer")
                raise response
            partial.write_bytes(response)
        return mock.patch.object(MODULE, "run", side_effect=download)

    def test_verified_cache_requires_no_download(self):
        self.archive.write_bytes(self.payload)
        with mock.patch.object(MODULE, "run") as run:
            self.assertEqual(MODULE.ensure_archive(self.asset, self.downloads), self.archive)
        run.assert_not_called()

    def test_mirror_is_preferred_and_only_verified_bytes_enter_cache(self):
        with self.downloader({self.asset["mirror_url"]: self.payload}) as run:
            MODULE.ensure_archive(self.asset, self.downloads)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(self.archive.read_bytes(), self.payload)
        self.assertEqual(list(self.downloads.iterdir()), [self.archive])

    def test_original_url_still_works_without_mirror_field(self):
        del self.asset["mirror_url"]
        with self.downloader({self.asset["url"]: self.payload}) as run:
            MODULE.ensure_archive(self.asset, self.downloads)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(self.archive.read_bytes(), self.payload)

    def test_failed_or_corrupt_mirror_falls_back_to_original(self):
        for failure in (subprocess.CalledProcessError(22, "curl"), b"wrong archive"):
            with self.subTest(failure=repr(failure)):
                self.archive.unlink(missing_ok=True)
                with self.downloader({self.asset["mirror_url"]: failure,
                                      self.asset["url"]: self.payload}) as run:
                    MODULE.ensure_archive(self.asset, self.downloads)
                self.assertEqual([call.args[-1] for call in run.call_args_list],
                                 [self.asset["mirror_url"], self.asset["url"]])
                self.assertEqual(self.archive.read_bytes(), self.payload)

    def test_all_sources_fail_without_replacing_existing_cache(self):
        self.archive.write_bytes(b"old cache")
        with self.downloader({self.asset["mirror_url"]: b"wrong mirror",
                              self.asset["url"]: subprocess.CalledProcessError(22, "curl")}):
            with self.assertRaisesRegex(MODULE.InstallError, "No checksum-verified"):
                MODULE.ensure_archive(self.asset, self.downloads)
        self.assertEqual(self.archive.read_bytes(), b"old cache")
        self.assertEqual(list(self.downloads.iterdir()), [self.archive])

    def test_interrupted_transfer_leaves_no_cache_or_partial(self):
        with self.downloader({self.asset["mirror_url"]: KeyboardInterrupt()}):
            with self.assertRaises(KeyboardInterrupt):
                MODULE.ensure_archive(self.asset, self.downloads)
        self.assertEqual(list(self.downloads.iterdir()), [])

    def test_duplicate_source_is_tried_only_once(self):
        self.asset["mirror_url"] = self.asset["url"]
        with self.downloader({self.asset["url"]: b"wrong archive"}) as run:
            with self.assertRaises(MODULE.InstallError):
                MODULE.ensure_archive(self.asset, self.downloads)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(list(self.downloads.iterdir()), [])

    def test_private_mirror_uses_api_bytes_with_the_same_hash(self):
        self.asset["mirror_api"] = "repos/example/project/releases/assets/123"

        def fetch(arguments, **options):
            self.assertEqual(arguments, ["/test/gh", "api", "--hostname", "github.com", "-H",
                                         "Accept: application/octet-stream", self.asset["mirror_api"]])
            self.assertTrue(options["check"])
            options["stdout"].write(self.payload)

        with mock.patch.object(MODULE.shutil, "which", return_value="/test/gh"):
            with mock.patch.object(MODULE.subprocess, "run", side_effect=fetch) as run:
                MODULE.ensure_archive(self.asset, self.downloads)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(self.archive.read_bytes(), self.payload)

    def test_corrupt_api_bytes_fall_back_to_hash_verified_url(self):
        self.asset["mirror_api"] = "repos/example/project/releases/assets/123"

        def corrupt_api(endpoint, partial):
            partial.write_bytes(b"wrong private archive")

        with mock.patch.object(MODULE, "download_api_asset", side_effect=corrupt_api):
            with self.downloader({self.asset["mirror_url"]: self.payload}) as run:
                MODULE.ensure_archive(self.asset, self.downloads)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(self.archive.read_bytes(), self.payload)

    def test_no_github_cli_still_allows_public_mirror(self):
        self.asset["mirror_api"] = "repos/example/project/releases/assets/123"
        with mock.patch.object(MODULE.shutil, "which", return_value=None):
            with self.downloader({self.asset["mirror_url"]: self.payload}):
                MODULE.ensure_archive(self.asset, self.downloads)
        self.assertEqual(self.archive.read_bytes(), self.payload)

    def test_api_endpoint_is_restricted_to_github_release_assets(self):
        for endpoint in ("https://example.invalid/token", "repos/a/b/issues/1",
                         "repos/a/b/releases/assets/1?query=secret", "repos/a/b/releases/assets/-1"):
            with self.subTest(endpoint=endpoint):
                with mock.patch.object(MODULE.subprocess, "run") as run:
                    with self.assertRaisesRegex(MODULE.InstallError, "Invalid GitHub"):
                        MODULE.download_api_asset(endpoint, self.root / "partial")
                run.assert_not_called()

    def make_zip(self, extra_entries=(), binary=True):
        entries = list(extra_entries)
        if binary:
            entry = zipfile.ZipInfo(self.asset["directory"] + "/verus")
            entry.create_system = 3
            entry.external_attr = (stat.S_IFREG | 0o755) << 16
            entries.append((entry, b"#!/bin/sh\nexit 0\n"))
        with zipfile.ZipFile(self.archive, "w") as bundle:
            for entry, contents in entries:
                bundle.writestr(entry, contents)
        self.asset["sha256"] = MODULE.digest(self.archive)

    def old_installation(self):
        destination = self.root / self.asset["directory"]
        destination.mkdir()
        (destination / "verus").write_bytes(b"old usable binary")
        (destination / "verus").chmod(0o755)
        return destination

    def test_extract_rejects_traversal_links_and_special_files(self):
        symlink = zipfile.ZipInfo(self.asset["directory"] + "/link")
        symlink.create_system = 3
        symlink.external_attr = (stat.S_IFLNK | 0o777) << 16
        fifo = zipfile.ZipInfo(self.asset["directory"] + "/pipe")
        fifo.create_system = 3
        fifo.external_attr = (stat.S_IFIFO | 0o600) << 16
        destination = self.old_installation()
        for entry in ("../outside", "/absolute", "dir\\outside", symlink, fifo):
            with self.subTest(entry=str(entry)):
                self.make_zip([(entry, b"unsafe")])
                with self.assertRaises(MODULE.InstallError):
                    MODULE.extract_archive(self.archive, self.asset, self.root)
                self.assertEqual((destination / "verus").read_bytes(), b"old usable binary")
                self.assertFalse((self.root.parent / "outside").exists())
        self.assertFalse(list(self.root.glob("verus-extract-*")))

    def test_extract_rejects_duplicate_normalized_paths(self):
        self.make_zip([("verus-test/extra", b"one"), ("verus-test/./extra", b"two")])
        with self.assertRaisesRegex(MODULE.InstallError, "duplicate"):
            MODULE.extract_archive(self.archive, self.asset, self.root)

    def test_missing_binary_preserves_old_installation(self):
        destination = self.old_installation()
        self.make_zip(binary=False)
        with self.assertRaisesRegex(MODULE.InstallError, "expected executable"):
            MODULE.extract_archive(self.archive, self.asset, self.root)
        self.assertEqual((destination / "verus").read_bytes(), b"old usable binary")

    def test_valid_installation_has_executable_binary_and_matching_stamp(self):
        destination = self.old_installation()
        self.make_zip()
        self.assertEqual(MODULE.extract_archive(self.archive, self.asset, self.root), destination)
        self.assertEqual((destination / "verus").read_bytes(), b"#!/bin/sh\nexit 0\n")
        self.assertEqual((destination / "verus").stat().st_mode & 0o777, 0o755)
        self.assertEqual((destination / ".cordis-sha256").read_text().strip(), self.asset["sha256"])
        self.assertFalse(list(self.root.glob("verus-extract-*")))

    def test_failed_installation_rename_restores_previous_binary(self):
        destination = self.old_installation()
        self.make_zip()
        rename = Path.rename

        def fail_new_installation(source, target):
            if source.name == self.asset["directory"] and source.parent.name.startswith("verus-extract-"):
                raise OSError("simulated installation rename failure")
            return rename(source, target)

        with mock.patch.object(Path, "rename", fail_new_installation):
            with self.assertRaisesRegex(OSError, "simulated installation"):
                MODULE.extract_archive(self.archive, self.asset, self.root)
        self.assertEqual((destination / "verus").read_bytes(), b"old usable binary")

    def test_interrupted_installation_rename_restores_previous_binary(self):
        destination = self.old_installation()
        self.make_zip()
        rename = Path.rename

        def interrupt_new_installation(source, target):
            if source.name == self.asset["directory"] and source.parent.name.startswith("verus-extract-"):
                raise KeyboardInterrupt()
            return rename(source, target)

        with mock.patch.object(Path, "rename", interrupt_new_installation):
            with self.assertRaises(KeyboardInterrupt):
                MODULE.extract_archive(self.archive, self.asset, self.root)
        self.assertEqual((destination / "verus").read_bytes(), b"old usable binary")
        self.assertFalse(list(self.root.glob("verus-backup-*")))

    def test_failed_rollback_preserves_old_binary_outside_staging_and_reports_path(self):
        self.old_installation()
        self.make_zip()
        rename = Path.rename

        def fail_installation_and_rollback(source, target):
            if source.parent.name.startswith(("verus-extract-", "verus-backup-")):
                raise OSError("simulated rename failure")
            return rename(source, target)

        with mock.patch.object(Path, "rename", fail_installation_and_rollback):
            with self.assertRaisesRegex(MODULE.InstallError, "previous installation is preserved at") as error:
                MODULE.extract_archive(self.archive, self.asset, self.root)
        backups = list(self.root.glob("verus-backup-*/verus-test"))
        self.assertEqual(len(backups), 1)
        self.assertEqual((backups[0] / "verus").read_bytes(), b"old usable binary")
        self.assertIn(str(backups[0]), str(error.exception))
        self.assertFalse(list(self.root.glob("verus-extract-*")))

    def test_stamp_without_binary_does_not_skip_installation(self):
        destination = self.root / self.asset["directory"]
        destination.mkdir()
        self.make_zip()
        (destination / ".cordis-sha256").write_text(self.asset["sha256"] + "\n")
        with mock.patch.object(MODULE, "run") as run:
            MODULE.install_asset(self.asset, self.root)
        run.assert_not_called()
        self.assertTrue((destination / "verus").is_file())


if __name__ == "__main__":
    unittest.main()
