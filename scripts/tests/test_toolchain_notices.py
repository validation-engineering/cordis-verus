import importlib.util
import io
from pathlib import Path
import tarfile
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "toolchain_notices", Path(__file__).resolve().parents[1] / "toolchain-notices.py")
NOTICES = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(NOTICES)


class ToolchainNoticeTests(unittest.TestCase):
    def test_rejects_wrong_pinned_revision(self):
        source = Path("/source")
        with patch.object(NOTICES, "command", side_effect=["/source\n", "wrong\n"]):
            with self.assertRaisesRegex(ValueError, "HEAD does not match"):
                NOTICES.validate_source(source, "expected")

    def test_rejects_dirty_source(self):
        with patch.object(NOTICES, "command", side_effect=["/source\n", "expected\n", " M LICENSE\n"]):
            with self.assertRaisesRegex(ValueError, "must be clean"):
                NOTICES.validate_source(Path("/source"), "expected")

    def test_refuses_existing_output_without_modification(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "existing"
            output.mkdir()
            marker = output / "keep.txt"
            marker.write_text("keep")
            args = SimpleNamespace(source=Path(temporary), output=output)
            with self.assertRaisesRegex(ValueError, "refusing to overwrite"):
                NOTICES.collect(args, {})
            self.assertEqual(marker.read_text(), "keep")

    def test_rejects_archive_path_traversal_and_links(self):
        with tempfile.TemporaryDirectory() as temporary:
            temporary = Path(temporary)
            destination = temporary / "destination"
            destination.mkdir()
            for name, link in [("../escape", False), ("linked", True)]:
                archive = temporary / "test.tar"
                with tarfile.open(archive, "w") as stream:
                    member = tarfile.TarInfo(name)
                    if link:
                        member.type = tarfile.SYMTYPE
                        member.linkname = "/etc/passwd"
                        stream.addfile(member)
                    else:
                        member.size = 4
                        stream.addfile(member, io.BytesIO(b"data"))
                with self.assertRaises(ValueError):
                    NOTICES.extract_source(archive, destination)
            self.assertFalse((temporary / "escape").exists())

    def test_extracts_regular_files_in_nested_directories(self):
        with tempfile.TemporaryDirectory() as temporary:
            temporary = Path(temporary)
            destination = temporary / "destination"
            destination.mkdir()
            archive = temporary / "test.tar"
            with tarfile.open(archive, "w") as stream:
                member = tarfile.TarInfo("nested/LICENSE")
                member.size = 4
                stream.addfile(member, io.BytesIO(b"data"))
            NOTICES.extract_source(archive, destination)
            self.assertEqual((destination / "nested/LICENSE").read_bytes(), b"data")

    def test_preserves_nested_notice_candidates_and_reports_absence(self):
        with tempfile.TemporaryDirectory() as temporary:
            stage = Path(temporary)
            package_dir = stage / "vendor/example-1.0.0"
            package_dir.mkdir(parents=True)
            (package_dir / "Cargo.toml").write_text("")
            nested = package_dir / "native/third-party"
            nested.mkdir(parents=True)
            (nested / "COPYING.txt").write_text("nested license text")
            package = {"name": "example", "version": "1.0.0", "source": "registry+example",
                       "license": "MIT", "manifest_path": "/registry/example/Cargo.toml"}
            record = NOTICES.package_record(package, Path("/source"), stage)
            self.assertEqual(record["noticeFiles"], ["vendor/example-1.0.0/native/third-party/COPYING.txt"])
            self.assertFalse(record["missingExplicitNoticeText"])
            (nested / "COPYING.txt").unlink()
            self.assertTrue(NOTICES.package_record(package, Path("/source"), stage)["missingExplicitNoticeText"])


if __name__ == "__main__":
    unittest.main()
