"""Regression coverage for extracted dependency patching and archive validation."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "package-check.py"
SPEC = importlib.util.spec_from_file_location("package_check", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class PackageDependencyTests(unittest.TestCase):
    def test_dependent_is_packaged_after_both_extracted_dependencies(self):
        self.assertEqual(MODULE.PACKAGE_ORDER, ("cordis-kernel", "cordis-driver", "cordis"))
        with tempfile.TemporaryDirectory(prefix="cordis-patch-space ") as directory:
            paths = {name: Path(directory) / name for name in MODULE.PACKAGE_ORDER[:2]}
            arguments = MODULE.cargo_patches(paths)
            self.assertEqual(arguments[::2], ["--config", "--config"])
            for name, argument in zip(paths, arguments[1::2]):
                prefix = f"patch.crates-io.{name}.path="
                self.assertTrue(argument.startswith(prefix))
                self.assertEqual(Path(json.loads(argument[len(prefix):])), paths[name])

    def test_kernel_has_no_self_patch(self):
        self.assertEqual(MODULE.cargo_patches({}), [])


if __name__ == "__main__":
    unittest.main()
