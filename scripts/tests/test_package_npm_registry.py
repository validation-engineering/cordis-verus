"""Registry assembly must not change JS payloads or trust unsafe tar entries."""
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location('npm_registry', Path(__file__).resolve().parents[1] / 'package-npm-registry.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class RegistryArchiveTests(unittest.TestCase):
    def test_extraction_rejects_escape_symlinks_and_duplicate_entries(self):
        for name, kind, duplicate in [('../escape', tarfile.REGTYPE, False),
                                      ('package/../escape', tarfile.REGTYPE, False),
                                      ('package/link', tarfile.SYMTYPE, False),
                                      ('package/index.js', tarfile.REGTYPE, True),
                                      ('package\\escape', tarfile.REGTYPE, False)]:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                archive = root / 'package.tgz'
                with tarfile.open(archive, 'w:gz') as bundle:
                    for _ in range(2 if duplicate else 1):
                        entry = tarfile.TarInfo(name); entry.type = kind
                        entry.size = 1 if kind == tarfile.REGTYPE else 0
                        bundle.addfile(entry, io.BytesIO(b'x') if entry.size else None)
                with self.assertRaisesRegex(ValueError, 'Unsafe or duplicate'):
                    MODULE.extract(archive, root / 'extracted')
                self.assertFalse((root / 'extracted').exists())

    def test_payload_ignores_only_the_native_layout(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'native').mkdir()
            (root / 'index.js').write_text('export const value = 1')
            (root / 'package.json').write_text('{}')
            (root / 'native/cordis.node').write_bytes(b'platform one')
            original = MODULE.payload(root)
            (root / 'native/cordis.node').write_bytes(b'platform two')
            self.assertEqual(MODULE.payload(root), original)
            (root / 'index.js').write_text('export const value = 2')
            self.assertNotEqual(MODULE.payload(root), original)

    def test_private_and_scripted_packages_cannot_enter_registry_bundle(self):
        valid = {'name': MODULE.CORE, 'version': '0.1.0',
                 'publishConfig': {'access': 'public', 'registry': 'https://registry.npmjs.org/'}}
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'package.json').write_text(json.dumps(valid))
            MODULE.check_metadata(root, MODULE.CORE, '0.1.0')
            for changes in [{'private': True}, {'name': 'unrelated'}, {'version': '9.0.0'},
                            {'publishConfig': {}}, {'scripts': {'install': 'cargo build'}}]:
                (root / 'package.json').write_text(json.dumps({**valid, **changes}))
                with self.subTest(changes=changes), self.assertRaises(ValueError):
                    MODULE.check_metadata(root, MODULE.CORE, '0.1.0')


if __name__ == '__main__':
    unittest.main()
