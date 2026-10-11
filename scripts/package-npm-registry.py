#!/usr/bin/env python3
"""Assemble one npm package per name/version from all four accepted runtime assets.

Only native layout changes: JS, manifests and binary/provenance bytes are retained.
The resulting archives still require installation checks on every target.
"""
import argparse
import importlib.util
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('runtime_release', ROOT / 'scripts/package-runtime-release.py')
RELEASE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RELEASE)
CORE = '@validation-engineering/cordis'


def extract(archive, output):
    with tarfile.open(archive, 'r:gz') as bundle:
        members = bundle.getmembers()
        seen = set()
        for member in members:
            path = PurePosixPath(member.name)
            if (path.is_absolute() or '..' in path.parts or not path.parts
                    or path.parts[0] != 'package' or '\\' in member.name
                    or not (member.isfile() or member.isdir()) or path in seen):
                raise ValueError(f'Unsafe or duplicate npm archive entry: {member.name}')
            seen.add(path)
        for member in members:
            path = output.joinpath(*PurePosixPath(member.name).parts)
            if member.isdir():
                path.mkdir(parents=True, exist_ok=True)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(bundle.extractfile(member).read())
    return output / 'package'


def payload(directory):
    return {path.relative_to(directory).as_posix(): RELEASE.digest(path)
            for path in sorted(directory.rglob('*')) if path.is_file()
            and path.relative_to(directory).parts[0] != 'native'}


def check_metadata(directory, name, version):
    metadata = RELEASE.read(directory / 'package.json')
    if (metadata.get('name') != name or metadata.get('version') != version
            or metadata.get('private') is True
            or metadata.get('publishConfig') != {'access': 'public', 'registry': 'https://registry.npmjs.org/'}):
        raise ValueError('Package is not configured for public npm publication')
    if any(key in metadata.get('scripts', {}) for key in ('preinstall', 'install', 'postinstall', 'prepare')):
        raise ValueError('Registry runtime must install without build/lifecycle scripts')


def assemble(inputs, output, commit):
    output = output.resolve()
    if output.exists():
        raise ValueError('Output already exists')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.npm-registry-', dir=output.parent) as temporary:
        temporary = Path(temporary)
        accepted = temporary / 'accepted'
        # Reuse the full release validator, including source freshness and proof.
        RELEASE.collect(inputs, accepted, commit)
        stage = temporary / 'registry'
        stage.mkdir()
        packages, native, sources, baselines = {}, [], {}, {}
        for target in sorted(RELEASE.TARGETS):
            manifest = RELEASE.read(accepted / f'cordis-runtime-{target}.json')
            sources[target] = {'manifest': RELEASE.asset(accepted / f'cordis-runtime-{target}.json'),
                               'evidence': manifest['evidence'], 'packages': manifest['packages']}
            for item in manifest['packages']:
                name = item['name']
                directory = extract(RELEASE.checked_asset(accepted, item), temporary / target / name.split('/')[-1])
                check_metadata(directory, name, item['version'])
                current = (item['version'], payload(directory))
                if name in baselines and current != baselines[name]:
                    raise ValueError(f'JavaScript package differs across release platforms: {name}')
                baselines[name] = current
                packages.setdefault(name, directory)
                if name == CORE:
                    native.append(directory / 'native')
        merged = temporary / 'merged-native'
        subprocess.run(['node', str(ROOT / 'scripts/package-native.mjs'), '--output', str(merged), *map(str, native)], check=True)
        native_manifest = RELEASE.read(merged / 'manifest.json')
        if {item['target'] for item in native_manifest['artifacts']} != RELEASE.TARGETS:
            raise ValueError('Universal npm package must contain exactly four native targets')
        targets = {}
        for entry in native_manifest['artifacts']:
            provenance = RELEASE.read(merged / entry['provenance'])
            targets[entry['target']] = {'sha256': entry['sha256'], 'sourceDigest': provenance['build']['sourceDigest']}
        core = packages[CORE]
        shutil.rmtree(core / 'native')
        shutil.copytree(merged, core / 'native')
        records = []
        npm = json.loads(subprocess.check_output(['node', '--input-type=module', '-e',
            "import { npmCommand } from './scripts/install-cordis.mjs'; console.log(JSON.stringify(npmCommand()));"], cwd=ROOT, text=True))
        for name, directory in sorted(packages.items()):
            packed, = json.loads(subprocess.check_output([*npm, 'pack', '--ignore-scripts', '--offline', '--json',
                '--pack-destination', str(stage)], cwd=directory, text=True))
            archive = stage / RELEASE.safe_file(packed['filename'])
            records.append({**RELEASE.asset(archive), 'name': name, 'version': packed['version'], 'integrity': packed['integrity']})
        record = {'schema': 'cordis-verus.npm-registry/v1', 'sourceCommit': commit,
                  'packages': records, 'targets': targets,
                  'nativeManifestSha256': RELEASE.digest(merged / 'manifest.json'),
                  'sourceAssets': sources, 'installation': 'required-on-every-target', 'uploaded': False}
        RELEASE.write(stage / 'npm-registry.json', record)
        for script in ('check-npm-registry.mjs', 'install-cordis.mjs'):
            shutil.copyfile(ROOT / 'scripts' / script, stage / script)
        (stage / 'SHA256SUMS').write_text(''.join(f'{RELEASE.digest(path)}  {path.name}\n' for path in sorted(stage.iterdir())))
        RELEASE.publish_directory(stage, output)
    print(f'Assembled three universal registry packages in {output}; no upload, installation still required.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--commit', required=True)
    args = parser.parse_args()
    assemble(args.input, args.output, args.commit)
