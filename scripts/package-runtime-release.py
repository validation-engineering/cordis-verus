#!/usr/bin/env python3
"""Stage GitHub Release assets from a fresh full quality gate; never upload.

`collect` requires all declared platforms from the same commit. Development
records cannot substitute for the full ordered mutation manifest.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
TARGETS = {'darwin-arm64-napi8', 'darwin-x64-napi8', 'linux-x64-gnu-napi8'}
NAMES = {'@cordis-verus/compat-cordis', '@cordis-verus/compat-harness', '@cordis-verus/compat-loader'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError(f'Expected regular file: {path}')
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def run(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).rstrip('\n')


def safe_file(name):
    if not isinstance(name, str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', name):
        raise ValueError(f'Unsafe release asset name: {name}')
    return name


def bound_files(root, hashes):
    if not isinstance(hashes, dict) or not hashes:
        raise ValueError('Missing source hashes')
    for name, expected in hashes.items():
        path = root / name
        if Path(name).is_absolute() or '..' in Path(name).parts or path.is_symlink() or digest(path) != expected:
            raise ValueError(f'Stale or unsafe source: {name}')


def verification_module():
    spec = importlib.util.spec_from_file_location('release_verification', ROOT / 'scripts/record-verification.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def validate_quality(record, verifier):
    if record.get('schema') != 'cordis-verus.verification/v3' or record.get('status') != 'passed':
        raise ValueError('A fresh full release verification report is required')
    verifier.validate_negative_report({'baseline': record.get('proof'), 'mutations': record.get('negativeControls')}, verifier.required_negative_names())
    if record.get('sha256') != verifier.source_hashes():
        raise ValueError('Release verification source hashes are stale')
    if record.get('paperCoverage', {}).get('completionClaimed') is not False:
        raise ValueError('Runtime release must preserve the paper proof boundary')


def checked_asset(directory, item):
    path = directory / safe_file(item['file'])
    if path.is_symlink() or not path.is_file() or path.stat().st_size != item['bytes'] or digest(path) != item['sha256']:
        raise ValueError(f'Release asset integrity mismatch: {path}')
    return path


def asset(path):
    return {'file': path.name, 'bytes': path.stat().st_size, 'sha256': digest(path)}


def publish_directory(stage, output):
    # Exclusive reservation; never replace prior evidence.
    output.mkdir()
    try:
        stage.rename(output)
    except BaseException:
        output.rmdir()
        raise


def package(output):
    verifier = verification_module()
    verification = read(ROOT / 'docs/verification-report.json')
    validate_quality(verification, verifier)
    # The recorder only changes its own checked-in report. No source may differ
    # from the release commit, including newly created untracked source files.
    changes = run('git', 'status', '--porcelain=v1', '--untracked-files=all').splitlines()
    if any(line != ' M docs/verification-report.json' for line in changes):
        raise ValueError('Release packaging requires a clean source commit (only the fresh verification report may differ)')
    commit = run('git', 'rev-parse', 'HEAD')
    if not re.fullmatch(r'[a-f0-9]{40}', commit):
        raise ValueError('Invalid source commit')
    npm_directory = ROOT / 'target/release-artifacts/npm'
    npm = read(npm_directory / 'package-report.json')
    build = read(ROOT / 'target/node-compat/build.json')
    if npm.get('schema') != 'cordis-verus.npm-package/v1' or npm.get('status') != 'passed':
        raise ValueError('A successful independent npm installation is required')
    bound_files(ROOT, npm['sourceHashes'])
    bound_files(ROOT, npm['nativeSourceHashes'])
    if npm['buildReportSha256'] != digest(ROOT / 'target/node-compat/build.json'):
        raise ValueError('Native build report changed')
    selection = json.loads(run('node', '--input-type=module', '-e', "import {selectNativeArtifact} from './packages/compat-cordis/native-artifacts.js'; const s=selectNativeArtifact(); console.log(JSON.stringify({target:s.entry.target,manifest:s.manifestSha256,binary:s.entry.sha256}));"))
    target = npm['nativeTarget']
    if target not in TARGETS or selection != {'target': target, 'manifest': npm['nativeManifestSha256'], 'binary': npm['nativeArtifactSha256']}:
        raise ValueError('Native package provenance or platform differs')
    if len(npm['packages']) != 3 or {item['name'] for item in npm['packages']} != NAMES:
        raise ValueError('Exactly three supported npm packages are required')
    output = output.resolve()
    if output.exists():
        raise ValueError('Output already exists')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.runtime-release-', dir=output.parent) as temporary:
        stage = Path(temporary) / 'assets'
        stage.mkdir()
        packages = []
        for item in sorted(npm['packages'], key=lambda item: item['name']):
            source = npm_directory / safe_file(item['filename'])
            if source.is_symlink() or digest(source) != item['sha256']:
                raise ValueError(f'Package changed: {source}')
            destination = stage / f'{target}-{source.name}'
            shutil.copyfile(source, destination)
            packages.append({**asset(destination), 'name': item['name'], 'version': item['version']})
        evidence = stage / f'cordis-evidence-{target}.json'
        write(evidence, {'sourceCommit': commit, 'verification': verification, 'npm': npm, 'build': build})
        manifest = {'schema': 'cordis-verus.runtime-release/v1', 'sourceCommit': commit, 'target': target,
                    'nativeManifestSha256': npm['nativeManifestSha256'], 'nativeArtifactSha256': npm['nativeArtifactSha256'],
                    'acceptance': {'fullQuality': True, 'negativeControls': len(verification['negativeControls']), 'paperCompletion': False},
                    'packages': packages, 'evidence': asset(evidence)}
        write(stage / f'cordis-runtime-{target}.json', manifest)
        shutil.copyfile(ROOT / 'scripts/install-cordis.mjs', stage / 'install-cordis.mjs')
        publish_directory(stage, output)
    print(f'Staged {target} from full quality evidence at {commit}. No upload performed.')


def collect(inputs, output, commit):
    if not re.fullmatch(r'[a-f0-9]{40}', commit):
        raise ValueError('Expected a full release commit SHA')
    manifests = sorted(inputs.glob('**/cordis-runtime-*.json'))
    seen, assets, installer = set(), {}, None
    verifier = verification_module()
    if run('git', 'rev-parse', 'HEAD') != commit:
        raise ValueError('Collector checkout differs from release commit')
    for path in manifests:
        record = read(path)
        target = record.get('target')
        if record.get('schema') != 'cordis-verus.runtime-release/v1' or target not in TARGETS or target in seen or record.get('sourceCommit') != commit:
            raise ValueError('Duplicate, unsupported or mixed-commit platform evidence')
        if record.get('acceptance', {}).get('fullQuality') is not True or record['acceptance'].get('paperCompletion') is not False:
            raise ValueError('A development artifact is not a release artifact')
        if len(record.get('packages', [])) != 3 or {item['name'] for item in record['packages']} != NAMES:
            raise ValueError('Incomplete npm package inventory')
        seen.add(target)
        assets[path.name] = path
        for item in [*record['packages'], record['evidence']]:
            source = checked_asset(path.parent, item)
            if source.name in assets:
                raise ValueError('Duplicate release filename')
            assets[source.name] = source
        evidence = read(path.parent / record['evidence']['file'])
        if evidence.get('sourceCommit') != commit:
            raise ValueError('Evidence commit differs')
        validate_quality(evidence['verification'], verifier)
        if record['acceptance'].get('negativeControls') != len(evidence['verification']['negativeControls']):
            raise ValueError('Negative control count differs')
        npm = evidence.get('npm', {})
        if (npm.get('status') != 'passed' or npm.get('nativeTarget') != target
                or npm.get('nativeManifestSha256') != record.get('nativeManifestSha256')
                or npm.get('nativeArtifactSha256') != record.get('nativeArtifactSha256')
                or sorted((item['name'], item['version'], item['sha256']) for item in npm.get('packages', []))
                != sorted((item['name'], item['version'], item['sha256']) for item in record['packages'])):
            raise ValueError('Platform assets differ from their package acceptance report')
        current = path.parent / 'install-cordis.mjs'
        if current.is_symlink() or not current.is_file() or (installer is not None and digest(current) != digest(installer)):
            raise ValueError('Platform installers differ')
        installer = current
    if seen != TARGETS:
        raise ValueError('All three full-quality platform artifacts are required')
    if digest(installer) != digest(ROOT / 'scripts/install-cordis.mjs'):
        raise ValueError('Installer differs from the release checkout')
    assets['install-cordis.mjs'] = installer
    output = output.resolve()
    if output.exists():
        raise ValueError('Output already exists')
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.runtime-collect-', dir=output.parent) as temporary:
        stage = Path(temporary) / 'assets'
        stage.mkdir()
        for name, source in sorted(assets.items()):
            shutil.copyfile(source, stage / name)
        (stage / 'SHA256SUMS').write_text(''.join(f'{digest(stage / name)}  {name}\n' for name in sorted(assets)))
        publish_directory(stage, output)
    print('Collected all three platforms. No upload performed.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    staging = commands.add_parser('package')
    staging.add_argument('--output', type=Path, default=ROOT / 'target/github-release')
    collecting = commands.add_parser('collect')
    collecting.add_argument('--input', type=Path, required=True)
    collecting.add_argument('--output', type=Path, required=True)
    collecting.add_argument('--commit', required=True)
    args = parser.parse_args()
    if args.command == 'package':
        package(args.output)
    else:
        collect(args.input, args.output, args.commit)


if __name__ == '__main__':
    main()
