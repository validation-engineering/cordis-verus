#!/usr/bin/env python3
"""Stage GitHub Release assets from fresh release quality checks; never upload.

`collect` requires all four targets from the same commit. A complete positive
proof is shared by byte-identical sources; runtime and installation acceptance
are required on each host. Host-only records never substitute for that proof.
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
TARGETS = {'darwin-arm64-napi8', 'darwin-x64-napi8', 'linux-x64-gnu-napi8', 'win32-x64-napi8'}
DEFAULT_TARGETS = TARGETS.copy()
NAMES = {'@validation-engineering/cordis', '@validation-engineering/cordis-harness', '@validation-engineering/cordis-loader'}


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


def validate_shared_kernel():
    # Sharing the Linux proof is restricted to this platform-independent kernel.
    # New conditional compilation requires reviewing that policy, not silently
    # using a proof of the Linux branch for another platform's executable code.
    files = list((ROOT / 'crates/cordis-kernel/src').rglob('*.rs'))
    if not files:
        raise ValueError('Missing shared kernel sources')
    allowed = {'all', 'any', 'not', 'test', 'verus_keep_ghost'}
    for path in files:
        source = path.read_text()
        if re.search(r'\bcfg_attr\s*\(|\b(?:cfg|include)\s*!', source):
            raise ValueError(f'Conditional/generated kernel code needs a proof portability review: {path.name}')
        for expression in re.findall(r'#\s*!?\s*\[\s*cfg\s*\((.*?)\)\s*\]', source, re.S):
            if set(re.findall(r'[A-Za-z_][A-Za-z_0-9]*', expression)) - allowed:
                raise ValueError(f'Platform/feature-specific kernel code needs a proof portability review: {path.name}')


def validate_quality(record, verifier):
    validate_shared_kernel()
    if record.get('schema') != 'cordis-verus.verification/v4' or record.get('status') != 'passed':
        raise ValueError('A fresh full release verification report is required')
    verifier.validate_release_report(record)
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


def validate_host_evidence(evidence, verifier):
    quality = evidence['verification']
    runtime = evidence.get('runtimeValidation')
    accepted = quality
    if runtime is not None:
        verifier.helper('record-runtime.py', 'runtime_acceptance').validate(
            runtime, sources=quality['sha256'], commit=evidence['sourceCommit'])
        accepted = runtime
    if accepted.get('npmDistribution') != evidence.get('npm') or accepted.get('nodeBuild') != evidence.get('build'):
        raise ValueError('Runtime packages differ from their host acceptance evidence')


def publish_directory(stage, output):
    # Exclusive reservation; never replace prior evidence.
    output.mkdir()
    try:
        for child in stage.iterdir():
            child.rename(output / child.name)
        stage.rmdir()
    except BaseException:
        shutil.rmtree(output)
        raise


def package(output, runtime_input=None, quality_report=None):
    verifier = verification_module()
    verification = read(quality_report or ROOT / 'docs/verification-report.json')
    validate_quality(verification, verifier)
    # The recorder only changes its own checked-in report. No source may differ
    # from the release commit, including newly created untracked source files.
    changes = run('git', 'status', '--porcelain=v1', '--untracked-files=all').splitlines()
    if any(line != ' M docs/verification-report.json' for line in changes):
        raise ValueError('Release packaging requires a clean source commit (only the fresh verification report may differ)')
    commit = run('git', 'rev-parse', 'HEAD')
    if not re.fullmatch(r'[a-f0-9]{40}', commit):
        raise ValueError('Invalid source commit')
    inputs = runtime_input or ROOT
    npm_directory = inputs / 'target/release-artifacts/npm'
    npm = read(npm_directory / 'package-report.json')
    build = read(inputs / 'target/node-compat/build.json')
    evidence_record = {'sourceCommit': commit, 'verification': verification, 'npm': npm, 'build': build}
    if runtime_input is not None:
        runtime = read(inputs / 'target/runtime-validation/report.json')
        if runtime.get('logSha256') != digest(inputs / 'target/runtime-validation/runtime.log'):
            raise ValueError('Runtime validation log changed')
        evidence_record['runtimeValidation'] = runtime
    validate_host_evidence(evidence_record, verifier)
    if npm.get('schema') != 'cordis-verus.npm-package/v1' or npm.get('status') != 'passed':
        raise ValueError('A successful independent npm installation is required')
    for name, expected in npm['sourceHashes'].items():
        bound_files(inputs if name.startswith('packages/compat-cordis/native/') else ROOT, {name: expected})
    bound_files(ROOT, npm['nativeSourceHashes'])
    if npm['buildReportSha256'] != digest(inputs / 'target/node-compat/build.json'):
        raise ValueError('Native build report changed')
    selection = json.loads(run('node', '--input-type=module', '-e',
        "import {verifyNativeManifest} from './packages/compat-cordis/native-artifacts.js'; "
        "const v=verifyNativeManifest(process.argv[1]); if(v.artifacts.length!==1) throw Error('Expected one host artifact'); "
        "const s=v.artifacts[0]; console.log(JSON.stringify({target:s.entry.target,manifest:v.manifestSha256,binary:s.entry.sha256}));",
        str(inputs / 'packages/compat-cordis/native')))
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
        write(evidence, evidence_record)
        manifest = {'schema': 'cordis-verus.runtime-release/v3', 'sourceCommit': commit, 'target': target,
                    'nativeManifestSha256': npm['nativeManifestSha256'], 'nativeArtifactSha256': npm['nativeArtifactSha256'],
                    'acceptance': {'releaseQuality': True, 'negativeControls': 'not_run', 'paperCompletion': False},
                    'packages': packages, 'evidence': asset(evidence)}
        write(stage / f'cordis-runtime-{target}.json', manifest)
        shutil.copyfile(ROOT / 'scripts/install-cordis.mjs', stage / 'install-cordis.mjs')
        publish_directory(stage, output)
    print(f'Staged {target} from full quality evidence at {commit}. No upload performed.')


def selected_targets(targets):
    if targets is None:
        return DEFAULT_TARGETS.copy()
    if not isinstance(targets, list) or not all(isinstance(target, str) for target in targets):
        raise ValueError('Release targets must be a JSON array of platform names')
    selection = set(targets)
    if len(selection) != len(targets):
        raise ValueError('Duplicate release targets')
    if selection != TARGETS:
        raise ValueError('A release requires Linux x64, both macOS architectures, and Windows x64')
    return selection


def parse_targets_json(value):
    targets = json.loads(value)
    if not isinstance(targets, list):
        raise ValueError('Release targets must be a JSON array of platform names')
    selected_targets(targets)
    return targets


def collect(inputs, output, commit, targets=None):
    required = selected_targets(targets)
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
        if record.get('schema') != 'cordis-verus.runtime-release/v3' or not isinstance(target, str) or target not in required or target in seen or record.get('sourceCommit') != commit:
            raise ValueError('Duplicate, unselected, unsupported or mixed-commit platform evidence')
        if record.get('acceptance', {}).get('releaseQuality') is not True or record['acceptance'].get('paperCompletion') is not False:
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
        if record['acceptance'].get('negativeControls') != evidence['verification']['negativeControls']['status']:
            raise ValueError('Independent negative-control status differs')
        npm = evidence.get('npm', {})
        validate_host_evidence(evidence, verifier)
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
    if seen != required:
        raise ValueError(f'All selected full-quality platform artifacts are required; missing: {", ".join(sorted(required - seen))}')
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
    print(f'Collected {len(required)} selected platforms: {", ".join(sorted(required))}. No upload performed.')


def release_plan():
    quality = ['ubuntu-24.04']
    runtime = ['macos-15', 'macos-15-intel', 'windows-2025']
    return {'quality': {'os': quality}, 'runtime': {'os': runtime},
            'install': {'os': quality + runtime}, 'targets': sorted(TARGETS)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    planning = commands.add_parser('plan')
    planning.add_argument('--github-output', type=Path, required=True)
    staging = commands.add_parser('package')
    staging.add_argument('--output', type=Path, default=ROOT / 'target/github-release')
    staging.add_argument('--runtime-input', type=Path, help='Downloaded host acceptance artifact')
    staging.add_argument('--quality-report', type=Path, help='Matching full release-quality report')
    collecting = commands.add_parser('collect')
    collecting.add_argument('--input', type=Path, required=True)
    collecting.add_argument('--output', type=Path, required=True)
    collecting.add_argument('--commit', required=True)
    collecting.add_argument('--targets-json', type=parse_targets_json,
                            help='JSON array of release targets; defaults to all four platforms')
    args = parser.parse_args()
    if args.command == 'plan':
        with args.github_output.open('a') as stream:
            for key, value in release_plan().items():
                stream.write(key + '=' + json.dumps(value, separators=(',', ':')) + '\n')
    elif args.command == 'package':
        package(args.output, args.runtime_input, args.quality_report)
    else:
        collect(args.input, args.output, args.commit, args.targets_json)


if __name__ == '__main__':
    main()
