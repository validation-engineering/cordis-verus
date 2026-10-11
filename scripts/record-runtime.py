#!/usr/bin/env python3
"""Run host-specific acceptance without claiming that a Verus proof ran here.

Release assembly joins this record with fresh whole-kernel release-quality
evidence for exactly the same source snapshot. This record alone cannot release.
"""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = 'cordis-verus.runtime-validation/v1'
STEPS = ['clippy', 'rust-tests', 'examples', 'native-build', 'node-tests', 'crate-packages', 'npm-packages']
TARGETS = {'darwin-arm64-napi8': ('darwin', 'arm64'), 'darwin-x64-napi8': ('darwin', 'x64'),
           'linux-x64-gnu-napi8': ('linux', 'x64'), 'win32-x64-napi8': ('win32', 'x64')}


def helpers():
    path = ROOT / 'scripts/record-verification.py'
    spec = importlib.util.spec_from_file_location('runtime_release_helpers', path)
    module = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


def validate(record, *, sources, commit):
    if (record.get('schema') != SCHEMA or record.get('status') != 'passed'
            or record.get('proofExecuted') is not False or record.get('releaseAcceptance') is not False
            or record.get('sha256') != sources or record.get('sourceCommit') != commit):
        raise ValueError('Runtime evidence is stale, incomplete, or misstates its proof boundary')
    if record.get('steps') != [{'name': name, 'status': 'passed'} for name in STEPS]:
        raise ValueError('Runtime evidence is missing an acceptance step')
    tests = record.get('tests', {})
    node = tests.get('nodeCompatibility', {})
    if (type(tests.get('total')) is not int or tests['total'] <= 0
            or type(node.get('tests')) is not int or node['tests'] <= 0
            or node.get('pass') != node['tests']
            or any(type(node.get(key)) is not int or node[key] != 0
                   for key in ('fail', 'cancelled', 'skipped', 'todo'))):
        raise ValueError('Runtime tests failed, skipped, or are incomplete')
    npm, build = record.get('npmDistribution', {}), record.get('nodeBuild', {})
    target = record.get('target')
    if (target not in TARGETS or npm.get('nativeTarget') != target
            or (build.get('platform'), build.get('architecture')) != TARGETS[target]
            or build.get('schema') != 'cordis-verus.node-build/v1'
            or npm.get('schema') != 'cordis-verus.npm-package/v1'
            or npm.get('status') != 'passed' or npm.get('offline') is not True
            or npm.get('nativeSourceHashes') != build.get('sourceHashes')
            or not build.get('sourceHashes')
            or any(sources.get(name) != digest for name, digest in build['sourceHashes'].items())
            or npm.get('nativeArtifactSha256') != build.get('artifactSha256')):
        raise ValueError('Runtime build/package evidence is inconsistent with its target or source')
    if not re.fullmatch(r'[a-f0-9]{64}', record.get('logSha256', '')):
        raise ValueError('Runtime log hash is missing')


def run_checks(checks, environment, log, on_success):
    """Collect independent failures; dependent steps require a fresh native build."""
    steps = []
    for name in STEPS:
        if name in ('node-tests', 'npm-packages') and not any(
                step == {'name': 'native-build', 'status': 'passed'} for step in steps):
            steps.append({'name': name, 'status': 'not_run'})
            message = f'{name}: not run because the native build failed\n'
            print(message, end='', flush=True); log.write(message); log.flush()
            continue
        passed = True
        for command in checks[name]:
            message = '+ ' + ' '.join(command) + '\n'
            print(message, end='', flush=True); log.write(message); log.flush()
            try:
                # CI owns the job process tree. No proof is executed here.
                result = subprocess.run(command, cwd=ROOT, env=environment, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, text=True, encoding='utf-8', errors='replace', timeout=1800)
                log.write(result.stdout); log.flush()
                print(result.stdout, end='', flush=True)
                result.check_returncode()
                on_success(name, result.stdout)
            except (OSError, subprocess.SubprocessError, ValueError, RuntimeError) as error:
                passed = False
                if isinstance(error, subprocess.TimeoutExpired) and error.stdout:
                    captured = error.stdout.decode('utf-8', errors='replace') if isinstance(error.stdout, bytes) else error.stdout
                    log.write(captured)
                message = f'FAILED {name}: {error}\n'
                print(message, end='', flush=True); log.write(message); log.flush()
        steps.append({'name': name, 'status': 'passed' if passed else 'failed'})
    return steps


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--offline', action='store_true')
    args = parser.parse_args()
    verifier = helpers()
    runtime = verifier.execution_helpers()
    before = verifier.source_hashes()
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    output = ROOT / 'target/runtime-validation'
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / 'report.json'
    report_path.unlink(missing_ok=True)
    diagnostic_path = output / 'diagnostic.json'
    diagnostic_path.unlink(missing_ok=True)
    environment = verifier.environment_for(args.offline)
    environment['RUSTUP_TOOLCHAIN'] = json.loads((ROOT / 'toolchain.lock.json').read_text())['rust']['channel']
    environment['PATH'] = str(Path(environment.get('CARGO_HOME', Path.home() / '.cargo')) / 'bin') + os.pathsep + environment.get('PATH', '')
    environment['PYTHONUTF8'] = '1'
    network = ['--offline'] if args.offline else []
    node_tests = sorted(str(path.relative_to(ROOT)) for folder in ('node-compat', 'node-loader', 'benchmarks')
                        for path in (ROOT / 'tests' / folder).glob('*.test.mjs'))
    checks = {
        'clippy': [['cargo', 'clippy', '--workspace', '--all-targets', '--locked', '--', '-D', 'warnings']],
        'rust-tests': [['cargo', 'test', '--workspace', '--locked', '--no-fail-fast']],
        'examples': [['cargo', 'run', '--locked', '-p', 'cordis', '--example', path.stem]
                     for path in sorted((ROOT / 'crates/cordis/examples').glob('*.rs'))],
        'native-build': [['node', 'scripts/build-node.mjs', *network]],
        'node-tests': [['node', '--test', '--test-concurrency=4', '--test-timeout=30000', '--test-reporter=tap', *node_tests]],
        'crate-packages': [[sys.executable, 'scripts/package-check.py', *network]],
        'npm-packages': [['node', 'scripts/check-npm-package.mjs']],
    }
    tests = {}
    def on_success(name, output):
        if name == 'rust-tests':
            tests.update(verifier.test_counts(output))
            tests.pop('deterministicTraces', None)
        elif name == 'node-tests':
            lines = ['workspace ended', runtime.NODE_BEGIN, *output.splitlines(), runtime.NODE_END, 'done']
            tests['nodeCompatibility'] = runtime.parse_node_tests(lines, 0)

    log_path = output / 'runtime.log'
    with log_path.open('w', encoding='utf-8') as log:
        steps = run_checks(checks, environment, log, on_success)
    if any(step['status'] != 'passed' for step in steps):
        diagnostic_path.write_text(json.dumps({
            'schema': 'cordis-verus.runtime-diagnostic/v1', 'status': 'failed',
            'proofExecuted': False, 'releaseAcceptance': False,
            'sourceCommit': commit, 'steps': steps, 'logSha256': runtime.file_sha256(log_path),
        }, indent=2) + '\n', encoding='utf-8')
        raise RuntimeError('Runtime acceptance failed: ' + ', '.join(
            f"{step['name']}={step['status']}" for step in steps if step['status'] != 'passed'))
    build_path = ROOT / 'target/node-compat/build.json'
    build = runtime.node_build_evidence(build_path)
    npm = runtime.npm_distribution_evidence(ROOT / 'target/release-artifacts/npm/package-report.json', build_path, build)
    if before != verifier.source_hashes() or commit != subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip():
        raise RuntimeError('Sources changed during runtime validation')
    record = {'schema': SCHEMA, 'status': 'passed', 'checkedAt': datetime.now(timezone.utc).isoformat(),
              'proofExecuted': False, 'releaseAcceptance': False, 'sourceCommit': commit,
              'target': npm['nativeTarget'], 'steps': steps, 'tests': tests, 'nodeBuild': build,
              'npmDistribution': npm, 'sha256': before, 'logSha256': runtime.file_sha256(log_path)}
    validate(record, sources=before, commit=commit)
    report_path.write_text(json.dumps(record, indent=2) + '\n', encoding='utf-8')
    print(f'Runtime acceptance passed for {record["target"]}. A matching full proof is still required for release.')


if __name__ == '__main__':
    main()
