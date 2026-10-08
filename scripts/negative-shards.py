#!/usr/bin/env python3
"""Distribute complete-crate negative checks; accept only their complete union.

Each shard compiles/verifies every assigned mutant as a full crate. Its positive
baseline is run locally or reused from the exact same CI run/attempt and platform. Collection revalidates the original output and command
metadata, rather than trusting a shard's summarized success flag.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = 'cordis-verus.full-negative-shard/v2'
PREFLIGHT_SCHEMA = 'cordis-verus.negative-preflight/v2'
SCRIPT_SHA = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def read_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate evidence JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs)


def module(filename, name):
    path = ROOT / 'scripts' / filename
    spec = importlib.util.spec_from_file_location(name, path)
    loaded = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), 'exec'), loaded.__dict__)
    return loaded


def checker():
    return module('check-negative.py', 'full_negative_checker')


def recorder():
    return module('record-verification.py', 'full_negative_recorder')


def source_binding():
    hashes = recorder().source_hashes()
    require(hashes.get('scripts/negative-shards.py') == SCRIPT_SHA,
            'Shard runner changed after loading')
    return hashes


def ci_origin():
    names = ['GITHUB_REPOSITORY', 'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_SHA']
    if os.environ.get('GITHUB_ACTIONS') == 'true':
        require(all(os.environ.get(name) for name in names), 'Incomplete Actions run identity')
        return {name: os.environ[name] for name in names}
    return None


def binding(checks, binary):
    require(not any(os.environ.get(name) for name in
                    ['VERUS_Z3_PATH', 'VERUS_EXTRA_ARGS', 'RUSTFLAGS', 'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER']),
            'Custom verifier/compiler overrides are not accepted')
    toolroot = Path(binary).parent
    # Hash executable solver/verifier and proof libraries, not just a version label.
    files = sorted(p for p in toolroot.iterdir() if p.is_file() and
                   (p.name in {'verus', 'rust_verify', 'z3', 'version.json', 'vstd.vir'}
                    or p.suffix in {'.rlib', '.dylib', '.so'}))
    require({'verus', 'rust_verify', 'z3', 'vstd.vir'}.issubset({p.name for p in files}),
            'Missing pinned verifier/solver/proof libraries')
    return {'sourceHashes': source_binding(), 'manifestSha256': fingerprint(checks.mutation_manifest()),
            'host': {'os': platform.system(), 'architecture': platform.machine()},
            'toolHashes': {p.name: digest(p) for p in files}, 'origin': ci_origin()}


def assigned(manifest, index, count):
    require(type(count) is int and 1 <= count <= len(manifest), 'Invalid shard count')
    require(type(index) is int and 0 <= index < count, 'Invalid shard index')
    return [item for position, item in enumerate(manifest) if position % count == index]


def safe_file(directory, name):
    require(isinstance(name, str) and name and Path(name).name == name and name not in {'.', '..'},
            'Unsafe evidence filename')
    path = directory / name
    require(path.is_file() and not path.is_symlink(), 'Missing or symlinked evidence: ' + name)
    return path


def save(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def stage_files(stem):
    return [stem + suffix for suffix in ('.stdout.json', '.stderr.txt', '.meta.json')]


def positive(result):
    data = json.loads(result.stdout)
    stats = data.get('verification-results', {})
    require(result.returncode == 0 and stats.get('success') is True
            and type(stats.get('verified')) is int and stats['verified'] > 0
            and type(stats.get('errors')) is int and stats['errors'] == 0
            and stats.get('encountered-vir-error') is False
            and stats.get('encountered-error') is False
            and stats.get('is-verifying-entire-crate') is True,
            'Incomplete full-crate positive baseline')
    return data


def run_preflight(output, *, threads=None, cpu_budget=None, timeout=2400):
    """Verify one full positive baseline; reusable only in this CI run/attempt."""
    require(type(timeout) is int and timeout > 0, 'Timeout must be positive')
    checks = checker()
    budget = checks.execution_budget(1, threads, cpu_budget)
    binary, environment = checks.toolchain()
    before = binding(checks, binary)
    output.mkdir(parents=True, exist_ok=False)
    record = {'schema': PREFLIGHT_SCHEMA, 'status': 'running',
              'releaseAcceptance': False, 'binding': before,
              'execution': {**budget, 'timeoutSeconds': timeout, 'diagnostics': True}}
    save(output / 'preflight.json', record)
    try:
        with tempfile.TemporaryDirectory(prefix='cordis-negative-preflight-') as temporary:
            source = Path(temporary) / 'baseline'
            shutil.copytree(ROOT / 'crates/cordis-kernel/src', source)
            print(f"Preflight: unchanged whole crate, {budget['threadsPerWorker']} threads, "
                  f"{timeout}s deadline; trace and timings retained in {output}", flush=True)
            with checks.ProcessSupervisor().signal_handlers() as supervisor:
                result = checks.run_verus(binary, environment, source / 'lib.rs', output / 'baseline',
                                          threads=budget['threadsPerWorker'], timeout=timeout,
                                          supervisor=supervisor, diagnostics=True)
                whole = positive(result)
                supervisor.check()
            supervisor.check()
        require(binding(checks, binary) == before, 'Sources/toolchain changed during preflight')
        record.update(status='passed', checkedAt=datetime.now(timezone.utc).isoformat(),
                      baseline=whole['verification-results'], verus=whole['verus'],
                      files={name: digest(safe_file(output, name)) for name in stage_files('baseline')})
        supervisor.check()
        save(output / 'preflight.json', record)
        print(f"Preflight passed: {whole['verification-results']['verified']} verified, 0 errors. "
              'Same-attempt shards may reuse these raw baseline files; every mutant still runs as a full crate.', flush=True)
    except BaseException as error:
        record.update(status='failed', failure=f'{type(error).__name__}: {error}')
        save(output / 'preflight.json', record)
        raise
    return record


def validate_execution(execution, *, compile_timeout=False):
    keys = ['jobs', 'threadsPerWorker', 'timeoutSeconds', 'availableCpus', 'cpuBudget',
            'requestedJobs', 'baselineThreads']
    if compile_timeout:
        keys.append('compileTimeoutSeconds')
    require(isinstance(execution, dict)
            and all(type(execution.get(key)) is int and execution[key] > 0 for key in keys)
            and execution['jobs'] * execution['threadsPerWorker'] <= execution['cpuBudget']
            <= execution['availableCpus'] and execution['requestedJobs'] >= execution['jobs']
            and execution['baselineThreads'] == execution['threadsPerWorker']
            and execution.get('diagnostics') is True,
            'Invalid shard or preflight execution budget')


def validate_preflight(directory, expected_binding, expected_source, execution):
    """Recheck raw evidence, never use the producer's status as proof by itself."""
    require(not directory.is_symlink(), 'Symlinked preflight evidence is not accepted')
    path = safe_file(directory, 'preflight.json')
    record = read_json(path)
    origin = expected_binding.get('origin')
    names = {'GITHUB_REPOSITORY', 'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_SHA'}
    require(isinstance(origin, dict) and set(origin) == names
            and all(isinstance(value, str) and value for value in origin.values()),
            'Preflight reuse requires a complete current CI run/attempt identity')
    require(record.get('schema') == PREFLIGHT_SCHEMA and record.get('status') == 'passed'
            and record.get('releaseAcceptance') is False and record.get('binding') == expected_binding,
            'Preflight source/toolchain/platform/run identity differs or preflight failed')
    validate_execution(record.get('execution'))
    require(all(record['execution'][key] == execution[key]
                for key in ['threadsPerWorker', 'baselineThreads', 'timeoutSeconds', 'diagnostics']),
            'Preflight verifier parameters differ from shard parameters')
    require(set(record.get('files', {})) == set(stage_files('baseline')),
            'Incomplete or additional preflight stage evidence')
    whole = positive(stage(directory, 'baseline', record, expected_source))
    require(record.get('baseline') == whole['verification-results'] and record.get('verus') == whole['verus'],
            'Preflight summary differs from raw verifier output')
    return record, whole, digest(path)


def run_shard(index, count, output, *, jobs=1, threads=None, cpu_budget=None, timeout=2400,
              compile_timeout=300, preflight=None):
    require(type(timeout) is int and timeout > 0 and type(compile_timeout) is int and compile_timeout > 0,
            'Timeouts must be positive')
    checks = checker()
    manifest = checks.mutation_manifest()
    selected = assigned(manifest, index, count)
    budget = checks.execution_budget(jobs, threads, cpu_budget)
    binary, environment = checks.toolchain()
    before = binding(checks, binary)
    output.mkdir(parents=True, exist_ok=False)
    record = {'schema': SCHEMA, 'status': 'running', 'binding': before,
              'baselineMode': 'preflight' if preflight is not None else 'local',
              'shard': {'index': index, 'count': count, 'names': [item[0] for item in selected]},
              'execution': {**budget, 'timeoutSeconds': timeout,
                            'compileTimeoutSeconds': compile_timeout, 'diagnostics': True}}
    save(output / 'shard.json', record)
    try:
        with tempfile.TemporaryDirectory(prefix='cordis-full-shard-') as temporary:
            temporary = Path(temporary)
            baseline = temporary / 'baseline'
            shutil.copytree(ROOT / 'crates/cordis-kernel/src', baseline)
            baseline_source = checks.source_fingerprint(baseline)
            with checks.ProcessSupervisor().signal_handlers() as supervisor:
                if preflight is None:
                    result = checks.run_verus(binary, environment, baseline / 'lib.rs', output / 'baseline',
                                              threads=budget['threadsPerWorker'], timeout=timeout,
                                              supervisor=supervisor, diagnostics=True)
                    whole = positive(result)
                else:
                    _, whole, preflight_hash = validate_preflight(preflight, before, baseline_source,
                                                                 record['execution'])
                    for name in ['preflight.json'] + stage_files('baseline'):
                        shutil.copyfile(safe_file(preflight, name), output / name)
                    _, _, copied_hash = validate_preflight(output, before, baseline_source, record['execution'])
                    require(copied_hash == preflight_hash, 'Preflight changed while copying evidence')
                    record['preflightSha256'] = preflight_hash
                print(f"OK unmodified kernel ({record['baselineMode']}): "
                      f"{whole['verification-results']['verified']} verified, 0 errors", flush=True)
                controls = checks.check_mutations(selected, baseline, temporary, output, binary, environment,
                                                 jobs=budget['jobs'], threads=budget['threadsPerWorker'],
                                                 timeout=timeout, compile_timeout=compile_timeout,
                                                 supervisor=supervisor, diagnostics=True)
                supervisor.check()
            supervisor.check()
        require(binding(checks, binary) == before, 'Sources/toolchain changed during shard execution')
        names = stage_files('baseline')
        if preflight is not None:
            _, _, final_hash = validate_preflight(output, before, baseline_source, record['execution'])
            require(final_hash == record['preflightSha256'], 'Preflight changed during shard execution')
            names.append('preflight.json')
        for item in selected:
            names += stage_files(item[0] + '-compile') + stage_files(item[0])
        record.update(status='passed', checkedAt=datetime.now(timezone.utc).isoformat(),
                      baseline=whole['verification-results'], verus=whole['verus'], mutations=controls,
                      files={name: digest(safe_file(output, name)) for name in names})
        supervisor.check()
        save(output / 'shard.json', record)
        print(f'Full-crate shard {index + 1}/{count} passed: {len(selected)} controls. Not complete release evidence.')
    except BaseException as error:
        record.update(status='failed', failure=f'{type(error).__name__}: {error}')
        save(output / 'shard.json', record)
        raise
    return record


def validate_cleanup(metadata, stem):
    cleanup = metadata.get('cleanup', {})
    pid = metadata.get('pid')
    require(type(pid) is int and pid > 0 and isinstance(cleanup, dict)
            and cleanup.get('leaderReaped') is True
            and cleanup.get('observationMethod') in {'waitid', 'kqueue'}
            and not any(key.endswith('Error') for key in cleanup),
            'Incomplete process cleanup evidence: ' + stem)
    snapshots = cleanup.get('snapshots')
    require(isinstance(snapshots, list) and len(snapshots) >= 3
            and all(isinstance(item, dict) for item in snapshots)
            and [item.get('phase') for item in snapshots[:2]] == ['before-cleanup', 'before-kill']
            and all(item.get('phase') == 'after-kill' for item in snapshots[2:]),
            'Incomplete process cleanup snapshots: ' + stem)
    for snapshot in snapshots:
        members = snapshot.get('members')
        require(isinstance(members, list) and all(isinstance(member, dict)
                and type(member.get('pid')) is int and member['pid'] > 0
                and type(member.get('groupId')) is int and member['groupId'] == pid
                and isinstance(member.get('state'), str) and member['state'] for member in members),
                'Invalid process cleanup members: ' + stem)
        require(any(member['pid'] == pid for member in members),
                'Cleanup snapshot lacks retained group leader: ' + stem)
    require(all(member['state'].startswith('Z') for member in snapshots[-1]['members']),
            'Live process-group members remain after cleanup: ' + stem)


def stage(directory, stem, record, expected_source, *, compile_only=False):
    validate_execution(record.get('execution'), compile_timeout=compile_only)
    for name in stage_files(stem):
        require(digest(safe_file(directory, name)) == record['files'].get(name),
                'Changed stage bytes: ' + name)
    metadata = read_json(directory / (stem + '.meta.json'))
    require(metadata.get('schema') == 'cordis.negative-stage/v1'
            and metadata.get('status') == 'completed' and type(metadata.get('returncode')) is int
            and metadata.get('compileOnly') is compile_only
            and metadata.get('sourceSha256') == expected_source
            and type(metadata.get('threads')) is int
            and metadata['threads'] == record['execution']['threadsPerWorker']
            and type(metadata.get('timeoutSeconds')) is int
            and metadata['timeoutSeconds'] == record['execution'][
                'compileTimeoutSeconds' if compile_only else 'timeoutSeconds']
            and metadata.get('diagnostics') is True
            and type(metadata.get('durationSeconds')) in {int, float}
            and math.isfinite(metadata['durationSeconds']) and metadata['durationSeconds'] >= 0
            and metadata.get('signal') is None and 'cancellationReason' not in metadata
            and 'cleanupError' not in metadata and 'primaryStatus' not in metadata and 'error' not in metadata,
            'Incomplete or mismatched stage metadata: ' + stem)
    validate_cleanup(metadata, stem)
    command = metadata.get('command')
    require(isinstance(command, list) and len(command) >= 2
            and all(isinstance(value, str) for value in command)
            and Path(command[0]).name == 'verus' and Path(command[1]).name == 'lib.rs',
            'Invalid verifier command: ' + stem)
    flags = ['--crate-name', 'cordis_negative', '--crate-type=lib', '--edition=2021',
             '--no-cheating', '--output-json', '--triggers-mode', 'silent',
             '--num-threads', str(record['execution']['threadsPerWorker']), '--trace', '--time']
    if compile_only:
        flags += ['--no-verify', '--compile', '-o', str(Path(command[1]).parent / 'compile-check.rlib')]
    require(command[2:] == flags, 'Unexpected or scoped verifier flags: ' + stem)
    result = subprocess.CompletedProcess(command, metadata['returncode'],
                                         (directory / (stem + '.stdout.json')).read_text(),
                                         (directory / (stem + '.stderr.txt')).read_text())
    # Reject ambiguous JSON even when the later contract parser needs only a subset.
    data = read_json(directory / (stem + '.stdout.json'))
    if compile_only:
        stats = data.get('verification-results', {})
        require(result.returncode == 0 and stats.get('success') is True
                and type(stats.get('errors')) is int and stats['errors'] == 0
                and stats.get('encountered-vir-error') is False,
                'Mutant compilation did not succeed: ' + stem)
    return result


def collect(input_directory, output):
    checks = checker()
    binary, _ = checks.toolchain()
    expected_binding = binding(checks, binary)
    manifest = checks.mutation_manifest()
    paths = sorted(input_directory.rglob('shard.json'))
    require(paths, 'No full-crate shard reports found')
    reports = [read_json(path) for path in paths]
    for path in paths:
        parts = path.relative_to(input_directory).parts
        require(not input_directory.is_symlink()
                and all(not (input_directory / Path(*parts[:length])).is_symlink()
                        for length in range(1, len(parts) + 1)),
                'Symlinked shard evidence is not accepted')
    count = reports[0].get('shard', {}).get('count')
    assigned(manifest, 0, count)
    require(len(reports) == count, 'Missing or additional full-crate shards')
    indices = [record.get('shard', {}).get('index') for record in reports]
    require(all(type(index) is int for index in indices) and sorted(indices) == list(range(count)),
            'Duplicate or missing shard indices')
    modes = {record.get('baselineMode') for record in reports}
    require(len(modes) == 1 and modes.issubset({'local', 'preflight'}), 'Mixed or invalid baseline modes')
    baseline_mode = modes.pop()
    preflight_hash = None
    rows, baseline, version, inputs = {}, None, None, []
    with tempfile.TemporaryDirectory(prefix='cordis-collect-sources-') as temporary:
        original = Path(temporary) / 'source'
        shutil.copytree(ROOT / 'crates/cordis-kernel/src', original)
        baseline_source = checks.source_fingerprint(original)
        for path, record in sorted(zip(paths, reports), key=lambda pair: pair[1]['shard']['index']):
            selected = assigned(manifest, record['shard']['index'], count)
            names = [item[0] for item in selected]
            require(record.get('schema') == SCHEMA and record.get('status') == 'passed'
                    and record.get('binding') == expected_binding and record['shard'].get('count') == count
                    and record['shard'].get('names') == names,
                    'Shard source/toolchain/run identity or selection differs')
            execution = record.get('execution', {})
            validate_execution(execution, compile_timeout=True)
            expected_files = set(stage_files('baseline'))
            if baseline_mode == 'preflight':
                expected_files.add('preflight.json')
            for name in names:
                expected_files.update(stage_files(name + '-compile') + stage_files(name))
            require(set(record.get('files', {})) == expected_files, 'Incomplete or additional stage evidence')
            if baseline_mode == 'preflight':
                _, whole, identity = validate_preflight(path.parent, expected_binding, baseline_source, execution)
                require(record.get('preflightSha256') == identity
                        and record['files'].get('preflight.json') == identity,
                        'Changed preflight manifest bytes or identity')
                require(all(record['files'][name] == digest(safe_file(path.parent, name))
                            for name in stage_files('baseline')), 'Changed stage bytes: reused baseline')
                if preflight_hash is None:
                    preflight_hash = identity
                require(identity == preflight_hash, 'Shards used different preflight evidence')
            else:
                require('preflightSha256' not in record, 'Local baseline cannot claim preflight evidence')
                whole = positive(stage(path.parent, 'baseline', record, baseline_source))
            require(record.get('baseline') == whole['verification-results'] and record.get('verus') == whole['verus'],
                    'Baseline summary differs from raw verifier output')
            if baseline is None:
                baseline, version = whole['verification-results'], whole['verus']
            require(whole['verification-results'] == baseline and whole['verus'] == version,
                    'Shard baseline or verifier version differs')
            accepted = []
            for name, relative, old, new in selected:
                source = original / relative
                text = source.read_text()
                require(text.count(old) == 1, 'Mutation no longer matches current sources: ' + name)
                try:
                    source.write_text(text.replace(old, new))
                    mutant_source = checks.source_fingerprint(original)
                finally:
                    source.write_text(text)
                stage(path.parent, name + '-compile', record, mutant_source, compile_only=True)
                result = stage(path.parent, name, record, mutant_source)
                accepted.append(checks.rejected_result(name, result))
                require(name not in rows, 'Duplicate mutation evidence: ' + name)
                rows[name] = accepted[-1]
            require(record.get('mutations') == accepted, 'Mutation summary differs from raw verifier output')
            inputs.append({'index': record['shard']['index'], 'reportSha256': digest(path),
                           'execution': execution, 'files': record['files']})
    require(binding(checks, binary) == expected_binding, 'Sources/toolchain changed during collection')
    summary = {'verus': version, 'baseline': baseline,
               'execution': {'mode': 'full-crate-shards', 'shardCount': count,
                             'binding': expected_binding, 'baselineMode': baseline_mode,
                             'preflightSha256': preflight_hash, 'shards': inputs},
               'mutations': [rows[item[0]] for item in manifest]}
    recorder().validate_negative_report(summary, [item[0] for item in manifest])
    # The recorder removes an earlier report before invoking the quality gate.
    output.mkdir(parents=True, exist_ok=True)
    require(not (output / 'report.json').exists(), 'Refusing to overwrite a negative report')
    save(output / 'report.json', summary)
    print(f"OK unmodified kernel: {baseline['verified']} verified, 0 errors", flush=True)
    print(f'Collected {len(manifest)} complete-crate negative controls from {count} fresh matching shards.')
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='action', required=True)
    preflight = commands.add_parser('preflight')
    preflight.add_argument('--output', type=Path, required=True)
    preflight.add_argument('--threads', type=int)
    preflight.add_argument('--cpu-budget', type=int)
    preflight.add_argument('--timeout', type=int, default=2400)
    run = commands.add_parser('run')
    run.add_argument('--shard-index', type=int, required=True)
    run.add_argument('--shard-count', type=int, required=True)
    run.add_argument('--output', type=Path, required=True)
    run.add_argument('--jobs', type=int, default=1)
    run.add_argument('--threads', type=int)
    run.add_argument('--cpu-budget', type=int)
    run.add_argument('--timeout', type=int, default=2400)
    run.add_argument('--compile-timeout', type=int, default=300)
    run.add_argument('--preflight', type=Path, help='Reuse raw baseline evidence from this CI run/attempt only')
    gather = commands.add_parser('collect')
    gather.add_argument('--input', type=Path, required=True)
    gather.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.action == 'preflight':
        run_preflight(args.output, threads=args.threads, cpu_budget=args.cpu_budget, timeout=args.timeout)
    elif args.action == 'run':
        require(args.timeout > 0, 'Timeout must be positive')
        run_shard(args.shard_index, args.shard_count, args.output, jobs=args.jobs,
                  threads=args.threads, cpu_budget=args.cpu_budget, timeout=args.timeout,
                  compile_timeout=args.compile_timeout, preflight=args.preflight)
    else:
        collect(args.input, args.output)


if __name__ == '__main__':
    main()
