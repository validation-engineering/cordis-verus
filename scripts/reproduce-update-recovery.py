#!/usr/bin/env python3
"""Reproduce actual update recovery; optionally run fresh scoped Verus proofs."""
import argparse
from contextlib import contextmanager, nullcontext
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / 'target/update-recovery'
PROOF_MODULES = (
    'lifecycle_state::cleanup',
    'lifecycle_state::cleanup::update',
    'lifecycle_state::execution',
    'cleanup_queue::completion',
    'reversible_value::managed::interleaving::history::lifecycle::callbacks',
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    paths = list((ROOT / 'crates').rglob('*.rs')) + list((ROOT / 'crates').rglob('Cargo.toml'))
    paths += [ROOT / name for name in ('Cargo.toml', 'Cargo.lock', 'rust-toolchain.toml',
              'toolchain.lock.json', 'scripts/verify.sh', 'scripts/toolchain-env.sh',
              'scripts/install-verus.py', 'scripts/reproduce-update-recovery.py')]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)}


def save(report):
    temporary = OUTPUT / 'report.tmp.json'
    temporary.write_text(json.dumps(report, indent=2) + '\n')
    temporary.replace(OUTPUT / 'report.json')


@contextmanager
def verifier_lease():
    # Pinned verifier platforms share the development/negative-control lease.
    import fcntl
    with Path('/tmp/cordis-local-verifier.lock').open('a') as lease:
        fcntl.flock(lease, fcntl.LOCK_EX)
        yield


def checked_proof(raw):
    stats = raw['verification-results']
    if (stats.get('success', True) is not True or stats['errors'] != 0 or stats['verified'] <= 0
            or stats['encountered-error'] is not False or stats['encountered-vir-error'] is not False):
        raise RuntimeError('Selected proof did not pass')
    if stats['is-verifying-entire-crate'] is not False:
        raise RuntimeError('Unexpected proof selection')
    checked = set()
    for module in raw['times-ms']['smt']['smt-run-module-times']:
        work = [f for f in module['function-breakdown'] if f['time-micros'] > 0 or f['rlimit'] > 0]
        if not work:
            continue
        name = module['module']
        if (not any(name == target or name.startswith(target + '::') for target in PROOF_MODULES)
                or any(f['success'] is not True for f in work)):
            raise RuntimeError('Proof work failed or ran outside the selected modules')
        checked.add(name)
    if not set(PROOF_MODULES).issubset(checked):
        raise RuntimeError('A selected module has no actual proof work')
    return stats, sorted(checked)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--offline', action='store_true')
    parser.add_argument('--proof', action='store_true', help='Also execute fresh selected kernel proofs')
    args = parser.parse_args()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    before = sources()
    report = {'schema': 'cordis-verus.update-recovery/v1', 'status': 'running',
              'scope': 'provider-consumer-one-child/v1', 'paperCompletion': False,
              'r01Completion': False, 'releaseAcceptance': False,
              'fullNegativeControls': 'not_run', 'proof': {'status': 'not_run'},
              'sourceHashes': before, 'runs': []}
    save(report)

    def run(label, command):
        print(f'Running {label}', flush=True)
        row = {'label': label, 'command': command}
        report['runs'].append(row)
        with verifier_lease() if label == 'proof' else nullcontext():
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=900)
        for name, contents in [('stdout', result.stdout), ('stderr', result.stderr)]:
            path = OUTPUT / f'{label}.{name}.txt'
            path.write_text(contents)
            row[name] = str(path.relative_to(ROOT))
            row[name + 'Sha256'] = digest(path)
        row['returncode'] = result.returncode
        save(report)
        if result.returncode:
            raise RuntimeError(f'{label} failed; see {row["stderr"]}')
        return result.stdout

    try:
        offline = ['--offline'] if args.offline else []
        for package, label in [('cordis-kernel', 'native'), ('cordis-verus', 'host')]:
            example = 'update_recovery_native' if label == 'native' else 'update_recovery'
            observed = json.loads(run(label, ['cargo', 'run', '--quiet', '--locked',
                                          *offline, '-p', package, '--example', example]))
            if (observed.get('status') != 'passed'
                    or observed.get('schema') != f'cordis-verus.update-recovery-{label}/v1'):
                raise RuntimeError(f'{label} did not complete the expected scenario')
            report[label] = observed
        run('tickets', ['cargo', 'test', '--locked', *offline, '-p', 'cordis-kernel',
                        '--test', 'cleanup_protocol'])
        if args.proof:
            if any(os.environ.get(name) for name in ('VERUS_Z3_PATH', 'VERUS_EXTRA_ARGS', 'RUSTFLAGS',
                                                    'RUSTC_WRAPPER', 'RUSTC_WORKSPACE_WRAPPER')):
                raise RuntimeError('Custom compiler/verifier overrides are not supported')
            # Keep this selected artifact separate from whole-kernel evidence.
            artifact = OUTPUT / 'libcordis_kernel.rlib'
            artifact.unlink(missing_ok=True)
            raw = json.loads(run('proof', ['bash', '-euc',
                 'source scripts/toolchain-env.sh\nexec "$VERUS" "$@"', 'update-recovery-proof',
                 'crates/cordis-kernel/src/lib.rs', '--crate-name', 'cordis_kernel',
                 '--crate-type=lib', '--edition=2021', '--no-cheating', '--compile',
                 '-o', str(artifact), '--num-threads', '2',
                 '--triggers-mode', 'silent', '--output-json', '--time',
                 *[argument for module in PROOF_MODULES for argument in ('--verify-module', module)]]))
            stats, checked = checked_proof(raw)
            pinned = json.loads((ROOT / 'toolchain.lock.json').read_text())['verus']
            if any(raw['verus'][key] != pinned[key] for key in ('version', 'commit')):
                raise RuntimeError('Selected proof does not use the pinned Verus version')
            if not artifact.is_file() or artifact.stat().st_size == 0:
                raise RuntimeError('Selected proof did not produce the executable kernel')
            report['proof'] = {'status': 'passed', 'wholeCrate': False,
                               'compiled': True, 'noCheating': True,
                               'artifact': str(artifact.relative_to(ROOT)), 'artifactSha256': digest(artifact),
                               'statistics': stats, 'modules': checked, 'verus': raw['verus']}
        if sources() != before:
            raise RuntimeError('Sources changed during reproduction; rerun on the final tree')
        report['status'] = 'passed'
        save(report)
        print('Passed: target/update-recovery/report.json (scoped evidence; R01 remains open)')
    except BaseException as error:
        report['status'] = 'failed'
        report['failure'] = f'{type(error).__name__}: {error}'
        save(report)
        raise


if __name__ == '__main__':
    main()
