"""Synthetic acceptance records for fail-closed validator tests, never evidence."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LOCK = json.loads((ROOT / 'toolchain.lock.json').read_text())


def positive(sources=None):
    return {
        'schema': 'cordis-verus.positive-proof/v1', 'status': 'passed', 'returncode': 0,
        'command': ['./scripts/verify.sh', '--num-threads', '2', '--triggers-mode', 'silent', '--output-json', '--time'],
        'compiled': True, 'noCheating': True,
        'proof': {'success': True, 'errors': 0, 'verified': 40, 'encountered-error': False,
                  'encountered-vir-error': False, 'is-verifying-entire-crate': True},
        'verus': {key: LOCK['verus'][key] for key in ('version', 'commit')},
        'sourceHashes': sources or {'fixture.rs': 'a' * 64},
        'toolHashes': {name: 'b' * 64 for name in ('verus', 'rust_verify', 'z3', 'vstd.vir')},
        'artifact': {'path': 'target/verus/libcordis_kernel.rlib', 'bytes': 8, 'sha256': 'c' * 64},
        'stdoutSha256': 'd' * 64, 'stderrSha256': 'e' * 64,
    }


def release(sources=None):
    proof = positive(sources)
    return {'schema': 'cordis-verus.verification/v4', 'status': 'passed', 'releaseAcceptance': True,
            'proof': proof['proof'], 'proofExecution': proof, 'verus': proof['verus'],
            'sha256': proof['sourceHashes'], 'paperCoverage': {'completionClaimed': False},
            'negativeControls': {'status': 'not_run', 'requiredForRelease': False,
                                 'workflow': '.github/workflows/negative-regression.yml'},
            'tests': {'total': 4, 'nodeCompatibility': {'tests': 1, 'pass': 1, 'fail': 0, 'cancelled': 0, 'skipped': 0, 'todo': 0}},
            'nodeBuild': {'schema': 'cordis-verus.node-build/v1'},
            'npmDistribution': {'schema': 'cordis-verus.npm-package/v1', 'status': 'passed', 'offline': True}}


def quality_log(marker):
    return ('verification results:: 40 verified, 0 errors\nBEGIN WORKSPACE TESTS\n'
            'Running tests/lifecycle.rs (target/lifecycle)\ntest result: ok. 4 passed; 0 failed;\n'
            'Doc-tests cordis\ntest result: ok. 2 passed; 0 failed;\nEND WORKSPACE TESTS\n'
            'BEGIN NODE COMPATIBILITY TESTS\n# tests 1\n# pass 1\n# fail 0\n# cancelled 0\n# skipped 0\n# todo 0\n'
            'END NODE COMPATIBILITY TESTS\n' + marker + '\n')
