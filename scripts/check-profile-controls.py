#!/usr/bin/env python3
"""Check a fixed control profile; not full regression or acceptance."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent


def module(name, filename):
    path = ROOT / 'scripts' / filename
    spec = importlib.util.spec_from_file_location(name, path)
    loaded = importlib.util.module_from_spec(spec)
    exec(compile(path.read_bytes(), str(path), 'exec'), loaded.__dict__)
    return loaded


PROFILES = {
    'update-recovery': ['cleanup-dispatch-promotes-failure', 'cleanup-dispatch-bypasses-receipt', 'cleanup-queue-discards-retained-payload', 'r2-value-ignores-inverse-depth', 'r2-shared-child-splits-request-inverse'],
    'r01-exclusive': ['r01-exclusive-source-ignores-input', 'r01-exclusive-source-ignores-allocation', 'r01-typed-seed-ignores-inverse-debt', 'r01-typed-seed-ignores-revision', 'r01-typed-call-ignores-source-history'],
    'episode': ['r3-replay-discards-foreign-history', 'r3-recovery-discards-stored-receipts'],
    'production': ['r3-managed-gap-ignores-writes', 'r3-typed-restores-consumed-head'],
    'final-cut': ['r3-final-cut-skips-foreign', 'r3-final-cut-skips-child'],
    'controlled-effects': ['r3-controlled-replay-admits-callback', 'r3-controlled-evaluation-uses-wrong-input'],
    'source-schedule': ['r3-source-call-fabricates-position', 'r3-typed-landing-skips-version'],
    'scalar-landing': ['r3-scalar-landing-ignores-depth'],
    'target-execution': ['r3-target-execution-skips-interpreter', 'r3-target-execution-drops-source-body'],
    'source-chain': ['r3-source-chain-skips-command', 'r3-source-chain-skips-unload-source'],
    'control-replay': ['r3-control-replay-keeps-source-allocation', 'r3-control-replay-skips-executable-begin'],
    'effect-deletion': ['r3-effect-deletion-skips-read', 'r3-effect-deletion-keeps-source-index'],
    'deletion': ['r3-deletion-retains-selected-actions', 'r3-deletion-skips-child-birth'],
    'host': ['r3-host-skips-append-history', 'r3-host-drops-terminal-history'],
    'observation': ['r3-observation-skips-publication', 'r3-observation-skips-pending'],
}


def load_profile(profile):
    if profile not in PROFILES:
        raise ValueError('Unknown control profile: ' + profile)
    stem = profile if profile in ('r01-exclusive', 'update-recovery') else f'r3-{profile}'
    manifest_path = ROOT / f'scripts/negative-controls.{stem}.json'
    h = module('profile_scoped', 'check-negative-scoped.py')
    canonical = module('profile_canonical', 'check-negative.py')
    manifest = h.load_json(manifest_path)
    h.validate_manifest(manifest)
    h.require([c['name'] for c in manifest['cases']] == PROFILES[profile], 'Control selection changed')
    mutations = {name: (file, old, new) for name, file, old, new in canonical.mutation_manifest()}
    for case in manifest['cases']:
        m = case['mutation']
        h.require(mutations.get(case['name']) == (m['file'], m['old'], m['new']),
                  'Mutation differs from the canonical control')
    h.preflight(manifest, ROOT / 'crates/cordis-kernel/src')
    return stem, manifest_path, manifest, mutations, h


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('profile', choices=PROFILES, help='fixed audited control selection')
    parser.add_argument('--check', action='store_true',
                        help='check selection, mutations and source anchors only; no proof execution')
    args = parser.parse_args(argv)
    stem, manifest_path, manifest, mutations, h = load_profile(args.profile)
    cases = manifest['cases']
    if args.check:
        print(f'{args.profile}: {len(cases)} control anchors checked; proofs not run.')
        return
    output = ROOT / f'target/{stem}-controls'
    bound_files = [Path(__file__), manifest_path, ROOT / 'scripts/check-negative-scoped.py',
                   ROOT / 'scripts/check-negative.py', ROOT / 'toolchain.lock.json',
                   ROOT / 'scripts/install-verus.py']
    digests = lambda: {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in bound_files}
    harness = digests()
    kernel = h.source_hashes(ROOT / 'crates/cordis-kernel/src')
    binary, environment, tool = h.tools_for(ROOT)
    output.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix='evidence-', dir=output))
    baseline = directory / 'baseline'
    shutil.copytree(ROOT / 'crates/cordis-kernel/src', baseline)
    h.require(h.source_hashes(baseline) == kernel, 'source changed while snapshotting')
    h.preflight(manifest, baseline)
    report = dict(schema=f'cordis-verus.{stem}-controls/v1', status='running',
                  fullNegativeControls='not_run', scopedCalibration='not_run',
                  releaseAcceptance=False, paperCompletion=False, wholeCrate=False,
                  selectedControlCount=len(cases), canonicalControlCount=len(mutations),
                  kernelSha256=kernel, harnessSha256=harness, tool=tool,
                  evidenceDirectory=directory.name, cases=[])

    def save():
        (directory / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')

    def invoke(label, tree, kind, case):
        artifact = directory / (label + '.rlib')
        h.verify_tool_artifacts(tool)
        command = h.command(binary, tree, kind, case['targets'] if kind == 'selected' else (), 2, artifact,
                            expected_failures=case['expectedFailures'])
        result = h.run(command, environment, directory / label, 600)
        h.verify_tool_artifacts(tool)
        return result, artifact

    save()
    try:
        for case in cases:
            name = case['name']
            print('Selected control: ' + name, flush=True)
            row = dict(name=name, case=case)
            report['cases'].append(row)
            row['positive'], _ = invoke(name + '-positive', baseline, 'selected', case)
            h.validate_positive(row['positive'], directory, entire=False, expected_tool=tool,
                                targets=case['targets'], expected_failures=case['expectedFailures'])
            mutant = directory / name
            row['mutantSha256'] = h.mutate(case, baseline, mutant)
            row['compile'], artifact = invoke(name + '-compile', mutant, 'compile', case)
            h.validate_compile(row['compile'], directory, artifact)
            row['negative'], _ = invoke(name + '-mutant', mutant, 'selected', case)
            h.validate_rejection(row['negative'], directory, case, mutant, tool)
            h.require(h.source_hashes(mutant) == row['mutantSha256']
                      and h.source_hashes(baseline) == kernel
                      and h.source_hashes(ROOT / 'crates/cordis-kernel/src') == kernel
                      and digests() == harness, 'source or harness changed during checks')
            row['status'] = 'passed'
            save()
        report['status'] = 'passed'
        save()
        print('Selected controls passed: ' + str(output / 'report.json'), flush=True)
    except BaseException as error:
        report.update(status='failed', failure=f'{type(error).__name__}: {error}')
        save()
        raise


if __name__ == '__main__':
    main()
