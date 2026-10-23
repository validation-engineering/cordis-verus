#!/usr/bin/env python3
"""Generate and replay source-bound lifecycle evidence; not whole-paper acceptance."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from lifecycle import evidence as E
from lifecycle.oracle import check_native
from lifecycle.scenarios import generate_native, REQUIRED_NATIVE


def replay(args):
    output=E.ROOT/'target/lifecycle-campaign/replay'
    cases=json.loads(args.input.read_text())['cases']
    binary=args.binary
    if binary is None: binary,_=E.build_native(output,offline=args.offline)
    binary=binary.resolve()
    if args.binary_sha256 and E.digest(binary)!=args.binary_sha256:
        raise RuntimeError('Replay binary does not match the requested artifact')
    run,results=E.execute_native(binary,cases,output)
    checks=[check_native(c,r) for c,r in zip(cases,results)] if results else []
    passed=(len(checks)==len(cases) and bool(checks) and all(
        c['status']=='failed' and c.get('failure',{}).get('code')==args.expect_failure
        if args.expect_failure else c['status']=='passed' for c in checks))
    report={'status':'passed' if passed else 'failed','input':str(args.input.resolve()),
            'inputSha256':E.digest(args.input),'run':run,'checks':checks,
            'expectedFailure':args.expect_failure,'sourceHashes':E.inputs()}
    E.write_json(output/'report.json',report)
    print(json.dumps({'status':report['status'],'checks':checks},ensure_ascii=False))
    if not passed: raise RuntimeError('Replay did not meet the requested result')


def native_campaign(args):
    output = E.ROOT / 'target/lifecycle-campaign/native'
    before = E.inputs()
    report = E.new_report('provider-consumer-one-child/v1', before)
    report.update(seed=args.seed, requestedCases=args.cases, generator='native-lifecycle/1')
    E.write_json(output / 'report.json', report)
    try:
        cases = generate_native(args.seed, args.cases)
        E.write_json(output / 'scenarios.json', {'cases': cases})
        report['scenarioSha256'] = E.digest(output / 'scenarios.json')
        binary, build = E.build_native(output, offline=args.offline)
        report['build'] = build
        coverage, outcomes, categories = set(), Counter(), Counter()
        for start in range(0, len(cases), 8):
            batch = cases[start:start + 8]
            run, results = E.execute_native(binary, batch, output, f'batch-{start:04}')
            if results is None:
                raise RuntimeError('Native execution failed; see ' + run['stderr'])
            for case, result in zip(batch, results):
                check = check_native(case, result)
                report['cases'].append({'id': case['id'], 'category':case['category'], 'run':run, 'check':check})
                coverage.update(check.get('coverage', []))
                outcomes.update(check.get('outcomes', {}))
                categories[case['category']] += 1
            E.write_json(output / 'report.json', report)
            print(f'Native scenarios: {len(report["cases"])}/{len(cases)}', flush=True)
        report.update(coverage=sorted(coverage), requiredCoverage=sorted(REQUIRED_NATIVE),
                      outcomes=dict(outcomes), categories=dict(categories), attempted=len(cases),
                      executed=len(report['cases']), supported=len(cases), unsupported=0)
        if any(row['check']['status'] != 'passed' for row in report['cases']):
            raise RuntimeError('Native scenario guarantee failed; inspect per-case checks and raw traces')
        if not REQUIRED_NATIVE <= coverage or set(categories) != {'admitted','interference','invalid-commands'}:
            raise RuntimeError('Missing required supported scenario families or categories')
        if E.inputs() != before:
            raise RuntimeError('Source changed during campaign')
        report['status'] = 'passed'
        E.write_json(output / 'report.json', report)
        print('Native lifecycle campaign passed: ' + str(output / 'report.json'))
    except BaseException as error:
        report.update(status='failed', failure=f'{type(error).__name__}: {error}')
        E.write_json(output / 'report.json', report)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    native = sub.add_parser('native', help='generate and check actual Native root/Child execution')
    native.add_argument('--seed', type=int, default=260824)
    native.add_argument('--cases', type=int, default=96)
    native.add_argument('--offline', action='store_true')
    control=sub.add_parser('controls',help='pair the five exact mutations with behavior, reduction and strict proof checks')
    control.add_argument('--seed',type=int,default=260824)
    control.add_argument('--cases',type=int,default=12)
    control.add_argument('--offline',action='store_true')
    control.add_argument('--behavior-only',action='store_true',help='integration pilot only; cannot satisfy paired acceptance')
    playback=sub.add_parser('replay',help='replay saved full commands against a real Native executable')
    playback.add_argument('--input',type=Path,required=True)
    playback.add_argument('--binary',type=Path)
    playback.add_argument('--binary-sha256')
    playback.add_argument('--expect-failure')
    playback.add_argument('--offline',action='store_true')
    comparison=sub.add_parser('compare',help='compare the common public plugin profile against pinned Cordis')
    comparison.add_argument('--seed',type=int,default=260824)
    comparison.add_argument('--cases',type=int,default=48)
    comparison.add_argument('--build',action='store_true',help='rebuild the native Node artifact before comparison')
    comparison.add_argument('--offline',action='store_true')
    sub.add_parser('accept',help='audit final-source development, scenario, differential and paired-control records')
    args = parser.parse_args()
    if args.command == 'native': native_campaign(args)
    elif args.command == 'replay': replay(args)
    elif args.command == 'controls':
        if args.cases>256: parser.error('Controls accept at most 256 cases')
        from lifecycle.controls import run_controls
        run_controls(args)
    elif args.command == 'compare':
        from lifecycle.comparison import run_comparison
        run_comparison(args)
    elif args.command == 'accept':
        from lifecycle.acceptance import audit
        audit()


if __name__ == '__main__':
    main()
