#!/usr/bin/env python3
"""Check whole-paper work allocation and review links, not proof completion.

Original claim statuses come only from paper-obligations.json. A valid plan
does not discharge a theorem, an environment assumption or a refinement bridge.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
PLAN = Path('docs/paper-refinement-plan.json')
LEDGER = Path('docs/paper-obligations.json')
VIEW = Path('docs/paper-refinement-map.md')
MILESTONES = ('R0', 'R1', 'R2', 'R3', 'R4', 'R5')
OBLIGATIONS = {'whole-lifecycle', 'corrected-specification', 'executable-simulation', 'host-boundary'}
ROLES = {
    'proof': r'\bproof\s+fn\s+',
    'contract': r'\b(?:open\s+|closed\s+)?spec\s+fn\s+',
    'execution': r'^\s*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?fn\s+',
    'host': r'^\s*(?:pub(?:\([^)]*\))?\s+)?(?:async\s+)?fn\s+',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def texts(values, label):
    require(isinstance(values, list) and values, f'Missing {label}')
    require(all(isinstance(value, str) and value.strip() for value in values), f'Invalid {label}')


def review_evidence(evidence, root, label):
    relative = Path(evidence['file'])
    path = (root / relative).resolve()
    require(not relative.is_absolute() and path.is_relative_to(root.resolve()) and path.suffix == '.rs'
            and path.is_file(), f'Invalid review source: {label}/{relative}')
    role = evidence['role']
    require(role in ROLES, f'Invalid review role: {label}')
    if role in {'execution', 'proof', 'contract'}:
        require(relative.parts[:3] == ('crates', 'cordis-kernel', 'src'), f'Checked code must be in the verified kernel: {label}')
    symbol = evidence['symbol']
    require(isinstance(symbol, str) and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', symbol), f'Invalid symbol: {label}')
    require(re.search(ROLES[role] + re.escape(symbol) + r'\b', path.read_text(), re.M), f'Missing {role} symbol: {relative}::{symbol}')


def validate(data, ledger, root=ROOT):
    require(data.get('schema') == 'cordis-verus.paper-refinement-plan/v1', 'Unknown plan schema')
    require(data.get('ledger') == str(LEDGER) and data.get('paper') == ledger['paper'], 'Plan is not bound to the paper ledger')
    require(bool(data.get('claim')), 'Missing inventory claim boundary')
    milestones = data['milestones']
    require([m['id'] for m in milestones] == list(MILESTONES), 'Expected ordered milestones R0 through R5')
    graph = {}
    for milestone in milestones:
        mid = milestone['id']
        require(milestone.get('status') in {'planned', 'in_progress', 'complete'}, f'Invalid milestone status: {mid}')
        require(bool(milestone.get('title')), f'Missing title: {mid}')
        texts(milestone.get('exitCriteria'), f'exit criteria: {mid}')
        dependencies = milestone['dependsOn']
        require(isinstance(dependencies, list) and len(dependencies) == len(set(dependencies))
                and set(dependencies) <= set(MILESTONES), f'Invalid dependencies: {mid}')
        graph[mid] = dependencies
    visited, active = set(), set()

    def visit(mid):
        require(mid not in active, f'Cyclic milestone dependency: {mid}')
        if mid in visited:
            return
        active.add(mid)
        for dependency in graph[mid]:
            visit(dependency)
        active.remove(mid)
        visited.add(mid)

    for mid in MILESTONES:
        visit(mid)
    require([item['id'] for item in ledger['items']] == list(range(1, 82)), 'Incomplete original ledger')
    require({i['id'] for i in ledger['integrationObligations']} == OBLIGATIONS, 'Original integration obligations changed')
    ids, covered = set(), []
    for package in data['workPackages']:
        pid = package['id']
        require(isinstance(pid, str) and re.fullmatch(r'[a-z][a-z-]*', pid) and pid not in ids, 'Invalid/duplicate work package')
        ids.add(pid)
        for field in ('title', 'currentCoverage', 'openGap', 'nextAction'):
            require(isinstance(package.get(field), str) and package[field].strip(), f'Missing {field}: {pid}')
        for field in ('premises', 'acceptance', 'milestones'):
            texts(package.get(field), f'{field}: {pid}')
        require(len(package['milestones']) == len(set(package['milestones']))
                and set(package['milestones']) <= set(MILESTONES), f'Invalid work package milestones: {pid}')
        items = package['paperItems']
        require(isinstance(items, list) and items and all(type(item) is int and 1 <= item <= 81 for item in items), f'Invalid paper items: {pid}')
        covered.extend(items)
        require(bool(package.get('reviewPath')), f'Missing review path: {pid}')
        for evidence in package['reviewPath']:
            review_evidence(evidence, root, pid)
    require(sorted(covered) == list(range(1, 82)), 'Every paper item needs exactly one primary work package')
    integration = data['integration']
    require(len(integration) == 4 and {i['id'] for i in integration} == OBLIGATIONS, 'All four integration obligations need exactly one owner record')
    for obligation in integration:
        texts(obligation.get('milestones'), f'integration milestones: {obligation["id"]}')
        require(len(obligation['milestones']) == len(set(obligation['milestones']))
                and set(obligation['milestones']) <= set(MILESTONES), 'Invalid integration milestone')
    if milestones[1]['status'] == 'complete':
        interpretation = data.get('r1Interpretation', {})
        require(interpretation.get('profile') == 'finite-strict-context/v1'
                and interpretation.get('originalPaperEquivalent') is False,
                'R1 completion requires an explicit strict interpretation, not original-paper equivalence')
        for field in ('carrier', 'executableProfile', 'remainingBoundary'):
            require(isinstance(interpretation.get(field), str) and interpretation[field].strip(), f'Missing R1 {field}')
        require(bool(milestones[1].get('completionScope')), 'Missing R1 completion scope')
        revisions = interpretation.get('revisions', [])
        require(len(revisions) == 3 and {r['id'] for r in revisions} == {'R1-CONTEXT', 'R1-DOMAIN', 'R1-FIELDS'},
                'R1 requires all three explicit semantic revisions')
        required = {
            'R1-CONTEXT': {('reified_context.rs', 'nontrivial_carrier'), ('reified_context.rs', 'reified_representation')},
            'R1-DOMAIN': {('guarded_components.rs', 'member_is_component'), ('reified_context.rs', 'root_component'),
                          ('typed_child_domain.rs', 'no_single_recovery_and_admission_relation')},
            'R1-FIELDS': {('reified_context.rs', 'function_correspondence'), ('inspected_run.rs', 'run_inspected')},
        }
        for revision in revisions:
            require(bool(revision.get('decision')), 'Missing R1 revision decision')
            require(revision.get('paperItems') and all(type(n) is int and 1 <= n <= 81 for n in revision['paperItems']),
                    'Invalid R1 original-paper references')
            review = revision.get('reviewPath', [])
            require(required[revision['id']] <= {(Path(e['file']).name, e['symbol']) for e in review},
                    'Missing R1 semantic or executable evidence')
            for evidence in review:
                review_evidence(evidence, root, revision['id'])
            if revision['id'] == 'R1-FIELDS':
                require(any(e['symbol'] == 'run_inspected' and e['role'] == 'execution' for e in review),
                        'R1 requires its actual executable caller')
    if milestones[-1]['status'] == 'complete':
        require(all(i['status'] not in {'missing', 'partial'} for i in ledger['items']), 'R5 cannot complete while original-paper audit outcomes remain open')
        require(all(i['status'] == 'proved' for i in ledger['integrationObligations']), 'R5 cannot complete while integration obligations remain open')


def render(data, ledger):
    counts = Counter(item['status'] for item in ledger['items'])
    lines = ['# Paper refinement work map', '',
             '[Milestones](paper-refinement-roadmap.md) · [里程碑（中文）](paper-refinement-roadmap.zh-CN.md)', '',
             'Generated from `paper-refinement-plan.json` and the original `paper-obligations.json`.',
             'This inventory checks allocation and source symbols. It does not establish a semantic bridge, prove a caller precondition, or certify paper completion.', '',
             'Original-paper audit: ' + ', '.join(f'{key} {value}' for key, value in sorted(counts.items())) + '.', '',
             '## Milestones', '', '| ID | Goal | Status | Depends on |', '| --- | --- | --- | --- |']
    for milestone in data['milestones']:
        lines.append(f'| {milestone["id"]} | {milestone["title"]} | {milestone["status"]} | {", ".join(milestone["dependsOn"]) or "—"} |')
    if data['milestones'][1]['status'] == 'complete':
        interpretation = data['r1Interpretation']
        lines += ['', 'R1 completion scope: ' + data['milestones'][1]['completionScope'], '',
                  '[R1 interpretation and reproduction](r1-semantics.md) · [中文](r1-semantics.zh-CN.md)', '',
                  'Carrier: ' + interpretation['carrier'], '', 'Executable profile: ' + interpretation['executableProfile'], '',
                  'Explicit revisions:', '']
        lines += ['- ' + r['id'] + ': ' + r['decision'] for r in interpretation['revisions']]
        lines += ['', 'Remaining boundary: ' + interpretation['remainingBoundary']]
    lines += ['', '## Work packages', '']
    owners = {}
    for package in data['workPackages']:
        for item in package['paperItems']:
            owners[item] = package
        lines += [f'### {package["id"]}', '', package['title'] + ' — ' + ', '.join(package['milestones']), '',
                  '**Current coverage:** ' + package['currentCoverage'], '', '**Open gap:** ' + package['openGap'], '',
                  '**Next action:** ' + package['nextAction'], '', '**Premises to discharge or identify:**', '']
        lines += ['- ' + text for text in package['premises']]
        lines += ['', '**Acceptance:**', ''] + ['- ' + text for text in package['acceptance']]
        lines += ['', '**Review path** (source roles, not a proof of calling relationships):', '']
        lines += [f'- {e["role"]}: [{e["symbol"]}](../{e["file"]})' for e in package['reviewPath']]
        lines.append('')
    lines += ['## Every numbered item', '', '| Paper item | Original status | Primary work package | Milestones |', '| --- | --- | --- | --- |']
    for item in ledger['items']:
        package = owners[item['id']]
        lines.append(f'| {item["kind"]} {item["id"]}: {item["title"]} | {item["status"]} | [{package["id"]}](#{package["id"]}) | {", ".join(package["milestones"])} |')
    lines += ['', '## Integration obligations', '', '| Obligation | Original status | Milestones |', '| --- | --- | --- |']
    status = {i['id']: i['status'] for i in ledger['integrationObligations']}
    lines += [f'| {i["id"]} | {status[i["id"]]} | {", ".join(i["milestones"])} |' for i in data['integration']]
    lines += ['', 'R0 completion means this planning baseline is recorded. R1–R5 require their own semantic and implementation evidence.',
              'Original refutations remain refuted. The original `check-paper-coverage.py --require-complete` gate is unchanged.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='Regenerate the work map')
    args = parser.parse_args()
    try:
        data = json.loads((ROOT / PLAN).read_text())
        ledger = json.loads((ROOT / LEDGER).read_text())
        validate(data, ledger)
        expected = render(data, ledger)
        if args.write:
            (ROOT / VIEW).write_text(expected)
        else:
            require((ROOT / VIEW).is_file() and (ROOT / VIEW).read_text() == expected, 'Generated paper-refinement-map.md is stale; use --write')
        print('Paper refinement plan: 81/81 items, 4/4 integration obligations; allocation, dependency and source checks passed. Not a proof-completion result.')
        return 0
    except (OSError, KeyError, TypeError, ValueError) as error:
        print(f'Paper refinement plan error: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
