#!/usr/bin/env python3
"""Display negative-check progress even when raw artifact upload fails.

This is a diagnostic view of reported results, not an evidence collector. Missing
or malformed reports remain visible; a summary never grants release acceptance.
"""
import argparse
import html
import json
from pathlib import Path


def read_report(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError('Report is missing or is a symlink: ' + path.name)
    if path.stat().st_size > 4 * 1024 * 1024:
        raise ValueError('Report is too large: ' + path.name)
    def unique(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('Duplicate report key: ' + str(key))
            result[key] = value
        return result
    report = json.loads(path.read_text(), object_pairs_hook=unique)
    if not isinstance(report, dict):
        raise ValueError('Report must be an object: ' + path.name)
    return report


def text(value, limit=600):
    value = str(value)
    return value if len(value) <= limit else value[:limit] + ' [truncated]'


def summarize(directory):
    summary = {'schema': 'cordis.negative-summary/v1', 'releaseAcceptance': False,
               'status': 'unavailable', 'mode': 'unknown', 'cases': [], 'notices': [],
               'purpose': 'Reported diagnostics only; raw artifacts are required for evidence validation.'}
    try:
        path = directory / 'shard.json'
        if not path.exists():
            path = directory / 'preflight.json'
        record = read_report(path)
        summary['report'] = path.name
        summary['status'] = text(record.get('status', 'unknown'))
        binding = record.get('binding', {})
        origin = binding.get('origin') or {}
        summary['sourceCommit'] = text(origin.get('GITHUB_SHA', 'unknown'))
        summary['runId'] = text(origin.get('GITHUB_RUN_ID', 'unknown'))
        summary['runAttempt'] = text(origin.get('GITHUB_RUN_ATTEMPT', 'unknown'))
        summary['host'] = binding.get('host', {})
        baseline = record.get('baseline', {})
        summary['baseline'] = {key: baseline.get(key) for key in ('verified', 'errors', 'is-verifying-entire-crate')}
        if 'failure' in record:
            summary['failure'] = text(record['failure'])
        if path.name == 'preflight.json':
            summary['mode'] = 'preflight'
            return summary
        shard = record['shard']
        names = shard['names']
        if not isinstance(names, list) or not all(isinstance(name, str) for name in names) or len(set(names)) != len(names):
            raise ValueError('Invalid selected-control names')
        summary['shard'] = {'index': shard['index'], 'count': shard['count']}
        # Start every selected item as unreported, so interrupted work is visible.
        summary['cases'] = [{'name': text(name), 'status': 'unreported'} for name in names]
        diagnostic_path = directory / 'diagnostic.json'
        diagnostic_mode = record.get('execution', {}).get('keepGoing', False) or diagnostic_path.exists()
        summary['mode'] = 'diagnostic' if diagnostic_mode else 'ordinary'
        if diagnostic_mode:
            diagnostic = read_report(diagnostic_path)
            rows = diagnostic['outcomes']
            if (diagnostic.get('schema') != 'cordis.negative-diagnostic/v1'
                    or diagnostic.get('releaseAcceptance') is not False
                    or not isinstance(rows, list) or [row['name'] for row in rows] != names
                    or any(row.get('status') not in {'pending', 'running', 'passed', 'failed', 'interrupted'}
                           or type(row.get('attempted')) is not bool for row in rows)):
                raise ValueError('Invalid or mismatched diagnostic outcomes')
            counts = {'selected': len(rows), 'attempted': sum(row['attempted'] for row in rows),
                      'passed': sum(row['status'] == 'passed' for row in rows),
                      'failed': sum(row['status'] == 'failed' for row in rows),
                      'notRun': sum(not row['attempted'] for row in rows)}
            if counts != diagnostic.get('counts'):
                raise ValueError('Diagnostic counts differ from outcomes')
            summary['coverage'] = counts
            summary['complete'] = diagnostic.get('complete') is True and bool(rows) and all(
                row['attempted'] and row['status'] in {'passed', 'failed'} and not row.get('fatal', False) for row in rows)
            summary['diagnosticStatus'] = text(diagnostic.get('status', 'unknown'))
            summary['cases'] = [{key: text(row[key]) for key in ('name', 'status')} |
                                ({'error': text(row['error'].get('message', 'unknown'))} if 'error' in row else {})
                                for row in rows]
        else:
            passed = {row['name'] for row in record.get('mutations', [])}
            if not passed.issubset(set(names)):
                raise ValueError('Reported controls differ from selection')
            summary['cases'] = [{'name': text(name), 'status': 'reported-passed' if name in passed else 'unreported'} for name in names]
    except (OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        summary['status'] = 'incomplete-summary'
        summary['complete'] = False
        summary['notices'].append(text(error))
    return summary


def markdown(summary):
    def cell(value):
        return html.escape(text(value)).replace('|', '&#124;').replace('\n', '<br>').replace('\r', '')
    lines = ['### Negative-check diagnostics', '',
             '**Diagnostic display only. This summary is not release evidence.**', '',
             f"Reported status: {cell(summary['status'])}; mode: {cell(summary['mode'])}."]
    if 'sourceCommit' in summary:
        lines += [f"Commit: {cell(summary['sourceCommit'])}; run: {cell(summary['runId'])}; attempt: {cell(summary['runAttempt'])}."]
    if 'baseline' in summary:
        baseline = summary['baseline']
        lines += [f"Baseline: {cell(baseline.get('verified'))} verified, {cell(baseline.get('errors'))} errors."]
    if 'coverage' in summary:
        lines += ['Coverage: ' + cell(json.dumps(summary['coverage'], sort_keys=True)) + '.',
                  'Collection complete: ' + str(summary['complete']).lower() + '.']
    if 'failure' in summary:
        lines += ['', 'Reported failure: ' + cell(summary['failure'])]
    for notice in summary['notices']:
        lines += ['', 'Summary notice: ' + cell(notice)]
    if summary['cases']:
        lines += ['', '| Control | Reported result | Detail |', '| --- | --- | --- |']
        lines += [f"| {cell(row['name'])} | {cell(row['status'])} | {cell(row.get('error', ''))} |" for row in summary['cases']]
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--github-summary', type=Path)
    args = parser.parse_args()
    summary = summarize(args.input)
    # One JSON line prevents report content from becoming workflow commands.
    print(json.dumps(summary, ensure_ascii=True), flush=True)
    if args.github_summary:
        with args.github_summary.open('a') as output:
            output.write(markdown(summary))
    # Existing verification and upload steps retain their own failure status.
    # An unavailable display cannot fabricate a verification result.


if __name__ == '__main__':
    main()
