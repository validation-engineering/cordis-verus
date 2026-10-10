"""Diagnostic output survives missing uploads without accepting partial evidence."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'summarize-negative.py'
spec = importlib.util.spec_from_file_location('negative_summary_test', SCRIPT)
SUMMARY = importlib.util.module_from_spec(spec)
exec(compile(SCRIPT.read_bytes(), str(SCRIPT), 'exec'), SUMMARY.__dict__)


class NegativeSummaryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.record = {'status': 'failed', 'binding': {'origin': {'GITHUB_SHA': 'fixture',
            'GITHUB_RUN_ID': '123', 'GITHUB_RUN_ATTEMPT': '2'}, 'host': {'os': 'fixture'}},
            'execution': {'keepGoing': True}, 'shard': {'index': 0, 'count': 1, 'names': ['first', 'second']},
            'baseline': {'verified': 40, 'errors': 0, 'is-verifying-entire-crate': True}}
        self.diagnostic = {'schema': 'cordis.negative-diagnostic/v1', 'releaseAcceptance': False,
            'status': 'failed', 'complete': True, 'outcomes': [
                {'name': 'first', 'status': 'failed', 'attempted': True, 'error': {'message': 'resource limit'}},
                {'name': 'second', 'status': 'passed', 'attempted': True}],
            'counts': {'selected': 2, 'attempted': 2, 'passed': 1, 'failed': 1, 'notRun': 0}}
        self.write()

    def write(self):
        (self.root / 'shard.json').write_text(json.dumps(self.record))
        (self.root / 'diagnostic.json').write_text(json.dumps(self.diagnostic))

    def test_completed_failures_remain_visible_in_console_and_job_summary(self):
        output = self.root / 'github-summary.md'
        result = subprocess.run(['python3', str(SCRIPT), '--input', str(self.root),
                                 '--github-summary', str(output)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report['coverage'], self.diagnostic['counts'])
        self.assertEqual(report['status'], 'failed')
        self.assertTrue(report['complete'])
        self.assertFalse(report['releaseAcceptance'])
        self.assertIn('first | failed | resource limit', output.read_text())
        self.assertIn('second | passed', output.read_text())
        self.assertFalse((self.root / 'report.json').exists())

    def test_interruption_keeps_unrun_controls_visible(self):
        self.diagnostic['status'] = 'interrupted'
        self.diagnostic['complete'] = False
        self.diagnostic['outcomes'][1] = {'name': 'second', 'status': 'pending', 'attempted': False}
        self.diagnostic['counts'].update(attempted=1, passed=0, notRun=1)
        self.write()
        result = SUMMARY.summarize(self.root)
        self.assertFalse(result['complete'])
        self.assertEqual(result['coverage']['notRun'], 1)
        self.assertEqual(result['cases'][1]['status'], 'pending')

    def test_missing_corrupt_and_mismatched_reports_never_display_complete(self):
        for content in ('not json', '{}', '{"outcomes":[],"outcomes":[]}'):
            with self.subTest(content=content):
                (self.root / 'diagnostic.json').write_text(content)
                result = SUMMARY.summarize(self.root)
                self.assertEqual(result['status'], 'incomplete-summary')
                self.assertFalse(result['complete'])
                self.assertTrue(result['notices'])
        (self.root / 'diagnostic.json').unlink()
        self.assertFalse(SUMMARY.summarize(self.root)['complete'])
        (self.root / 'shard.json').unlink()
        self.assertFalse(SUMMARY.summarize(self.root)['complete'])

    def test_changed_counts_or_selection_are_not_displayed_as_complete(self):
        self.diagnostic['counts']['passed'] = 2
        self.write()
        self.assertFalse(SUMMARY.summarize(self.root)['complete'])
        self.diagnostic['counts']['passed'] = 1
        self.diagnostic['outcomes'].reverse()
        self.write()
        self.assertFalse(SUMMARY.summarize(self.root)['complete'])

    def test_workflow_commands_and_html_remain_data(self):
        message = 'bad\n::error::forged\n<script>alert(1)</script>|detail'
        self.diagnostic['outcomes'][0]['error']['message'] = message
        self.write()
        result = subprocess.run(['python3', str(SCRIPT), '--input', str(self.root)], capture_output=True, text=True)
        self.assertEqual(len(result.stdout.splitlines()), 1)
        self.assertEqual(json.loads(result.stdout)['cases'][0]['error'], message)
        rendered = SUMMARY.markdown(SUMMARY.summarize(self.root))
        self.assertNotIn('<script>', rendered)
        self.assertIn('&#124;detail', rendered)

    def test_ordinary_and_preflight_results_are_display_only(self):
        (self.root / 'diagnostic.json').unlink()
        self.record.update(status='passed', mutations=[{'name': 'first'}, {'name': 'second'}])
        self.record['execution']['keepGoing'] = False
        (self.root / 'shard.json').write_text(json.dumps(self.record))
        result = SUMMARY.summarize(self.root)
        self.assertEqual(result['mode'], 'ordinary')
        self.assertFalse(result['releaseAcceptance'])
        self.assertTrue(all(row['status'] == 'reported-passed' for row in result['cases']))
        (self.root / 'shard.json').rename(self.root / 'preflight.json')
        result = SUMMARY.summarize(self.root)
        self.assertEqual(result['mode'], 'preflight')
        self.assertEqual(result['baseline']['verified'], 40)
        self.assertFalse(result['releaseAcceptance'])


if __name__ == '__main__':
    unittest.main()
