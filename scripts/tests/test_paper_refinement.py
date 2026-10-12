import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('paper_refinement', ROOT / 'scripts/check-paper-refinement.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class PaperRefinementTests(unittest.TestCase):
    def setUp(self):
        self.plan = json.loads((ROOT / checker.PLAN).read_text())
        self.ledger = json.loads((ROOT / checker.LEDGER).read_text())

    def test_inventory_does_not_promote_original_claims(self):
        original = copy.deepcopy(self.ledger)
        checker.validate(self.plan, self.ledger)
        rendered = checker.render(self.plan, self.ledger)
        self.assertEqual(self.ledger, original)
        self.assertIn('Lemma 62: Vestigial entries | refuted', rendered)
        self.assertIn('whole-lifecycle | open', rendered)
        self.assertIn('not a proof of calling relationships', rendered)

    def test_missing_or_duplicated_item_cannot_hide_in_group_counts(self):
        self.plan['workPackages'][0]['paperItems'][-1] = 19
        with self.assertRaisesRegex(ValueError, 'exactly one primary'):
            checker.validate(self.plan, self.ledger)

    def test_missing_integration_obligation_is_rejected(self):
        self.plan['integration'].pop()
        with self.assertRaisesRegex(ValueError, 'four integration'):
            checker.validate(self.plan, self.ledger)

    def test_cyclic_dependency_is_rejected(self):
        self.plan['milestones'][0]['dependsOn'] = ['R5']
        with self.assertRaisesRegex(ValueError, 'Cyclic'):
            checker.validate(self.plan, self.ledger)

    def test_specification_cannot_be_labelled_executable_code(self):
        entry = self.plan['workPackages'][0]['reviewPath'][0]
        entry['role'] = 'execution'
        with self.assertRaisesRegex(ValueError, 'Missing execution symbol'):
            checker.validate(self.plan, self.ledger)

    def test_reference_cannot_escape_repository(self):
        self.plan['workPackages'][0]['reviewPath'][0]['file'] = '../outside.rs'
        with self.assertRaisesRegex(ValueError, 'Invalid review source'):
            checker.validate(self.plan, self.ledger)

    def test_paper_version_must_match_immutable_ledger(self):
        self.plan['paper']['arxiv'] = '2608.25512v2'
        with self.assertRaisesRegex(ValueError, 'bound to the paper ledger'):
            checker.validate(self.plan, self.ledger)

    def test_r1_cannot_complete_by_silently_claiming_original_equivalence(self):
        self.plan['milestones'][1]['status'] = 'complete'
        self.plan['r1Interpretation']['originalPaperEquivalent'] = True
        with self.assertRaisesRegex(ValueError, 'explicit strict interpretation'):
            checker.validate(self.plan, self.ledger)

    def test_r1_cannot_omit_the_parent_contract_or_executable_caller(self):
        self.plan['milestones'][1]['status'] = 'complete'
        for revision in self.plan['r1Interpretation']['revisions']:
            if revision['id'] == 'R1-DOMAIN':
                revision['reviewPath'] = [e for e in revision['reviewPath'] if e['symbol'] != 'root_component']
        with self.assertRaisesRegex(ValueError, 'Missing R1 semantic or executable'):
            checker.validate(self.plan, self.ledger)

    def test_final_milestone_cannot_hide_open_audit_or_integration(self):
        self.plan['milestones'][-1]['status'] = 'complete'
        with self.assertRaisesRegex(ValueError, 'audit outcomes remain open'):
            checker.validate(self.plan, self.ledger)
        for item in self.ledger['items']:
            if item['status'] in {'partial', 'missing'}:
                item['status'] = 'formalized' if item['kind'] == 'Definition' else 'proved'
        with self.assertRaisesRegex(ValueError, 'integration obligations remain open'):
            checker.validate(self.plan, self.ledger)


if __name__ == '__main__':
    unittest.main()
