"""Guard evidence interpretation, invalid inputs and reduction validity."""
import copy
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'scripts'))
from lifecycle import evidence as E
from lifecycle.comparison import compare, generate_plugin, project
from lifecycle.controls import classify_test
from lifecycle.oracle import check_native
from lifecycle.reducer import minimize, signature
from lifecycle.scenarios import baseline, generate_native


class GeneratedInputs(unittest.TestCase):
    def test_seed_and_complete_input_are_reproducible(self):
        self.assertEqual(generate_native(17,12),generate_native(17,12))
        self.assertNotEqual(generate_native(17,12),generate_native(18,12))
        self.assertEqual(baseline(),json.loads((ROOT/'crates/cordis/examples/support/lifecycle_scenarios/baseline.json').read_text()))

    def test_smallest_campaign_keeps_nonempty_success_and_adverse_strata(self):
        cases=generate_native(0,6)
        self.assertEqual({c['category'] for c in cases},{'admitted','interference','invalid-commands'})
        for case in cases:
            successful=[c['action']['op'] for c in case['commands'] if c['expect']['status']=='ok']
            self.assertGreaterEqual(successful.count('spawn'),2)
            self.assertGreaterEqual(successful.count('start'),4)
            self.assertEqual(case['commands'][-1]['action'],{'op':'remove','actor':'provider'})
        self.assertTrue(any(s['action'].get('amount')==0 for c in cases for s in c['commands'] if s['action']['op']=='write'))

    def test_bad_budgets_and_boolean_seeds_are_not_silent_empty_success(self):
        for seed,count in [(True,6),(-1,6),(2**32,6),(0,0),(0,5),(0,4097)]:
            with self.assertRaises(ValueError):generate_native(seed,count)
        with self.assertRaises(ValueError):generate_plugin(0,11)

    def test_comparison_keeps_unsupported_commands_in_full_input(self):
        cases=generate_plugin(0,12)
        self.assertEqual(sum(c['profile']=='native-managed/v1' for c in cases),2)
        retries=[c for c in cases if c['category']=='retry-extension']
        self.assertEqual(len(retries),2)
        for case in retries:
            names=[s['action']['op'] for s in case['commands']]
            self.assertLess(names.index('settle_fault'),names.index('repair'))
            self.assertLess(names.index('repair'),names.index('retry'))
            self.assertEqual(names[-1],'shutdown')


class ObservationGuards(unittest.TestCase):
    def fixture(self):
        case=generate_native(0,6)[0]
        case['purpose']='counterexample'
        case['commands']=[{'action':{'op':'observe'},'expect':{'status':'ok','values':[{'value':v,'depth':0} for v in case['parameters']['values']]}}]
        state={'plugins':[],'values':case['commands'][0]['expect']['values'],'rawInverses':[],
               'publications':{'value':False,'marker':False,'retainedValues':0}}
        result={'id':case['id'],'status':'executed','initial':copy.deepcopy(state),
                'steps':[{'index':0,'action':{'op':'observe'},'outcome':{'status':'ok','data':None},'state':copy.deepcopy(state)}]}
        return case,result

    def test_missing_depth_check_cannot_turn_same_value_into_success(self):
        case,result=self.fixture()
        self.assertEqual(check_native(case,result)['status'],'passed')
        result['steps'][0]['state']['values'][0]['depth']=1
        check=check_native(case,result)
        self.assertEqual(check['failure']['code'],'strict-resource-state')

    def test_crash_without_a_witness_is_inconclusive(self):
        case,result=self.fixture();result.update(status='panicked',steps=[],at=0)
        self.assertEqual(check_native(case,result)['status'],'inconclusive')

    def test_empty_prefix_is_not_a_complete_campaign(self):
        case,result=self.fixture();case['purpose']='campaign'
        self.assertEqual(check_native(case,result)['failure']['code'],'nonempty-supported-success')

    def test_comparison_cannot_hide_an_unexpected_execution_as_unsupported(self):
        case=generate_native(0,6)[0]
        result=compare(case,{'id':case['id'],'status':'executed'}, {'id':case['id'],'status':'unsupported'})
        self.assertEqual(result['status'],'unexplained')

    def test_id_projection_is_a_bijection_not_actor_name_collapse(self):
        state={'native':None,'registrations':[{'birth':1,'uid':80,'actor':'provider'}],
               'fibers':[{'birth':1,'uid':80,'actor':'provider','state':2}], 'episodes':[], 'publications':{}}
        self.assertEqual(project(state)['fibers'][0]['uid'],1)
        self.assertEqual(state['fibers'][0]['uid'],80)
        state['registrations'].append({'birth':2,'uid':80,'actor':'child'})
        with self.assertRaises(ValueError):project(state)

    def test_projection_rejects_crosswired_episode(self):
        state={'native':None,'registrations':[{'birth':1,'uid':80,'actor':'provider'},{'birth':2,'uid':90,'actor':'consumer'}],
               'fibers':[],'episodes':[{'birth':2,'uid':80,'actor':'consumer'}],'publications':{}}
        with self.assertRaises(ValueError):project(state)


class ReductionGuards(unittest.TestCase):
    def test_reduction_preserves_semantic_prerequisites_and_checks_each_deletion(self):
        case={'purpose':'campaign','commands':[{'op':s} for s in ['noise','register','noise','write','fault','noise','restore','noise']]}
        required=['register','write','fault','restore'];attempts=[]
        def predicate(c):
            names=[s['op'] for s in c['commands']];attempts.append(names)
            return [name for name in names if name!='noise']==required
        reduced=minimize(case,predicate)
        self.assertEqual([s['op'] for s in reduced['commands']],required)
        self.assertEqual(reduced['purpose'],'counterexample')
        self.assertEqual(case['purpose'],'campaign')
        for i in range(len(required)):self.assertIn(required[:i]+required[i+1:],attempts)

    def test_no_failure_cannot_be_reduced(self):
        with self.assertRaises(ValueError):minimize({'commands':[]},lambda _:False)

    def test_failure_signature_preserves_actor_and_operation(self):
        case={'commands':[{'action':{'op':'restore','actor':'child'}}]}
        check={'status':'failed','failure':{'code':'strict-resource-state','index':0}}
        self.assertEqual(signature(case,check),{'guarantee':'strict-resource-state','operation':'restore','actor':'child'})
        self.assertIsNone(signature(case,{'status':'inconclusive'}))


class EvidenceGuards(unittest.TestCase):
    def test_only_the_designated_assertion_counts_as_detection(self):
        run={'returncode':101,'timedOut':False,'interrupted':False}
        stdout='running 1 test\ntest safety ... FAILED\ntest result: FAILED. 0 passed; 1 failed;'
        stderr="thread 'safety' (123) panicked at crates/cordis-kernel/tests/cleanup.rs:42:5:\nassertion failed"
        self.assertEqual(classify_test(run,stdout,stderr,'cleanup','safety',42),'detected')
        self.assertEqual(classify_test(run,stdout,stderr,'cleanup','safety',41),'inconclusive')
        self.assertEqual(classify_test(run,'running 0 tests',stderr,'cleanup','safety',42),'inconclusive')
        self.assertEqual(classify_test({**run,'timedOut':True},stdout,stderr,'cleanup','safety',42),'inconclusive')

    def test_failed_command_is_not_valid_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            run,text=E.invoke([sys.executable,'-c','print("diagnostic");raise SystemExit(9)'],directory,'failed')
            self.assertEqual(text.strip(),'diagnostic')
            self.assertEqual(run['stdoutSha256'],E.digest(Path(directory)/run['stdout']))
            self.assertEqual(run['evidenceDirectory'],str(Path(directory).resolve()))
            with self.assertRaises(RuntimeError):E.checked(run)

    def test_timeout_is_inconclusive_and_reaped(self):
        with tempfile.TemporaryDirectory() as directory:
            run,_=E.invoke([sys.executable,'-c','import time; time.sleep(60)'],directory,'timeout',timeout=0.1)
            self.assertTrue(run['timedOut'])
            self.assertIsNotNone(run['returncode'])
            with self.assertRaises(RuntimeError):E.checked(run)

    def test_custom_compiler_override_is_rejected(self):
        with patch.dict(os.environ,{'RUSTC_WRAPPER':'unreviewed-wrapper'}):
            with self.assertRaises(RuntimeError):E.environment()


if __name__=='__main__':unittest.main()
