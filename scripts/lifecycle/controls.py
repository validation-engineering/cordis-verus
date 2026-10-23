"""Run the same canonical implementation mutations through behavior and Verus.

Neither a compile error nor an arbitrary crashing test counts as detection.
The existing strict verifier harness remains authoritative for proof rejection.
"""
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

from . import evidence as E
from .oracle import check_native
from .reducer import reduce_native
from .scenarios import generate_native

TESTS = {
    'cleanup-dispatch-promotes-failure': ('cleanup_protocol', 'repeated_failed_prefixes_pin_the_provider_while_another_consumer_finishes',
        '    assert_eq!(\n        run.replies.iter().map(Result::is_ok).collect::<Vec<_>>(),\n        [false, false, true, true, false]'),
    'cleanup-dispatch-bypasses-receipt': ('cleanup_protocol', 'repeated_failed_prefixes_pin_the_provider_while_another_consumer_finishes',
        '    assert_eq!(\n        run.replies.iter().map(Result::is_ok).collect::<Vec<_>>(),\n        [false, false, true, true, false]'),
    'cleanup-queue-discards-retained-payload': ('cleanup_queue', 'retained_payload_returns_from_the_same_slot_before_late_and_earlier_work',
        '    assert_eq!(drops.load(Ordering::SeqCst), 0);\n    assert!(queue.pop().unwrap().is_none());'),
    'r2-value-ignores-inverse-depth': ('reversible_value', 'same_value_interference_retains_the_exact_inverse',
        '    let first = first.inverse.restore().err().unwrap();'),
    'r2-shared-child-splits-request-inverse': ('shared_child', 'checked_pair_keeps_fifo_requests_lifo_inverses_and_actual_payloads_distinct',
        '    assert_eq!(first.snapshot().identity().unwrap().id(), id);'),
}


def build_test(root, target, test, directory, offline):
    command = ['cargo','test','--locked','-p','cordis-kernel','--test',test,'--no-run',
               '--message-format=json','--target-dir',str(target)]
    if offline: command.append('--offline')
    run, output = E.invoke(command,directory,'test-build',cwd=root,timeout=600,env=E.environment(offline))
    E.checked(run)
    artifacts = [json.loads(line) for line in output.splitlines() if line.startswith('{')]
    binaries = [Path(a['executable']) for a in artifacts if a.get('reason')=='compiler-artifact'
                and a.get('target',{}).get('name')==test and a.get('executable')]
    if len(binaries)!=1: raise RuntimeError('Expected exactly one real test executable')
    binary=binaries[0]
    run.update(artifact=str(binary),artifactSha256=E.digest(binary))
    return binary,run


def test_behavior(binary, spec, root, directory):
    test,name,anchor=spec
    source=(root/f'crates/cordis-kernel/tests/{test}.rs').read_text()
    if source.count(anchor)!=1: raise RuntimeError('Behavioral rejection anchor is no longer unique')
    line=source[:source.index(anchor)].count('\n')+1
    run,stdout=E.invoke([str(binary),'--exact',name,'--nocapture'],directory,'test-run',timeout=60)
    stderr=(directory/run['stderr']).read_text()
    run['artifactSha256']=E.digest(binary)
    status=classify_test(run,stdout,stderr,test,name,line)
    return {'status':status,'test':name,'expectedPanicAnchor':anchor,'expectedLine':line,'run':run}


def classify_test(run,stdout,stderr,test,name,line):
    if (run['timedOut'] or run['interrupted'] or run.get('launchError')
            or 'running 1 test' not in stdout):
        status='inconclusive'
    elif run['returncode']==0 and f'test {name} ... ok' in stdout and '1 passed; 0 failed' in stdout:
        status='not_detected'
    elif (run['returncode']==101 and f'test {name} ... FAILED' in stdout
          and '0 passed; 1 failed' in stdout
          and re.search(rf"thread '{re.escape(name)}' .*panicked at [^\n]*tests/{test}\.rs:{line}:\d+:",stderr)):
        status='detected'
    else:
        status='inconclusive'
    return status


def behavior_cases(binary,cases,directory):
    run,results=E.execute_native(binary,cases,directory)
    checks=[check_native(case,result) for case,result in zip(cases,results)] if results else []
    failed=[{'id':case['id'],'check':check} for case,check in zip(cases,checks) if check['status']=='failed']
    status='detected' if failed else ('not_detected' if len(checks)==len(cases) and all(c['status']=='passed' for c in checks) else 'inconclusive')
    return {'status':status,'run':run,'checks':checks,'failures':failed}


def run_controls(args):
    output=E.ROOT/'target/lifecycle-campaign/controls'
    before=E.inputs()
    report=E.new_report('provider-consumer-one-child/v1',before)
    E.write_json(output/'report.json',report)
    try:
        _,manifest_path,manifest,_,helper=E.module('check-profile-controls.py').load_profile('update-recovery')
        report['manifestSha256']=E.digest(manifest_path)
        cases=generate_native(args.seed,args.cases)
        E.write_json(output/'scenarios.json',{'cases':cases})
        report['scenarioSha256']=E.digest(output/'scenarios.json')
        baseline,build=E.build_native(output/'positive',offline=args.offline)
        report['positiveBuild']=build
        report['positiveScenarios']=behavior_cases(baseline,cases,output/'positive')
        if report['positiveScenarios']['status']!='not_detected': raise RuntimeError('Fresh positive scenario baseline failed')
        report['positiveTests']={}
        for name,spec in TESTS.items():
            directory=output/'positive'/name
            binary,build=build_test(E.ROOT,E.ROOT/'target',spec[0],directory,args.offline)
            result=test_behavior(binary,spec,E.ROOT,directory)
            report['positiveTests'][name]={'build':build,**result}
            if result['status']!='not_detected': raise RuntimeError('Fresh positive behavior test failed: '+name)
        # Keep each complete mutated workspace and binary for independent replay.
        workspace=Path(tempfile.mkdtemp(prefix='sources-',dir=output))
        report['workspace']=str(workspace)
        for case in manifest['cases']:
            name=case['name']; print('Behavioral control: '+name,flush=True)
            directory=workspace/name; root=directory/'source'; root.mkdir(parents=True)
            for filename in ('Cargo.toml','Cargo.lock','rust-toolchain.toml','toolchain.lock.json'):
                if (E.ROOT/filename).exists(): shutil.copyfile(E.ROOT/filename,root/filename)
            shutil.copytree(E.ROOT/'crates',root/'crates',ignore=shutil.ignore_patterns('target','__pycache__'))
            if (E.ROOT/'.cargo').is_dir(): shutil.copytree(E.ROOT/'.cargo',root/'.cargo')
            mutation=case['mutation']; source=root/'crates/cordis-kernel/src'/mutation['file']
            text=source.read_text()
            if text.count(mutation['old'])!=1: raise RuntimeError('Mutation anchor changed')
            source.write_text(text.replace(mutation['old'],mutation['new'],1))
            row={'name':name,'mutation':mutation,'mutantKernelSha256':helper.source_hashes(root/'crates/cordis-kernel/src')}
            report['cases'].append(row)
            binary,build=E.build_native(directory,root=root,target=output/'behavior-build',offline=args.offline)
            saved=directory/'lifecycle_scenario'
            shutil.copy2(binary,saved); binary=saved
            build['artifact']=str(binary)
            row['build']=build
            row['generated']=behavior_cases(binary,cases,directory/'generated')
            test,build=build_test(root,output/'behavior-build',TESTS[name][0],directory,args.offline)
            saved=directory/'behavior-test'
            shutil.copy2(test,saved); test=saved
            build['artifact']=str(test)
            row['targeted']={'build':build,**test_behavior(test,TESTS[name],root,directory)}
            if row['targeted']['status']!='detected': raise RuntimeError('Designated behavioral control not detected: '+name)
            if name in {'cleanup-dispatch-promotes-failure','cleanup-dispatch-bypasses-receipt'}:
                # NativeRuntime uses the shared primitives directly, whereas
                # the host dispatcher has its own actual caller test above.
                row['generated']['scopeNote']='Native managed scenarios do not call execute_cleanup; the designated real dispatcher test supplies this coverage.'
            if name=='r2-value-ignores-inverse-depth':
                selected=next(c for c in cases if any(f['id']==c['id'] for f in row['generated']['failures']))
                row['reduction']=reduce_native(selected,baseline,binary,directory/'reduction')
                if row['reduction']['reducedCommands']>=row['reduction']['originalCommands']:
                    raise RuntimeError('Known counterexample was not reduced')
            E.write_json(output/'report.json',report)
        if E.inputs()!=before: raise RuntimeError('Source changed during behavioral controls')
        if args.behavior_only:
            report.update(status='behavior_only_passed',proof='not_run')
            E.write_json(output/'report.json',report)
            print('Behavioral pilot passed; strict proof checks not run',flush=True)
            return
        print('Running the canonical strict proof controls',flush=True)
        run,_=E.invoke([sys.executable,'-B','scripts/check-profile-controls.py','update-recovery'],
                       output,'strict-proof-controls',timeout=10800,env=E.environment(args.offline))
        E.checked(run)
        proof_path=E.ROOT/'target/update-recovery-controls/report.json'
        proof=json.loads(proof_path.read_text())
        if proof['status']!='passed' or proof['kernelSha256']!=helper.source_hashes(E.ROOT/'crates/cordis-kernel/src'):
            raise RuntimeError('Proof report is stale or incomplete')
        if [r['name'] for r in proof['cases']]!=[r['name'] for r in report['cases']]:
            raise RuntimeError('Behavior/proof selections differ')
        for row,verified in zip(report['cases'],proof['cases']):
            if row['mutantKernelSha256']!=verified['mutantSha256'] or verified['status']!='passed':
                raise RuntimeError('Behavior/proof did not use the exact same mutation')
            row['proof']='rejected_designated_contract'
        report['proof']={'run':run,'path':str(proof_path),'sha256':E.digest(proof_path)}
        if E.inputs()!=before: raise RuntimeError('Source changed during paired controls')
        report['status']='passed'
        E.write_json(output/'report.json',report)
        print('Paired lifecycle controls passed: '+str(output/'report.json'),flush=True)
    except BaseException as error:
        report.update(status='failed',failure=f'{type(error).__name__}: {error}')
        E.write_json(output/'report.json',report)
        raise
