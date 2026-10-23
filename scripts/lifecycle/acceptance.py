"""Audit fresh final-source records. This command does not run a new proof."""
from collections import Counter
import json
from pathlib import Path

from . import evidence as E
from .comparison import compare
from .oracle import check_native
from .scenarios import REQUIRED_NATIVE


def require(condition,message):
    if not condition: raise RuntimeError(message)


def command_output(run):
    directory=Path(run['evidenceDirectory'])
    for stream in ('stdout','stderr'):
        require(E.digest(directory/run[stream])==run[stream+'Sha256'],'Changed command output: '+run[stream])
    require(not run['timedOut'] and not run['interrupted'] and not run.get('launchError'),'Inconclusive command')
    if run.get('artifact'):
        require(E.digest(run['artifact'])==run['artifactSha256'],'Changed compiled artifact')
    elif run.get('artifactSha256'):
        require(E.digest(run['command'][0])==run['artifactSha256'],'Changed executed binary')
    return (directory/run['stdout']).read_text()


def load_campaign(name,before):
    directory=E.ROOT/'target/lifecycle-campaign'/name
    report=json.loads((directory/'report.json').read_text())
    require(report['status']=='passed' and report['sourceHashes']==before,'Missing, failed or stale '+name+' campaign')
    require(report['releaseAcceptance'] is False and report['paperCompletion'] is False,'Overbroad campaign claim')
    require(report['scenarioSha256']==E.digest(directory/'scenarios.json'),'Changed saved commands')
    cases=json.loads((directory/'scenarios.json').read_text())['cases']
    require(len(cases)>0 and len({c['id'] for c in cases})==len(cases),'Empty or duplicate case IDs')
    return directory,report,cases


def audit():
    before=E.inputs()
    E.module('record-development.py').check_record()
    development=json.loads((E.ROOT/'docs/development-report.json').read_text())
    log=E.ROOT/development['log']
    require(E.digest(log)==development['logSha256'],'Changed development log')
    E.module('record-development.py').parse_results(log.read_text())
    native_dir,native,cases=load_campaign('native',before)
    require([r['id'] for r in native['cases']]==[c['id'] for c in cases],'Native case accounting differs')
    coverage=set(); traces={}
    command_output(native['build'])
    for row in native['cases']:
        key=row['run']['stdout']
        if key not in traces:
            values=json.loads(command_output(row['run']))['results']
            traces[key]={r['id']:r for r in values}
    for case,row in zip(cases,native['cases']):
        check=check_native(case,traces[row['run']['stdout']][case['id']])
        require(check==row['check'] and check['status']=='passed','Native observation check changed')
        coverage.update(check['coverage'])
    require(REQUIRED_NATIVE<=coverage,'Missing actual native coverage')
    require({c['category'] for c in cases}=={'admitted','interference','invalid-commands'},'Missing admitted or adverse scenarios')

    comparison_dir,comparison,plugin_cases=load_campaign('comparison',before)
    require([r['id'] for r in comparison['cases']]==[c['id'] for c in plugin_cases],'Comparison accounting differs')
    for file,sha in comparison['bundles']['inputs'].items(): require(E.digest(E.ROOT/file)==sha,'Stale comparison input')
    for artifact in comparison['bundles']['artifacts'].values(): require(E.digest(artifact['path'])==artifact['sha256'],'Changed comparison bundle')
    require(comparison['bundles']['nativeBuild']['sourceHashes']==E.module('record-development.py').native_source_hashes(),'Stale comparison native build')
    for case,row in zip(plugin_cases,comparison['cases']):
        observed={backend:json.loads(command_output(run))['results'][0] for backend,run in row['runs'].items()}
        check=compare(case,observed['native'],observed['upstream'])
        require(check==row['comparison'] and check['status'] in {'matched','intentional_difference','unsupported'},'Unexplained comparison')
    counts=Counter(row['comparison']['status'] for row in comparison['cases'])
    require(dict(counts)==comparison['counts'] and all(counts[k]>0 for k in ('matched','intentional_difference','unsupported')),'Missing comparison strata')

    controls_dir,controls,control_cases=load_campaign('controls',before)
    _,_,manifest,_,helper=E.module('check-profile-controls.py').load_profile('update-recovery')
    proof_path=Path(controls['proof']['path'])
    require(E.digest(proof_path)==controls['proof']['sha256'],'Changed strict proof record')
    proof=json.loads(proof_path.read_text()); proof_dir=proof_path.parent/proof['evidenceDirectory']
    require(proof['status']=='passed' and proof['kernelSha256']==helper.source_hashes(E.ROOT/'crates/cordis-kernel/src'),'Stale strict proof baseline')
    require([r['name'] for r in controls['cases']]==[c['name'] for c in manifest['cases']]==[r['name'] for r in proof['cases']],'Control selections differ')
    helper.verify_tool_artifacts(proof['tool'])
    from .controls import TESTS, classify_test
    from .reducer import signature
    # Re-evaluate saved observations; don't rerun test executables or solvers.
    reduction=None
    for row,verified,case in zip(controls['cases'],proof['cases'],manifest['cases']):
        require(row['mutation']==case['mutation'] and row['mutantKernelSha256']==verified['mutantSha256'],'Behavior and proof mutations differ')
        source=proof_dir/case['name']
        require(helper.source_hashes(source)==verified['mutantSha256'],'Changed proof mutant source')
        helper.validate_positive(verified['positive'],proof_dir,entire=False,expected_tool=proof['tool'],
                                 targets=case['targets'],expected_failures=case['expectedFailures'])
        helper.validate_compile(verified['compile'],proof_dir,proof_dir/(case['name']+'-compile.rlib'))
        helper.validate_rejection(verified['negative'],proof_dir,case,source,proof['tool'])
        require(row['targeted']['status']=='detected','Missing designated behavioral failure')
        command_output(row['build']); command_output(row['targeted']['build'])
        saved=command_output(row['targeted']['run'])
        spec=TESTS[row['name']]
        source_text=(E.ROOT/f'crates/cordis-kernel/tests/{spec[0]}.rs').read_text()
        require(source_text.count(spec[2])==1,'Changed behavioral assertion')
        line=source_text[:source_text.index(spec[2])].count('\n')+1
        stderr=(Path(row['targeted']['run']['evidenceDirectory'])/row['targeted']['run']['stderr']).read_text()
        require(classify_test(row['targeted']['run'],saved,stderr,spec[0],spec[1],line)=='detected','Missing designated behavioral failure')
        for scope in (controls['positiveTests'][row['name']],):
            require(scope['status']=='not_detected','Positive behavior baseline failed')
            command_output(scope['build']); command_output(scope['run'])
        results=json.loads(command_output(row['generated']['run']))['results']
        require([check_native(c,r) for c,r in zip(control_cases,results)]==row['generated']['checks'],'Changed mutant behavior evidence')
        if row.get('reduction'):
            reduction=row['reduction']; require(reduction['status']=='passed' and reduction['oneDeletionMinimal'],'Missing reduction evidence')
            require(reduction['reducedCommands']<reduction['originalCommands'],'Counterexample did not shrink')
            require(E.digest(reduction['baseline'])==reduction['baselineSha256'] and E.digest(reduction['mutant'])==reduction['mutantSha256'],'Changed reducer executables')
            reduced_path=Path(reduction['replay'][4])
            require(E.digest(reduced_path)==reduction['reducedSha256'],'Changed reduced commands')
            reduced=json.loads(reduced_path.read_text())['cases'][0]
            for attempt in reduction['attempts']:
                input_path=Path(attempt['positive']['evidenceDirectory'])/attempt['input']
                require(E.digest(input_path)==attempt['inputSha256'],'Changed reduction candidate')
                candidate=json.loads(input_path.read_text())['cases'][0]
                positive=check_native(candidate,json.loads(command_output(attempt['positive']))['results'][0])
                require(positive==attempt['positiveCheck'],'Changed reduction positive result')
                preserved=False
                if 'negative' in attempt:
                    negative=check_native(candidate,json.loads(command_output(attempt['negative']))['results'][0])
                    require(negative==attempt['negativeCheck'],'Changed reduction mutant result')
                    preserved=positive['status']=='passed' and signature(candidate,negative)==reduction['predicate']
                require(preserved==attempt['preservesFailure'],'Reduction predicate changed')
            last=reduction['attempts'][-len(reduced['commands']):]
            require(len(last)==len(reduced['commands']),'Missing one-deletion checks')
            for i,attempt in enumerate(last):
                candidate=json.loads((Path(attempt['positive']['evidenceDirectory'])/attempt['input']).read_text())['cases'][0]
                require(candidate['commands']==reduced['commands'][:i]+reduced['commands'][i+1:] and not attempt['preservesFailure'],'Missing final one-deletion minimality')
            for name,entry in reduction['final'].items():
                check=check_native(reduced,json.loads(command_output(entry['run']))['results'][0])
                require(check==entry['check'] and (check['status']=='passed' if name=='positive' else signature(reduced,check)==reduction['predicate']),'Reduced artifact no longer establishes the failure')
    require(reduction is not None,'No real negative control was reduced')
    # The old exact fixture remains an independent gate with no normalization.
    fixed_path=E.ROOT/'target/node-compat/differential.json'
    fixed=json.loads(fixed_path.read_text())
    require(fixed['status']=='passed' and fixed['normalization']=='none','Original exact differential was not preserved')
    for file,sha in fixed['inputs'].items(): require(E.digest(E.ROOT/file)==sha,'Stale exact differential input: '+file)
    require(fixed['observations']['native']==fixed['observations']['upstream'],'Exact fixture differs')
    lock=json.loads((E.ROOT/'upstream.lock.json').read_text())['repositories']['cordis']
    require(comparison['bundles']['upstream']==lock and fixed['profile']['revision']==lock['revision'],'Different upstream revisions')
    output=E.ROOT/'target/lifecycle-campaign/acceptance'
    for args,expected in [(['rev-parse','--abbrev-ref','HEAD'],'main'),
                          (['rev-parse','codex/archive-before-refactor-2026-10-24'],'60bdd89442519b64677f1435eda79030938e6d67'),
                          (['-C',lock['path'],'rev-parse','HEAD'],lock['revision']),
                          (['-C',lock['path'],'status','--porcelain=v1','--untracked-files=all'],'')]:
        run,text=E.invoke(['git',*args],output,'git-'+str(len(args))+'-'+str(len(expected)),timeout=30)
        E.checked(run);require(text.strip()==expected,'Archive, branch or upstream differs')
    require(E.inputs()==before,'Sources changed during acceptance audit')
    reports=[E.ROOT/'docs/development-report.json',native_dir/'report.json',comparison_dir/'report.json',controls_dir/'report.json',fixed_path,proof_path]
    report={'schema':'cordis-verus.lifecycle-acceptance/v1','status':'passed','scope':'provider-consumer-one-child/v1',
            'sourceHashes':before,'reports':{str(p.relative_to(E.ROOT)):E.digest(p) for p in reports},
            'nativeCases':len(cases),'nativeCoverage':sorted(coverage),'comparison':dict(counts),
            'strictControls':len(manifest['cases']),'reducedCommands':reduction['reducedCommands'],
            'releaseAcceptance':False,'paperCompletion':False,'fullNegativeControls':'not_run',
            'proofBoundary':'Executable contracts only; callback effects, FFI and global progress remain host premises',
            'note':'Audit of fresh records, not a new solver run'}
    E.write_json(output/'report.json',report)
    print('Final lifecycle acceptance passed: '+str(output/'report.json'))
    return report
