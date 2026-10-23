"""Pinned Cordis comparison with narrow, reviewed policy differences.

Raw events are never sorted. ID projection is a checked birth-preserving
bijection. Backend-only native diagnostics are checked independently and saved.
"""
import copy
from collections import Counter
import json
import random

from . import evidence as E
from .scenarios import SCHEMA, generate_native


def generate_plugin(seed, count):
    if type(seed) is not int or not 0<=seed<2**32 or type(count) is not int or not 12<=count<=512:
        raise ValueError('Plugin campaign requires a u32 seed and 12..512 cases')
    cases=[]
    for i in range(count):
        rng=random.Random((seed+i)%2**32)
        family=('activation','updates','child-failure','consumer-failure','retry-extension','unsupported-native')[i%6]
        if family=='unsupported-native':
            case=generate_native((seed+i)%2**32,6)[0]
            case['id']=f'plugin-{i:04}-{seed+i}'
            cases.append(case); continue
        order=['consumer','provider'] if (i//6)%2 else ['provider','consumer']
        actions=[{'op':'mount','actor':actor} for actor in order]+[{'op':'settle'}]
        actions.extend({'op':'observe'} for _ in range(rng.randrange(1,4)))
        if family=='updates':
            actions += [{'op':'update','revision':1},{'op':'observe'},{'op':'update','revision':2},{'op':'shutdown'}]
        elif family in {'child-failure','consumer-failure','retry-extension'}:
            actor='consumer' if family=='consumer-failure' else 'child'
            actions += [{'op':'fault','actor':actor},{'op':'update','revision':1}]
            if family=='retry-extension':
                actions += [{'op':'settle_fault'},{'op':'repair'},{'op':'retry','actor':actor},{'op':'update','revision':2},{'op':'shutdown'}]
        cases.append({'schema':SCHEMA,'profile':'plugin-lifecycle/v1','id':f'plugin-{i:04}-{seed+i}',
                      'seed':(seed+i)%2**32,'generator':'plugin-lifecycle/1','category':family,'purpose':'campaign',
                      'families':[family,order[0]+'-first'],
                      'parameters':{'values':[rng.randrange(1,101) for _ in range(3)]},
                      'commands':[{'action':a} for a in actions]})
    return cases


def need(condition, detail):
    if not condition: raise ValueError(detail)


def project(state):
    """Rename actual runtime IDs only after checking the complete association."""
    value=copy.deepcopy(state)
    value.pop('native')
    registrations=value['registrations']
    need([r['birth'] for r in registrations]==list(range(1,len(registrations)+1)),'Non-sequential birth records')
    mapping={r['uid']:r['birth'] for r in registrations}
    need(len(mapping)==len(registrations) and all(type(k) is int for k in mapping),'Reused or missing runtime ID')
    for row in value['fibers']+value['episodes']:
        if row['uid'] is None:
            need('state' in row and row['state']==4,'Only a disposed fiber may lose its public ID')
        else:
            need(mapping.get(row['uid'])==row['birth'],'ID projection changes ownership or Episode identity')
            row['uid']=row['birth']
        owner=registrations[row['birth']-1]
        need(owner['actor']==row['actor'],'Birth has a different owner')
    for row in registrations: row['uid']=row['birth']
    return value


def events_for(episode, *, cleanup=False, fail=False):
    base={k:episode[k] for k in ('birth','actor','episode')}
    if not cleanup:
        return [{**base,'kind':'setup',**{k:episode[k] for k in ('revision','bindings','resource','parent')}}]
    attempt=episode['attempts']+1
    return [{**base,'kind':'cleanup-attempt','attempt':attempt,'reads':episode['bindings']},
            {**base,'kind':'cleanup-failed' if fail else 'cleanup-succeeded','attempt':attempt}]


def transition(before, *, cleanup=(), fail=None, revision=None, shutdown=False):
    """Expected public observations, never supplied to either implementation."""
    state=copy.deepcopy(before)
    emitted=[]
    for actor in cleanup:
        episode=next(e for e in reversed(state['episodes']) if e['actor']==actor and e['live'])
        emitted += events_for(episode,cleanup=True,fail=actor==fail)
        episode['attempts']+=1
        if actor!=fail: episode['live']=False
    if revision is not None:
        # Existing root registrations persist; each real Child is freshly born.
        child_birth=len(state['registrations'])+1
        state['registrations'].append({'birth':child_birth,'actor':'child','uid':child_birth})
        old_fibers={f['actor']:f for f in state['fibers']}
        for actor in ('provider','consumer','child'):
            old=old_fibers.get(actor)
            birth=child_birth if actor=='child' else old['birth']
            binding=[] if actor=='provider' else [next(e['resource'] for e in reversed(state['episodes']) if e['actor']=='provider')]
            parent=None
            if actor=='child':
                consumer=next(e for e in reversed(state['episodes']) if e['actor']=='consumer')
                binding.append(consumer['resource']); parent={'birth':consumer['birth'],'episode':consumer['episode']}
            episode={'birth':birth,'actor':actor,'uid':birth,
                     'episode':sum(e['birth']==birth for e in state['episodes'])+1,
                     'revision':revision,'bindings':binding,'parent':parent,
                     'resource':len(state['episodes'])+1,'live':True,'attempts':0}
            state['episodes'].append(episode);emitted += events_for(episode)
            fiber={'birth':birth,'actor':actor,'uid':birth,'state':2}
            if old: state['fibers'][state['fibers'].index(old)]=fiber
            else: state['fibers'].append(fiber)
        state['publications']={key:{'resource':next(e['resource'] for e in reversed(state['episodes']) if e['actor']==actor),'revision':revision}
                               for key,actor in [('value','provider'),('marker','consumer')]}
    elif shutdown or fail:
        state['publications']={'value':None,'marker':None}
        for fiber in state['fibers']:
            latest=next(e for e in reversed(state['episodes']) if e['birth']==fiber['birth'])
            disposed=shutdown or (fiber['actor']=='child' and not latest['live'])
            fiber['state']=4 if disposed else 5
            if disposed: fiber['uid']=None
    return state,emitted


def native_frame(raw):
    need(raw is not None and not raw['checkErrors'],'Native diagnostics missing or invalid')
    plugins={p['id']:p for p in raw['plugins']}
    for plugin in plugins.values():
        for binding in plugin['committed']:
            provider=plugins.get(binding['provider'])
            need(provider is not None and provider['state']!='Inactive'
                 and provider['generation']==binding['generation']
                 and (provider['pendingAction'] or {}).get('kind')!='cleanup',
                 'Native committed provider was released, replaced or admitted to cleanup')


def check_plugin(case,result,backend):
    if case['profile']!='plugin-lifecycle/v1':
        need(result.get('status')=='unsupported' and not result.get('steps'),'Unsupported profile was executed')
        return {'status':'unsupported','steps':[]}
    need(result.get('id')==case['id'],'Wrong input association')
    initial=project(result['initial'])
    need(initial=={'registrations':[],'fibers':[],'episodes':[],'publications':{'value':None,'marker':None}},'Unexpected initial state')
    before=initial; fault=None; sequence=0; projected=[]; unsupported=False
    for index,row in enumerate(result['steps']):
        action=case['commands'][index]['action']; op=action['op']
        need(row['index']==index and row['action']==action,'Wrong executed command')
        state=project(row['state']);expected_status='ok';events=[]
        if backend=='native': native_frame(row['state']['native'])
        if op=='mount':
            expected=copy.deepcopy(before)
            birth=len(expected['registrations'])+1
            actor=action['actor']
            expected['registrations'].append({'birth':birth,'actor':actor,'uid':birth})
            expected['fibers'].append({'birth':birth,'actor':actor,'uid':birth,'state':1 if actor=='provider' else 0})
        elif op=='settle':
            expected,events=transition(before,revision=0)
        elif op=='settle_fault':
            # The explicit domain observation consumes the queued diagnostic
            # from the failed update. It cannot be silently treated as success.
            expected=before
            if backend=='native': expected_status='rejected'
        elif op in {'observe','fault','repair'}:
            expected=before
            if op=='fault': fault=action['actor']
            if op=='repair': fault=None
        elif op in {'update','shutdown','retry'}:
            if op=='retry' and backend=='upstream':
                expected=before; expected_status='unsupported';unsupported=True
            else:
                order=['child','consumer','provider'] if backend=='native' else (
                    ['consumer','child','provider'] if op=='shutdown' else ['provider','consumer','child'])
                if op=='retry':
                    order=[actor for actor in order if next(e for e in reversed(before['episodes']) if e['actor']==actor)['live']]
                failed=fault if op=='update' else None
                if failed and backend=='native':
                    order=order[:order.index(failed)+1]; expected_status='rejected'
                revision=None if op=='shutdown' or expected_status=='rejected' else (1 if op=='retry' else action['revision'])
                expected,events=transition(before,cleanup=order,fail=failed,revision=revision,shutdown=op=='shutdown')
        else: raise ValueError('Unknown generated command')
        need(row['outcome']['status']==expected_status,f'{backend} unexpected outcome at {index}: {row["outcome"]}')
        if expected_status=='rejected':
            messages=[]
            def walk(error):
                messages.append(error['message'])
                for child in error.get('errors',[]): walk(child)
                if error.get('cause'): walk(error['cause'])
            walk(row['outcome']['error'])
            old=next(e for e in reversed(before['episodes']) if e['actor']==fault)
            need(f'campaign-cleanup:{fault}:{old["revision"]}' in messages,'Rejected for an unrelated error')
        need(state==expected,f'{backend} unexpected public state at {index}: {op}')
        full_events=[{'sequence':sequence+j,**event} for j,event in enumerate(events)]
        need(row['events']==full_events,f'{backend} unexpected callback order or ownership at {index}: {row["events"]}')
        sequence+=len(events)
        projected.append({'index':index,'action':action,'status':expected_status,'state':state,'events':full_events})
        before=state
    need(result['events']==[event for row in projected for event in row['events']],'Event history differs from command observations')
    if unsupported:
        need(result['status']=='unsupported' and projected[-1]['status']=='unsupported','Unsupported result was hidden')
    else:
        need(result['status']=='executed' and len(projected)==len(case['commands']),'Incomplete execution')
    return {'status':'unsupported' if unsupported else 'executed','steps':projected}


def compare(case,native,upstream):
    try:
        left=check_plugin(case,native,'native'); right=check_plugin(case,upstream,'upstream')
        if left['status']=='unsupported' or right['status']=='unsupported':
            return {'status':'unsupported','nativeStatus':left['status'],'upstreamStatus':right['status'],
                    'reason':'No matching public API for the profile or retryCleanup extension',
                    'completedNativeCommands':len(left['steps']),'completedUpstreamCommands':len(right['steps'])}
        if left==right: return {'status':'matched','projection':'checked-registration-bijection/v1'}
        differences=[]
        for l,r in zip(left['steps'],right['steps']):
            if l==r: continue
            # Both complete traces have already met the exact backend policy
            # above. Only these operations may carry a reviewed difference.
            need(l['action']['op'] in {'update','shutdown','settle_fault','repair'},'Difference outside reviewed cleanup policy')
            differences.append({'index':l['index'],'policy':'cleanup-failure-retention/v1' if l['status']=='rejected' or l['action']['op']=='repair' else 'dependency-cleanup-order/v1'})
        need(bool(differences),'Missing explained difference')
        return {'status':'intentional_difference','differences':differences,
                'projection':'checked-registration-bijection/v1','review':'docs/cases/generated-lifecycle.md'}
    except (ValueError,KeyError,TypeError,IndexError,StopIteration) as error:
        return {'status':'unexplained','reason':str(error)}


def run_comparison(args):
    output=E.ROOT/'target/lifecycle-campaign/comparison'
    before=E.inputs();report=E.new_report('plugin-lifecycle/v1',before)
    E.write_json(output/'report.json',report)
    try:
        if args.build:
            build,_=E.invoke(['node','scripts/build-node.mjs',*(['--offline'] if args.offline else [])],output,'native-build',timeout=900,env=E.environment(args.offline))
            E.checked(build); report['build']=build
        run,_=E.invoke(['node','scripts/bundle-lifecycle.mjs'],output,'bundles',timeout=120)
        E.checked(run)
        bundles_path=E.ROOT/'target/lifecycle-campaign/node/bundles.json'
        bundles=json.loads(bundles_path.read_text());report['bundles']=bundles
        report['bundlesSha256']=E.digest(bundles_path)
        cases=generate_plugin(args.seed,args.cases)
        E.write_json(output/'scenarios.json',{'cases':cases})
        report.update(seed=args.seed,generator='plugin-lifecycle/1',scenarioSha256=E.digest(output/'scenarios.json'))
        for i,case in enumerate(cases):
            observed={}; runs={}
            for backend in ('native','upstream'):
                artifact=bundles['artifacts'][backend]
                need(E.digest(artifact['path'])==artifact['sha256'],'Bundle changed')
                run,text=E.invoke(['node',artifact['path'],backend],output,f'case-{i:04}-{backend}',timeout=20,
                                  input_text=json.dumps({'cases':[case]})+'\n')
                runs[backend]=run
                if run['returncode']==0 and not run['timedOut']:
                    try:
                        parsed=json.loads(text)
                        need(parsed['schema']=='cordis-verus.lifecycle-execution/v1' and parsed['backend']==backend and len(parsed['results'])==1,'Malformed response')
                        observed[backend]=parsed['results'][0]
                    except (ValueError,KeyError,TypeError): pass
            result=compare(case,observed['native'],observed['upstream']) if len(observed)==2 else {'status':'inconclusive','reason':'Executor crashed, timed out, or returned invalid output'}
            report['cases'].append({'id':case['id'],'category':case['category'],'runs':runs,'comparison':result})
            E.write_json(output/'report.json',report)
            print(f'Plugin comparison {i+1}/{len(cases)}: {result["status"]}',flush=True)
        counts=Counter(row['comparison']['status'] for row in report['cases'])
        report.update(attempted=len(cases),counts=dict(counts),supported=counts['matched']+counts['intentional_difference'],
                      completedPairs=sum(all(run['returncode']==0 and not run['timedOut'] for run in row['runs'].values()) for row in report['cases']))
        need(not counts['unexplained'] and not counts['inconclusive'],'Unexplained or inconclusive comparisons block acceptance')
        need(all(counts[name]>0 for name in ('matched','intentional_difference','unsupported')),'Missing nonempty comparison strata')
        need(E.inputs()==before,'Sources changed during comparison')
        for file,sha in bundles['inputs'].items(): need(E.digest(E.ROOT/file)==sha,'Bundle input changed')
        report['status']='passed'
        E.write_json(output/'report.json',report)
        print('Lifecycle comparison passed: '+str(output/'report.json'),flush=True)
    except BaseException as error:
        report.update(status='failed',failure=f'{type(error).__name__}: {error}')
        E.write_json(output/'report.json',report)
        raise
