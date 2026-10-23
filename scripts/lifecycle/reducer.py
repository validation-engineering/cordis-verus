"""Deletion minimization with a real baseline and a stable failure predicate.

Candidates must still pass on the unmodified executable. An adapter error,
timeout, or unrelated panic cannot substitute for the original property failure.
"""
import copy
import math

from . import evidence as E
from .oracle import check_native


def signature(case, check):
    if check.get('status') != 'failed':
        return None
    failure = check['failure']
    index = failure['index']
    if not 0 <= index < len(case['commands']):
        return None
    action = case['commands'][index]['action']
    value={'guarantee':failure['code'], 'operation':action['op'], 'actor':action.get('actor')}
    if failure['code'].startswith('api-outcome:'):
        detail=failure['detail']
        value.update(expectedStatus=detail['expected'],observedStatus=detail['actual']['status'],
                     payloadKind=detail['actual'].get('kind'))
    return value


def minimize(case, predicate):
    """ddmin, followed by an exhaustive one-command deletion check.

    The callback owns semantic validity; this algorithm only deletes commands.
    Returns 1-minimality for this exact failure predicate, not a global minimum.
    """
    current = copy.deepcopy(case)
    current['purpose'] = 'counterexample'
    if not predicate(current):
        raise ValueError('Original scenario does not satisfy the reduction predicate')
    granularity = 2
    while len(current['commands']) >= 2:
        width = math.ceil(len(current['commands']) / granularity)
        changed = False
        for start in range(0, len(current['commands']), width):
            candidate = copy.deepcopy(current)
            del candidate['commands'][start:start + width]
            if predicate(candidate):
                current, changed = candidate, True
                granularity = max(2, granularity - 1)
                break
        if changed: continue
        if granularity >= len(current['commands']): break
        granularity = min(len(current['commands']), granularity * 2)
    # A successful deletion changes later dependencies. Restart until a full
    # pass rejects every single deletion on the final candidate.
    index = 0
    while index < len(current['commands']):
        candidate = copy.deepcopy(current)
        del candidate['commands'][index]
        if predicate(candidate):
            current, index = candidate, 0
        else:
            index += 1
    return current


def reduce_native(case, baseline, mutant, directory):
    directory.mkdir(parents=True, exist_ok=True)
    E.write_json(directory / 'original.json', {'cases':[case]})
    original_run, results = E.execute_native(mutant, [case], directory, 'original-mutant')
    if results is None: raise RuntimeError('Cannot reduce inconclusive execution')
    wanted = signature(case, check_native(case, results[0]))
    if wanted is None: raise RuntimeError('No concrete behavioral violation to reduce')
    attempts = []

    def predicate(candidate):
        label = f'candidate-{len(attempts):04}'
        # Save every candidate; a seed cannot reconstruct deletion choices.
        E.write_json(directory / (label + '.json'), {'cases':[candidate]})
        positive, values = E.execute_native(baseline, [candidate], directory, label + '-positive')
        positive_check = check_native(candidate, values[0]) if values else {'status':'inconclusive'}
        row = {'input':label+'.json','inputSha256':E.digest(directory/(label+'.json')),
               'commands':len(candidate['commands']),'positive':positive,'positiveCheck':positive_check,
               'preservesFailure':False}
        if positive_check['status'] == 'passed':
            negative, values = E.execute_native(mutant, [candidate], directory, label + '-mutant')
            negative_check = check_native(candidate, values[0]) if values else {'status':'inconclusive'}
            row.update(negative=negative, negativeCheck=negative_check,
                       preservesFailure=signature(candidate, negative_check) == wanted)
        attempts.append(row)
        return row['preservesFailure']

    reduced = minimize(case, predicate)
    # Keep final traces next to the minimized complete input, independently of
    # the search logs. These are also what the replay command consumes.
    E.write_json(directory / 'reduced.json', {'cases':[reduced]})
    final = {}
    for name, binary in [('positive',baseline),('mutant',mutant)]:
        run, values = E.execute_native(binary, [reduced], directory, 'reduced-'+name)
        final[name] = {'run':run,'check':check_native(reduced, values[0]) if values else {'status':'inconclusive'}}
    if final['positive']['check']['status'] != 'passed' or signature(reduced, final['mutant']['check']) != wanted:
        raise RuntimeError('Final reduced artifact did not replay its precise failure')
    report = {'schema':'cordis-verus.lifecycle-reduction/v1','status':'passed',
              'predicate':wanted,'originalCommands':len(case['commands']),'reducedCommands':len(reduced['commands']),
              'originalSha256':E.digest(directory/'original.json'),'reducedSha256':E.digest(directory/'reduced.json'),
              'oneDeletionMinimal':True,'minimumClaim':'one-command deletion under this predicate only',
              'baseline':str(baseline),'baselineSha256':E.digest(baseline),
              'mutant':str(mutant),'mutantSha256':E.digest(mutant),'attempts':attempts,'final':final,
              'replay':['python3','scripts/check-lifecycle-campaign.py','replay','--input',str(directory/'reduced.json'),
                        '--binary',str(mutant),'--binary-sha256',E.digest(mutant),'--expect-failure',wanted['guarantee']]}
    E.write_json(directory/'report.json',report)
    return report
