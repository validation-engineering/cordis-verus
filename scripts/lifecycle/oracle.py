"""Independent behavioral checks over unmodified production observations.

No function here creates an executable kernel state or a proof certificate.
The oracle keeps the raw trace, checks relational identities and strict values,
and reports the FIRST violated guarantee separately from executor failures.
"""
from collections import Counter


class Violation(Exception):
    def __init__(self, code, index, detail):
        self.code, self.index, self.detail = code, index, detail
        super().__init__(f'{code} at command {index}: {detail}')


def check_native(case, result):
    coverage = set()
    counts = Counter()
    ids = {}
    generations = {}
    consumed = set()
    failed = {}
    retries = set()
    births = []
    actions = set()
    registers = []
    starts = Counter()
    retained = Counter()
    before = result.get('initial')

    def require(condition, code, index, detail):
        if not condition:
            raise Violation(code, index, detail)

    def plugin(state, role):
        return next((p for p in state['plugins'] if p['id'] == ids.get(role)), None)

    def frame(state, index):
        plugins = {p['id']: p for p in state['plugins']}
        require(len(plugins) == len(state['plugins']), 'unique-registration', index, state['plugins'])
        for p in state['plugins']:
            if p['phase'] == 'Inactive':
                require(not p['committed'], 'inactive-has-no-commitments', index, p)
            for binding in p['committed']:
                provider = plugins.get(binding['provider'])
                require(provider is not None and provider['phase'] != 'Inactive' and not provider['cleanupStarted'],
                        'committed-provider-protection', index, {'consumer':p,'binding':binding,'provider':provider})
            execution = p['execution']
            if execution and execution['phase'] != 'Closed':
                require(execution['belongs'], 'execution-owner-association', index, p)

    try:
        require(result.get('id') == case['id'], 'input-association', -1, result.get('id'))
        require(before is not None, 'missing-initial-observation', -1, result.get('status'))
        require(before['plugins'] == [] and before['values'] == [{'value':v,'depth':0} for v in case['parameters']['values']],
                'initial-resources', -1, before)
        rows = result.get('steps', [])
        for index, row in enumerate(rows):
            require(index < len(case['commands']), 'extra-command', index, row)
            spec = case['commands'][index]
            action, expected = spec['action'], spec['expect']
            require(row.get('index') == index and row.get('action') == action, 'executed-command', index, row)
            outcome, state = row['outcome'], row['state']
            op, status = action['op'], outcome['status']
            require(status == expected['status'], 'api-outcome:' + op, index,
                    {'expected':expected['status'],'actual':outcome})
            require(state['values'] == expected['values'], 'strict-resource-state', index,
                    {'expected':expected['values'],'actual':state['values']})
            counts[status] += 1
            if status == 'rejected' and op in {'start','begin_cleanup','release','retry','reply','remove'}:
                require(state == before, 'rejection-preserves-state:' + op, index, action)
            role = action.get('actor')
            if op == 'register' and status == 'ok':
                identifier = outcome['data']['id']
                require(identifier not in ids.values(), 'fresh-registration', index, identifier)
                ids[role] = identifier
                registers.append(role)
                coverage.add('provider-first' if registers[0] == 'provider' else 'consumer-first')
            if op == 'start':
                if status == 'rejected' and role == 'consumer' and starts['provider'] == 0:
                    coverage.add('missing-provider')
                if status == 'ok':
                    starts[role] += 1
                    p = plugin(state, role)
                    require(p is not None and p['phase'] == 'Active' and p['execution']['belongs'], 'actual-root-finish', index, p)
                    ticket = p['execution']['ticket']
                    require(ticket['owner'] == p['id'] and ticket['kind'] == 'Setup', 'root-origin', index, ticket)
                    if role in generations:
                        require(ticket['generation'] > generations[role], 'fresh-episode', index, ticket)
                    generations[role] = ticket['generation']
                    if role == 'provider':
                        require(state['publications']['value'], 'provider-publication', index, state['publications'])
                        if starts[role] > 1: coverage.add('successful-update')
                    if role == 'consumer':
                        require(any(b['key'] == 1 and b['provider'] == ids['provider'] for b in p['committed']),
                                'consumer-committed-provider', index, p)
                        require(state['publications']['marker'], 'consumer-publication', index, state['publications'])
            if op == 'spawn' and status == 'ok':
                child = outcome['data']['id']
                require(child not in births, 'fresh-child', index, child)
                ids['child'] = child
                p = plugin(state, 'child')
                handle = state['children'][-1]
                require(handle['id'] == child and handle['parent'] == ids['consumer']
                        and handle['generation'] == generations['consumer'],
                        'child-request-inverse-identity', index, {'handle':handle,'child':child})
                require(p['parent'] == ids['consumer'] and p['execution']['belongs'], 'child-parent-execution', index, p)
                for key, provider in ((1, ids['provider']), (2, ids['consumer'])):
                    require(any(b['key'] == key and b['provider'] == provider for b in p['committed']),
                            'child-explicit-dependencies', index, p)
                births.append(child)
                if len(births) > 1: coverage.add('fresh-child-after-update')
            if op in {'begin_cleanup','retry'} and status == 'ok':
                ticket = outcome['data']
                identity = (ticket['domain'], ticket['action'])
                p = plugin(state, role)
                require(identity not in actions and ticket == p['pending']
                        and ticket['owner'] == ids[role] and ticket['generation'] == p['execution']['ticket']['generation'],
                        'fresh-cleanup-authority', index, ticket)
                actions.add(identity)
                if op == 'retry':
                    require(not p['execution']['failed'], 'retry-clears-failure', index, p)
                    retries.add(role); coverage.add('explicit-retry')
            if op == 'restore' and status in {'restored','retained'}:
                ticket = outcome['ticket']
                p = plugin(state, role)
                require(ticket['domain'] == p['execution']['rootQueue']['domain'], 'inverse-owner-domain', index, ticket)
                if status == 'retained':
                    retained[role] += 1
                    coverage.add(role + '-failure')
                    queue = p['execution']['rootQueue']
                    require(queue['failed'] and queue['canRetry'] and not queue['empty'], 'retained-inverse-payload', index, queue)
                    require(state['values'] == before['values'], 'failed-restore-preserves-resource', index, state['values'])
                    failed[role] = ticket
                    if retained[role] > 1: coverage.add('repeated-failure')
                else:
                    consumed.add(action['ticket'])
                    if outcome['kind'] == 'child':
                        require(outcome['child'] == ids['child'], 'inverse-retires-own-child', index, outcome)
                    if role in failed:
                        old = failed[role]
                        require(ticket['token'] == old['token'] and ticket['domain'] == old['domain']
                                and ticket['attempt'] > old['attempt'], 'retry-retains-token-refreshes-attempt', index, {'old':old,'new':ticket})
                        del failed[role]
            if op == 'reply' and status == 'rejected':
                if action['ticket'] in consumed: coverage.add('duplicate-reply')
                if role in retries: coverage.add('stale-reply-after-retry')
                p = plugin(state, role)
                if state['tickets'][action['ticket']]['domain'] != p['execution']['rootQueue']['domain']:
                    coverage.add('stale-reply-new-episode')
            if op == 'write' and status == 'ok' and action['amount'] == 0:
                coverage.add('same-value-interference')
            if op == 'release' and status == 'ok':
                p = plugin(state, role)
                require(p['phase'] == 'Inactive' and not p['committed'] and p['execution']['phase'] == 'Closed',
                        'successful-release', index, p)
            frame(state,index)
            before = state
        require(result.get('status') == 'executed' and len(rows) == len(case['commands']),
                'executor-incomplete', len(rows), {'status':result.get('status'),'at':result.get('at')})
        if starts['provider'] > 1 and not retained:
            coverage.add('clean-update')
        if not before['plugins'] and not before['rawInverses'] and before['values'] == [{'value':v,'depth':0} for v in case['parameters']['values']]:
            coverage.add('shutdown')
        if case['purpose'] == 'campaign':
            require('shutdown' in coverage, 'complete-shutdown', len(rows), before)
            require(before['publications']=={'value':False,'marker':False,'retainedValues':0},
                    'shutdown-reclaims-publications',len(rows),before['publications'])
            require(starts['provider'] >= 2 and starts['consumer'] >= 2 and len(births) >= 2,
                    'nonempty-supported-success', len(rows), dict(starts))
        return {'status':'passed','coverage':sorted(coverage),'outcomes':dict(counts)}
    except (KeyError, TypeError, IndexError) as error:
        return {'status':'inconclusive','reason':'malformed executor observation: '+str(error)}
    except Violation as error:
        # A failure before a later executor crash is still a concrete witnessed
        # property failure. A crash without such a prefix is not a detection.
        return {'status':'inconclusive' if error.code in {'executor-incomplete','missing-initial-observation'} else 'failed',
                'failure':{'code':error.code,'index':error.index,'detail':error.detail},
                'coverage':sorted(coverage),'outcomes':dict(counts)}
