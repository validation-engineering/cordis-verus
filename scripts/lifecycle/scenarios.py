"""Versioned, seeded commands. This model chooses inputs; Rust executes them.

The small value oracle uses the paper's strict inverse domain (value AND depth).
It never supplies a journal, execution certificate or precomputed runtime state.
"""
import copy
import random

SCHEMA = 'cordis-verus.lifecycle-scenario/v1'
GENERATOR = 'native-lifecycle/1'
REQUIRED_NATIVE = {
    'provider-first', 'consumer-first', 'missing-provider', 'successful-update',
    'child-failure', 'consumer-failure', 'same-value-interference', 'repeated-failure',
    'explicit-retry', 'stale-reply-after-retry', 'stale-reply-new-episode',
    'duplicate-reply', 'fresh-child-after-update', 'shutdown', 'clean-update',
}


class Builder:
    def __init__(self, seed, index):
        rng = random.Random(seed)
        self.seed, self.index = seed, index
        self.parameters = {'values': [rng.randrange(1, 101) for _ in range(3)],
                           'consumer_delta': rng.randrange(0, 11), 'child_delta': rng.randrange(0, 11)}
        self.values = [{'value': v, 'depth': 0} for v in self.parameters['values']]
        self.stacks = {}
        self.writes = {}
        self.steps = []
        self.revision = 0
        self.counter = 0
        self.rng = rng

    def command(self, op, status='ok', **fields):
        self.steps.append({'action': {'op': op, **fields},
                           'expect': {'status': status, 'values': copy.deepcopy(self.values)}})

    def tag(self, purpose):
        self.counter += 1
        return f'{purpose}-{self.counter}'

    def apply(self, amount):
        before = copy.deepcopy(self.values[self.revision])
        after = {'value': before['value'] + amount, 'depth': before['depth'] + 1}
        self.values[self.revision] = after
        return ('value', self.revision, before, copy.deepcopy(after))

    def start(self, actor):
        self.stacks[actor] = []
        if actor != 'provider':
            self.stacks[actor].append(self.apply(self.parameters[f'{actor}_delta']))
        self.command('start', actor=actor, **({'revision': self.revision} if actor == 'provider' else {}))

    def spawn(self):
        self.stacks['consumer'].append(('child',))
        self.stacks['child'] = [self.apply(self.parameters['child_delta'])]
        self.command('spawn')

    def restore(self, actor):
        ticket = self.tag('restore')
        stack = self.stacks[actor]
        if not stack:
            self.command('restore', 'empty', actor=actor, ticket=ticket)
            return ticket
        item = stack[-1]
        if item[0] == 'child':
            stack.pop()
            status = 'restored'
        else:
            _, revision, before, after = item
            if self.values[revision] == after:
                self.values[revision] = copy.deepcopy(before)
                stack.pop()
                status = 'restored'
            else:
                status = 'retained'
        self.command('restore', status, actor=actor, ticket=ticket)
        return ticket

    def write(self, amount):
        label = self.tag('interference')
        self.writes[label] = self.apply(amount)
        self.command('write', revision=self.revision, amount=amount, inverse=label)
        return label

    def undo(self, label):
        _, revision, before, after = self.writes[label]
        assert self.values[revision] == after
        self.values[revision] = copy.deepcopy(before)
        del self.writes[label]
        self.command('undo_write', inverse=label)

    def rejection(self, op, **fields):
        self.command(op, 'rejected', **fields)

    def fail_and_recover(self, actor, interference, repeats, probes):
        failed = self.restore(actor)
        assert self.steps[-1]['expect']['status'] == 'retained'
        self.command('fail', actor=actor)
        self.rejection('release', actor=actor)
        self.rejection('begin_cleanup', actor='provider')
        if actor == 'child':
            self.rejection('begin_cleanup', actor='consumer')
        self.rejection('start', actor='provider', revision=self.revision + 1)
        if probes:
            self.rejection('reply', actor=actor, ticket=failed)
            # A failed inverse does not run again until the explicit retry.
            self.command('restore', 'empty', actor=actor, ticket=self.tag('no-implicit-retry'))
        for _ in range(repeats):
            self.command('retry', actor=actor)
            self.rejection('reply', actor=actor, ticket=failed)
            again = self.restore(actor)
            assert self.steps[-1]['expect']['status'] == 'retained'
            self.command('fail', actor=actor)
            failed = again
        self.undo(interference)
        self.command('retry', actor=actor)
        if probes:
            self.rejection('retry', actor=actor)
        self.rejection('reply', actor=actor, ticket=failed)
        restored = self.restore(actor)
        assert self.steps[-1]['expect']['status'] == 'restored'
        if probes:
            self.rejection('reply', actor=actor, ticket=restored)
        return failed

    def drain(self, *, fault=None, repeats=0, probes=False, shutdown=False, amount=0):
        old = None
        interference = self.write(amount) if fault == 'child' else None
        if not shutdown:
            self.command('replace')
        else:
            self.command('retire', actor='provider')
        self.command('withdraw', actor='provider')
        if shutdown:
            self.command('retire', actor='consumer')
        self.command('withdraw', actor='consumer')
        self.command('retire_child')
        self.command('withdraw', actor='child')
        if probes:
            self.rejection('begin_cleanup', actor='provider')
            self.rejection('begin_cleanup', actor='consumer')
            self.rejection('remove', actor='provider')
        self.command('begin_cleanup', actor='child')
        if fault == 'child':
            old = self.fail_and_recover('child', interference, repeats, probes)
        else:
            self.restore('child')
        self.command('release', actor='child')
        self.command('begin_cleanup', actor='consumer')
        self.restore('consumer')  # The actual Child request has its own inverse.
        if fault == 'consumer':
            interference = self.write(amount)
            old = self.fail_and_recover('consumer', interference, repeats, probes)
        else:
            self.restore('consumer')
        self.command('release', actor='consumer')
        self.command('remove', actor='child')
        if shutdown:
            self.command('remove', actor='consumer')
        self.command('begin_cleanup', actor='provider')
        self.command('release', actor='provider')
        if shutdown:
            self.command('remove', actor='provider')
        return old

    def build(self):
        # Deterministic strata ensure that coverage is not an accident of RNG.
        fault = (None, 'child', 'consumer')[self.index % 3]
        probes = self.index % 3 != 0 or self.index % 2 == 1
        consumer_first = self.index % 2 == 1
        amount = 0 if self.index % 2 == 1 else self.rng.randrange(1, 11)
        repeats = self.index % 3 if fault else 0
        order = ['consumer', 'provider'] if consumer_first else ['provider', 'consumer']
        self.command('register', actor=order[0])
        if consumer_first and probes:
            self.rejection('start', actor='consumer')
        self.command('register', actor=order[1])
        self.start('provider'); self.start('consumer'); self.spawn()
        for _ in range(self.rng.randrange(1, 5)):
            self.command('observe')
        old = self.drain(fault=fault, repeats=repeats, probes=probes, amount=amount)
        self.revision = 1
        self.start('provider'); self.start('consumer'); self.spawn()
        if old:
            self.rejection('reply', actor=fault, ticket=old)
        # Every recovered scenario also exercises a subsequent successful update.
        if fault or self.index % 2 == 0:
            self.drain(probes=probes)
            self.revision = 2
            self.start('provider'); self.start('consumer'); self.spawn()
        self.drain(shutdown=True, probes=probes)
        return {'schema': SCHEMA, 'profile': 'native-managed/v1',
                'id': f'native-{self.index:04}-{self.seed}', 'seed': self.seed, 'generator': GENERATOR,
                'category': 'interference' if fault else ('invalid-commands' if probes else 'admitted'),
                'families': [f'{fault}-fault' if fault else 'no-fault', 'one-child', 'provider-update'],
                'purpose': 'campaign', 'parameters': self.parameters, 'commands': self.steps}


def generate_native(seed=260824, count=96):
    if type(seed) is not int or not 0 <= seed < 2**32 or type(count) is not int or not 6 <= count <= 4096:
        raise ValueError('Native campaign requires a u32 seed and 6..4096 cases')
    return [Builder((seed + i) % 2**32, i).build() for i in range(count)]


def baseline():
    return {'cases': [generate_native(count=6)[0]]}
