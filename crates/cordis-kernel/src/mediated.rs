//! Definition 30 and Lemma 39, with operation preconditions and partial inverses.
//! The grammar is a least closed set, not a bounded iterator unrolling.
#[cfg(verus_keep_ghost)]
use crate::{calculus, observation};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(V)]
pub struct ValueYield<V, O> {
    pub value: V,
    pub undo: spec_fn(V) -> Option<V>,
    pub outcome: O,
}
pub type Operation<V, O> = spec_fn(V) -> Option<ValueYield<V, O>>;

#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(O)]
pub enum Node<K, V, O> {
    Unit,
    Operation { key: K, operation: Operation<V, O>, select: spec_fn(O) -> Option<nat> },
    Provision { key: K, value: V, next: Option<nat> },
}

pub type Program<K, V, O> = spec_fn(nat) -> Node<K, V, O>;
pub type Allowed<K, V, O> = spec_fn(K, Operation<V, O>) -> bool;

pub type PartialMap<S> = spec_fn(S) -> Option<S>;
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
pub struct Stage<K, V> {
    pub state: IMap<K, V>,
    pub undo: PartialMap<IMap<K, V>>,
    pub next: Option<nat>,
}

pub open spec fn partial_related<S>(eq: spec_fn(S, S) -> bool,
    left: spec_fn(S) -> Option<S>, right: spec_fn(S) -> Option<S>) -> bool
{
    forall|a: S, b: S| #![trigger left(a), right(b)] eq(a, b) ==> {
        &&& left(a).is_some() == right(b).is_some()
        &&& (left(a).is_some() ==> eq(left(a).unwrap(), right(b).unwrap()))
    }
}

pub open spec fn operation_admissible<V, O>(eq: spec_fn(V, V) -> bool, op: Operation<V, O>) -> bool {
    &&& forall|a: V, b: V| #![trigger op(a), op(b)] eq(a, b) ==> {
        &&& op(a).is_some() == op(b).is_some()
        &&& (op(a).is_some() ==> {
            let x = op(a).unwrap(); let y = op(b).unwrap();
            &&& eq(x.value, y.value) && x.outcome == y.outcome
            &&& partial_related(eq, x.undo, y.undo)
        })
    }
    &&& forall|a: V| #[trigger] op(a).is_some() ==> (op(a).unwrap().undo)(op(a).unwrap().value) == Some(a)
}

pub open spec fn lift_inverse<K, V>(key: K, inverse: spec_fn(V) -> Option<V>) -> spec_fn(IMap<K, V>) -> Option<IMap<K, V>> {
    |s: IMap<K, V>| if !s.dom().contains(key) { None }
        else { match inverse(s[key]) { Some(v) => Some(s.insert(key, v)), None => None } }
}

pub open spec fn run<K, V, O>(node: Node<K, V, O>, s: IMap<K, V>) -> Option<Stage<K, V>> {
    match node {
        Node::Unit => Some(Stage { state: s, undo: |x: IMap<K, V>| Some(x), next: None }),
        Node::Operation { key, operation, select: next } => {
            if !s.dom().contains(key) { None }
            else { match operation(s[key]) {
                None => None,
                Some(y) => Some(Stage { state: s.insert(key, y.value), undo: lift_inverse(key, y.undo), next: next(y.outcome) }),
            } }
        },
        Node::Provision { key, value, next } => {
            if s.dom().contains(key) { None }
            else { Some(Stage { state: s.insert(key, value), undo: |x: IMap<K, V>| if x.dom().contains(key) { Some(x.remove(key)) } else { None }, next }) }
        },
    }
}

pub open spec fn stage_respects<K, V, O>(eq: spec_fn(K, V, V) -> bool, keys: ISet<K>, node: Node<K, V, O>) -> bool {
    forall|a: IMap<K, V>, b: IMap<K, V>| #![trigger run(node, a), run(node, b)]
        observation::context_equal(eq, keys, a, b) ==> {
            &&& run(node, a).is_some() == run(node, b).is_some()
            &&& (run(node, a).is_some() ==> {
                let x = run(node, a).unwrap(); let y = run(node, b).unwrap();
                &&& observation::context_equal(eq, keys, x.state, y.state)
                &&& partial_related(|s: IMap<K, V>, t: IMap<K, V>| observation::context_equal(eq, keys, s, t), x.undo, y.undo)
                &&& x.next == y.next
            })
        }
}

pub open spec fn stage_witness<K, V, O>(node: Node<K, V, O>) -> bool {
    forall|s: IMap<K, V>| #[trigger] run(node, s).is_some()
        ==> (run(node, s).unwrap().undo)(run(node, s).unwrap().state) == Some(s)
}

pub proof fn update_related<K, V>(eq: spec_fn(K, V, V) -> bool, keys: ISet<K>, key: K,
    a: IMap<K, V>, b: IMap<K, V>, value: V, other: V)
    requires observation::context_equal(eq, keys, a, b), eq(key, value, other),
    ensures observation::context_equal(eq, keys, a.insert(key, value), b.insert(key, other)),
{
    assert forall|k: K| keys.contains(k) && a.insert(key, value).dom().contains(k) implies
        eq(k, a.insert(key, value)[k], b.insert(key, other)[k]) by { if k != key { assert(a.dom().contains(k)); } }
}

pub proof fn remove_related<K, V>(eq: spec_fn(K, V, V) -> bool, keys: ISet<K>, key: K,
    a: IMap<K, V>, b: IMap<K, V>)
    requires observation::context_equal(eq, keys, a, b),
    ensures observation::context_equal(eq, keys, a.remove(key), b.remove(key)),
{ }

pub proof fn inverse_lift_respects<K, V>(eq: spec_fn(K, V, V) -> bool, keys: ISet<K>, key: K,
    inverse: spec_fn(V) -> Option<V>, other: spec_fn(V) -> Option<V>)
    requires keys.contains(key), partial_related(|a: V, b: V| eq(key, a, b), inverse, other),
    ensures partial_related(|a: IMap<K, V>, b: IMap<K, V>| observation::context_equal(eq, keys, a, b),
        lift_inverse(key, inverse), lift_inverse(key, other)),
{
    let left = lift_inverse(key, inverse); let right = lift_inverse(key, other);
    assert forall|a: IMap<K, V>, b: IMap<K, V>| #![trigger left(a), right(b)]
        observation::context_equal(eq, keys, a, b) implies {
            &&& left(a).is_some() == right(b).is_some()
            &&& (left(a).is_some() ==> observation::context_equal(eq, keys, left(a).unwrap(), right(b).unwrap()))
        } by {
        if a.dom().contains(key) {
            assert(eq(key, a[key], b[key]));
            assert(inverse(a[key]).is_some() == other(b[key]).is_some());
            if inverse(a[key]).is_some() {
                update_related(eq, keys, key, a, b, inverse(a[key]).unwrap(), other(b[key]).unwrap());
            }
        }
    }
}

pub proof fn unit_admissible<K, V, O>(eq: spec_fn(K, V, V) -> bool, keys: ISet<K>)
    ensures stage_respects(eq, keys, Node::<K, V, O>::Unit), stage_witness(Node::<K, V, O>::Unit),
{ }

pub proof fn operation_admissible_lift<K, V, O>(eq: spec_fn(K, V, V) -> bool, keys: ISet<K>, key: K,
    operation: Operation<V, O>, next: spec_fn(O) -> Option<nat>)
    requires keys.contains(key), operation_admissible(|a: V, b: V| eq(key, a, b), operation),
    ensures stage_respects(eq, keys, Node::Operation { key, operation, select: next }),
        stage_witness(Node::Operation { key, operation, select: next }),
{
    let node = Node::Operation { key, operation, select: next };
    assert forall|a: IMap<K, V>, b: IMap<K, V>| #![trigger run(node, a), run(node, b)]
        observation::context_equal(eq, keys, a, b) implies {
            &&& run(node, a).is_some() == run(node, b).is_some()
            &&& (run(node, a).is_some() ==> {
                let x = run(node, a).unwrap(); let y = run(node, b).unwrap();
                &&& observation::context_equal(eq, keys, x.state, y.state)
                &&& partial_related(|s: IMap<K, V>, t: IMap<K, V>| observation::context_equal(eq, keys, s, t), x.undo, y.undo)
                &&& x.next == y.next
            })
        } by {
        if a.dom().contains(key) {
            assert(eq(key, a[key], b[key]));
            assert(operation(a[key]).is_some() == operation(b[key]).is_some());
            if operation(a[key]).is_some() {
                let x = operation(a[key]).unwrap(); let y = operation(b[key]).unwrap();
                update_related(eq, keys, key, a, b, x.value, y.value);
                inverse_lift_respects(eq, keys, key, x.undo, y.undo);
                assert(x.outcome == y.outcome);
                assert(next(x.outcome) == next(y.outcome));
            }
        }
    }
    assert forall|s: IMap<K, V>| #[trigger] run(node, s).is_some() implies
        (run(node, s).unwrap().undo)(run(node, s).unwrap().state) == Some(s) by {
        let y = operation(s[key]).unwrap();
        assert((y.undo)(y.value) == Some(s[key]));
        assert(s.insert(key, y.value).insert(key, s[key]) =~= s);
    }
}

/// Definition 20 restriction is undefined when the binding to withdraw is
/// absent. Failure is retained even though removal itself is idempotent.
pub proof fn provision_inverse_domain<K, V, O>(key: K, value: V, next: Option<nat>, input: IMap<K, V>, current: IMap<K, V>)
    requires !input.dom().contains(key),
    ensures (run(Node::<K, V, O>::Provision { key, value, next }, input).unwrap().undo)(current).is_some()
        == current.dom().contains(key),
        !current.dom().contains(key) ==> (run(Node::<K, V, O>::Provision { key, value, next }, input).unwrap().undo)(current) == None,
{ }

pub proof fn provision_admissible<K, V, O>(eq: spec_fn(K, V, V) -> bool, keys: ISet<K>, key: K, value: V, next: Option<nat>)
    requires keys.contains(key), eq(key, value, value),
    ensures stage_respects(eq, keys, Node::<K, V, O>::Provision { key, value, next }),
        stage_witness(Node::<K, V, O>::Provision { key, value, next }),
{
    let node = Node::<K, V, O>::Provision { key, value, next };
    let inverse = |s: IMap<K, V>| if s.dom().contains(key) { Some(s.remove(key)) } else { None };
    assert(partial_related(|a: IMap<K, V>, b: IMap<K, V>| observation::context_equal(eq, keys, a, b), inverse, inverse)) by {
        assert forall|a: IMap<K, V>, b: IMap<K, V>| #![trigger inverse(a), inverse(b)]
            observation::context_equal(eq, keys, a, b) implies {
                &&& inverse(a).is_some() == inverse(b).is_some()
                &&& (inverse(a).is_some() ==> observation::context_equal(eq, keys, inverse(a).unwrap(), inverse(b).unwrap()))
            } by { remove_related(eq, keys, key, a, b); }
    }
    assert forall|a: IMap<K, V>, b: IMap<K, V>| #![trigger run(node, a), run(node, b)]
        observation::context_equal(eq, keys, a, b) implies {
            &&& run(node, a).is_some() == run(node, b).is_some()
            &&& (run(node, a).is_some() ==> {
                let x = run(node, a).unwrap(); let y = run(node, b).unwrap();
                &&& observation::context_equal(eq, keys, x.state, y.state)
                &&& partial_related(|s: IMap<K, V>, t: IMap<K, V>| observation::context_equal(eq, keys, s, t), x.undo, y.undo)
                &&& x.next == y.next
            })
        } by { if !a.dom().contains(key) { update_related(eq, keys, key, a, b, value, value); } }
    assert forall|s: IMap<K, V>| #[trigger] run(node, s).is_some() implies
        (run(node, s).unwrap().undo)(run(node, s).unwrap().state) == Some(s) by {
        assert(!s.dom().contains(key));
        assert(s.insert(key, value).remove(key) =~= s);
    }
}

pub open spec fn continuations<K, V, O>(node: Node<K, V, O>, names: ISet<nat>) -> bool {
    match node {
        Node::Unit => true,
        Node::Operation { select: next, .. } => forall|outcome: O| #[trigger] next(outcome).is_some() ==> names.contains(next(outcome).unwrap()),
        Node::Provision { next, .. } => next.is_some() ==> names.contains(next.unwrap()),
    }
}

pub open spec fn permitted<K, V, O>(allowed: Allowed<K, V, O>, keys: ISet<K>, provisions: ISet<K>, node: Node<K, V, O>) -> bool {
    match node {
        Node::Unit => true,
        Node::Operation { key, operation, .. } => keys.contains(key) && allowed(key, operation),
        Node::Provision { key, .. } => provisions.contains(key),
    }
}

pub open spec fn closed<K, V, O>(program: Program<K, V, O>, allowed: Allowed<K, V, O>, keys: ISet<K>, provisions: ISet<K>, names: ISet<nat>) -> bool {
    forall|id: nat| permitted(allowed, keys, provisions, program(id)) && continuations(program(id), names) ==> names.contains(id)
}

/// The intersection of all sets closed under the actual grammar constructors.
/// Unlike a natural-number height bound, this admits unbounded branching over
/// outcomes while excluding unsupported cycles from the least fixed point.
pub open spec fn member<K, V, O>(program: Program<K, V, O>, allowed: Allowed<K, V, O>, keys: ISet<K>, provisions: ISet<K>, id: nat) -> bool {
    forall|names: ISet<nat>| closed(program, allowed, keys, provisions, names) ==> names.contains(id)
}

pub open spec fn members<K, V, O>(program: Program<K, V, O>, allowed: Allowed<K, V, O>, keys: ISet<K>, provisions: ISet<K>) -> ISet<nat> {
    ISet::new(|id: nat| member(program, allowed, keys, provisions, id))
}

pub proof fn constructor_member<K, V, O>(program: Program<K, V, O>, allowed: Allowed<K, V, O>, keys: ISet<K>, provisions: ISet<K>, id: nat)
    requires permitted(allowed, keys, provisions, program(id)), continuations(program(id), members(program, allowed, keys, provisions)),
    ensures member(program, allowed, keys, provisions, id),
{
    assert forall|names: ISet<nat>| closed(program, allowed, keys, provisions, names) implies names.contains(id) by {
        match program(id) {
            Node::Unit => { },
            Node::Operation { select: next, .. } => {
                assert forall|outcome: O| #[trigger] next(outcome).is_some() implies names.contains(next(outcome).unwrap()) by {
                    assert(member(program, allowed, keys, provisions, next(outcome).unwrap()));
                }
            },
            Node::Provision { next, .. } => {
                if next.is_some() { assert(member(program, allowed, keys, provisions, next.unwrap())); }
            },
        }
        assert(continuations(program(id), names));
    }
}

pub open spec fn key_equivalence<K, V>(eq: spec_fn(K, V, V) -> bool, key: K) -> bool {
    calculus::equivalence(|a: V, b: V| eq(key, a, b))
}

pub open spec fn primitive_theory<K, V, O>(eq: spec_fn(K, V, V) -> bool, allowed: Allowed<K, V, O>) -> bool {
    &&& forall|key: K| #[trigger] key_equivalence(eq, key)
    &&& forall|key: K, op: Operation<V, O>| #[trigger] allowed(key, op)
        ==> operation_admissible(|a: V, b: V| eq(key, a, b), op)
}

pub proof fn permitted_admissible<K, V, O>(eq: spec_fn(K, V, V) -> bool, program: Program<K, V, O>, allowed: Allowed<K, V, O>, keys: ISet<K>, provisions: ISet<K>, id: nat)
    requires primitive_theory(eq, allowed), provisions.subset_of(keys), permitted(allowed, keys, provisions, program(id)),
    ensures stage_respects(eq, keys, program(id)), stage_witness(program(id)),
{
    match program(id) {
        Node::Unit => { unit_admissible::<K, V, O>(eq, keys); },
        Node::Operation { key, operation, select: next } => {
            operation_admissible_lift(eq, keys, key, operation, next);
        },
        Node::Provision { key, value, next } => {
            assert(key_equivalence(eq, key));
            let local = |a: V, b: V| eq(key, a, b);
            assert(calculus::equivalence(local));
            assert(local(value, value));
            assert(eq(key, value, value));
            provision_admissible::<K, V, O>(eq, keys, key, value, next);
        },
    }
}

/// Lemma 39: least-grammar membership implies local observational respect,
/// exact recovery and the same property recursively for every continuation.
/// Operation preconditions and inverse definedness are retained throughout.
pub proof fn context_mediated_admissible<K, V, O>(eq: spec_fn(K, V, V) -> bool, program: Program<K, V, O>, allowed: Allowed<K, V, O>, keys: ISet<K>, provisions: ISet<K>, id: nat)
    requires primitive_theory(eq, allowed), provisions.subset_of(keys), member(program, allowed, keys, provisions, id),
    ensures stage_respects(eq, keys, program(id)), stage_witness(program(id)),
        continuations(program(id), members(program, allowed, keys, provisions)),
{
    let good = ISet::new(|n: nat| stage_respects(eq, keys, program(n)) && stage_witness(program(n))
        && continuations(program(n), members(program, allowed, keys, provisions))
        && member(program, allowed, keys, provisions, n));
    assert(closed(program, allowed, keys, provisions, good)) by {
        assert forall|n: nat| permitted(allowed, keys, provisions, program(n)) && continuations(program(n), good)
            implies good.contains(n) by {
            permitted_admissible(eq, program, allowed, keys, provisions, n);
            match program(n) {
                Node::Unit => { },
                Node::Operation { select: next, .. } => {
                    assert forall|outcome: O| #[trigger] next(outcome).is_some() implies
                        members(program, allowed, keys, provisions).contains(next(outcome).unwrap()) by {
                        assert(good.contains(next(outcome).unwrap()));
                    }
                },
                Node::Provision { next, .. } => {
                    if next.is_some() { assert(good.contains(next.unwrap())); }
                },
            }
            assert(continuations(program(n), members(program, allowed, keys, provisions)));
            constructor_member(program, allowed, keys, provisions, n);
        }
    }
    assert(good.contains(id));
}

pub proof fn member_permitted<K, V, O>(program: Program<K, V, O>, allowed: Allowed<K, V, O>, keys: ISet<K>, provisions: ISet<K>, id: nat)
    requires member(program, allowed, keys, provisions, id),
    ensures permitted(allowed, keys, provisions, program(id)),
{
    let legal = ISet::new(|n: nat| permitted(allowed, keys, provisions, program(n)));
    assert(closed(program, allowed, keys, provisions, legal));
    assert(legal.contains(id));
}

pub open spec fn covered_node<K, V, O>(keys: ISet<K>, node: Node<K, V, O>) -> bool {
    match node {
        Node::Unit => true,
        Node::Operation { key, .. } | Node::Provision { key, .. } => keys.contains(key),
    }
}

pub open spec fn coverage<K, V, O>(program: Program<K, V, O>, keys: ISet<K>, names: ISet<nat>) -> bool {
    forall|n: nat| names.contains(n) ==> covered_node(keys, program(n)) && continuations(program(n), names)
}

/// Every named continuation, including outcomes not selected in one particular
/// run, stays within a set whose stages act only at observed keys.
pub open spec fn covered<K, V, O>(program: Program<K, V, O>, keys: ISet<K>, id: nat) -> bool {
    exists|names: ISet<nat>| names.contains(id) && coverage(program, keys, names)
}

pub proof fn covered_continuations<K, V, O>(program: Program<K, V, O>, keys: ISet<K>, id: nat)
    requires covered(program, keys, id),
    ensures covered_node(keys, program(id)),
        continuations(program(id), ISet::new(|n: nat| covered(program, keys, n))),
{
    let names = choose|names: ISet<nat>| names.contains(id) && coverage(program, keys, names);
    match program(id) {
        Node::Unit => { },
        Node::Operation { select: next, .. } => {
            assert forall|outcome: O| #[trigger] next(outcome).is_some() implies covered(program, keys, next(outcome).unwrap()) by {
                assert(names.contains(next(outcome).unwrap()));
            }
        },
        Node::Provision { next, .. } => {
            if next.is_some() { assert(names.contains(next.unwrap())); }
        },
    }
}

/// Lemma 39's separate observation set S need only contain the keys of this
/// iterator's reachable stages; it need not contain every unrelated declaration
/// in the program's construction interface S'.
pub proof fn restricted_admissibility<K, V, O>(eq: spec_fn(K, V, V) -> bool, program: Program<K, V, O>, allowed: Allowed<K, V, O>, declared: ISet<K>, provisions: ISet<K>, observed: ISet<K>, id: nat)
    requires primitive_theory(eq, allowed), provisions.subset_of(declared),
        member(program, allowed, declared, provisions, id), covered(program, observed, id),
    ensures stage_respects(eq, observed, program(id)), stage_witness(program(id)),
        continuations(program(id), ISet::new(|n: nat| member(program, allowed, declared, provisions, n)
            && covered(program, observed, n))),
{
    member_permitted(program, allowed, declared, provisions, id);
    context_mediated_admissible(eq, program, allowed, declared, provisions, id);
    covered_continuations(program, observed, id);
    match program(id) {
        Node::Unit => { unit_admissible::<K, V, O>(eq, observed); },
        Node::Operation { key, operation, select: next } => {
            operation_admissible_lift(eq, observed, key, operation, next);
            assert forall|outcome: O| #[trigger] next(outcome).is_some() implies
                member(program, allowed, declared, provisions, next(outcome).unwrap()) && covered(program, observed, next(outcome).unwrap()) by { }
        },
        Node::Provision { key, value, next } => {
            let local = |a: V, b: V| eq(key, a, b);
            assert(key_equivalence(eq, key));
            assert(calculus::equivalence(local));
            assert(local(value, value));
            provision_admissible::<K, V, O>(eq, observed, key, value, next);
        },
    }
}

/// Every inverse actually returned by an admitted iterator descends to the
/// observational quotient, with its partial domain retained, and restores the
/// exact input table at the state where the corresponding stage just landed.
pub proof fn yielded_inverse_respects<K, V, O>(eq: spec_fn(K, V, V) -> bool, program: Program<K, V, O>, allowed: Allowed<K, V, O>, declared: ISet<K>, provisions: ISet<K>, observed: ISet<K>, id: nat, input: IMap<K, V>)
    requires primitive_theory(eq, allowed), provisions.subset_of(declared),
        member(program, allowed, declared, provisions, id), covered(program, observed, id), run(program(id), input).is_some(),
    ensures {
        let result = run(program(id), input).unwrap();
        &&& partial_related(|a: IMap<K, V>, b: IMap<K, V>| observation::context_equal(eq, observed, a, b), result.undo, result.undo)
        &&& (result.undo)(result.state) == Some(input)
    },
{
    restricted_admissibility(eq, program, allowed, declared, provisions, observed, id);
    assert forall|key: K| observed.contains(key) implies calculus::equivalence(|a: V, b: V| eq(key, a, b)) by {
        assert(key_equivalence(eq, key));
    }
    observation::context_equivalence(eq, observed);
    let ctx = |a: IMap<K, V>, b: IMap<K, V>| observation::context_equal(eq, observed, a, b);
    assert(calculus::equivalence(ctx));
    assert(ctx(input, input));
}

} // verus!
