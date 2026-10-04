//! Definition 51: the union of all registered service tables, restricted by key.
//! Inactive and Loading tables participate exactly as Active tables do. This is
//! the recovery observation, distinct from Active-only service publication.
#[cfg(verus_keep_ghost)]
use crate::{mediated, observation, preservation as inv, semantics as full, Port};
use vstd::prelude::*;

verus! {

pub open spec fn owns<V>(s: full::State<V>, key: Port, owner: usize) -> bool {
    full::registered(s, owner) && s.tables[owner].dom().contains(key)
}

pub open spec fn unambiguous<V>(s: full::State<V>) -> bool {
    forall|key: Port, a: usize, b: usize| owns(s, key, a) && owns(s, key, b) ==> a == b
}

pub open spec fn owner<V>(s: full::State<V>, key: Port) -> usize {
    choose|n: usize| owns(s, key, n)
}

pub open spec fn project<V>(s: full::State<V>, keys: ISet<Port>) -> IMap<Port, V> {
    IMap::new(|key: Port| keys.contains(key) && exists|n: usize| owns(s, key, n),
        |key: Port| s.tables[owner(s, key)][key])
}

pub proof fn unique_owner<V>(s: full::State<V>)
    requires inv::well_formed(s),
    ensures unambiguous(s),
{
    assert forall|key: Port, a: usize, b: usize| owns(s, key, a) && owns(s, key, b) implies a == b by {
        assert(s.control.fibers[a].provisions.contains(key));
        assert(s.control.fibers[b].provisions.contains(key));
    }
}

/// No phase condition occurs in this law: a provision written while Loading is
/// immediately part of the witness's coeffect projection.
pub proof fn lookup<V>(s: full::State<V>, keys: ISet<Port>, key: Port, n: usize)
    requires unambiguous(s), keys.contains(key), owns(s, key, n),
    ensures project(s, keys).dom().contains(key), owner(s, key) == n,
        project(s, keys)[key] == s.tables[n][key],
{
    assert(exists|m: usize| owns(s, key, m));
    assert(owns(s, key, owner(s, key)));
}

pub proof fn restriction<V>(s: full::State<V>, keys: ISet<Port>)
    ensures project(s, keys) == project(s, ISet::full()).restrict(keys),
{
    assert(project(s, keys) =~= project(s, ISet::full()).restrict(keys));
}

pub open spec fn bindings_equal<V>(a: full::State<V>, b: full::State<V>) -> bool {
    forall|key: Port, n: usize| owns(a, key, n) == owns(b, key, n)
        && (owns(a, key, n) ==> a.tables[n][key] == b.tables[n][key])
}

pub proof fn projection_equal<V>(a: full::State<V>, b: full::State<V>, keys: ISet<Port>)
    requires unambiguous(a), unambiguous(b), bindings_equal(a, b),
    ensures project(a, keys) == project(b, keys),
{
    assert(project(a, keys) =~= project(b, keys)) by {
        assert forall|key: Port| project(a, keys).dom().contains(key) == project(b, keys).dom().contains(key) by {
            if project(a, keys).dom().contains(key) {
                let n = choose|n: usize| owns(a, key, n);
                assert(owns(b, key, n));
            }
            if project(b, keys).dom().contains(key) {
                let n = choose|n: usize| owns(b, key, n);
                assert(owns(a, key, n));
            }
        }
        assert forall|key: Port| project(a, keys).dom().contains(key) implies project(a, keys)[key] == project(b, keys)[key] by {
            let n = choose|n: usize| owns(a, key, n);
            lookup(a, keys, key, n);
            lookup(b, keys, key, n);
        }
    }
}

pub proof fn empty_insertion<V>(a: full::State<V>, z: full::State<V>, child: usize, keys: ISet<Port>)
    requires inv::well_formed(a), inv::insert_map(a, z, child),
    ensures project(a, keys) == project(z, keys),
{
    inv::insert_preservation(a, z, child);
    unique_owner(a); unique_owner(z);
    assert(bindings_equal(a, z)) by {
        assert forall|key: Port, n: usize| owns(a, key, n) == owns(z, key, n)
            && (owns(a, key, n) ==> a.tables[n][key] == z.tables[n][key]) by {
            if n != child { assert(full::registered(a, n) == full::registered(z, n)); }
        }
    }
    projection_equal(a, z, keys);
}

pub proof fn empty_erasure<V>(a: full::State<V>, n: usize, keys: ISet<Port>)
    requires unambiguous(a), a.tables[n].is_empty(),
    ensures project(a, keys) == project(full::erase(a, n), keys),
{
    let z = full::erase(a, n);
    assert(bindings_equal(a, z)) by {
        assert forall|key: Port, m: usize| owns(a, key, m) == owns(z, key, m)
            && (owns(a, key, m) ==> a.tables[m][key] == z.tables[m][key]) by { }
    }
    assert(unambiguous(z)) by {
        assert forall|key: Port, x: usize, y: usize| owns(z, key, x) && owns(z, key, y) implies x == y by {
            assert(owns(a, key, x)); assert(owns(a, key, y));
        }
    }
    projection_equal(a, z, keys);
}

/// Control/iterator edits do not alter the key observation, even when the phase
/// change changes Active-only publication. This is the distinction in Eq. 47.
pub proof fn lifecycle_edit<V>(a: full::State<V>, n: usize, phase: crate::Phase,
    committed: ISet<crate::Binding>, iterator: Option<nat>, accumulator: Seq<nat>, keys: ISet<Port>)
    requires unambiguous(a), full::registered(a, n),
    ensures project(a, keys) == project(full::edit(a, n, phase, committed, iterator, accumulator), keys),
{
    let z = full::edit(a, n, phase, committed, iterator, accumulator);
    assert(bindings_equal(a, z)) by {
        assert forall|key: Port, m: usize| owns(a, key, m) == owns(z, key, m)
            && (owns(a, key, m) ==> a.tables[m][key] == z.tables[m][key]) by { }
    }
    assert(unambiguous(z)) by {
        assert forall|key: Port, x: usize, y: usize| owns(z, key, x) && owns(z, key, y) implies x == y by {
            assert(owns(a, key, x)); assert(owns(a, key, y));
        }
    }
    projection_equal(a, z, keys);
}

/// A confined table effect can change presence only in its own provision and
/// values only in the union of its dependency and provision declarations.
pub proof fn table_map_footprint<V>(a: full::State<V>, z: full::State<V>, actor: usize, key: Port)
    requires inv::well_formed(a), full::registered(a, actor), inv::table_map(a, z, actor),
    ensures !a.control.fibers[actor].provisions.contains(key)
        ==> project(a, ISet::full()).dom().contains(key) == project(z, ISet::full()).dom().contains(key),
        !a.control.fibers[actor].provisions.contains(key) && !a.control.fibers[actor].dependencies.contains(key)
        && project(a, ISet::full()).dom().contains(key)
            ==> project(a, ISet::full())[key] == project(z, ISet::full())[key],
{
    inv::table_preservation(a, z, actor);
    unique_owner(a); unique_owner(z);
    if !a.control.fibers[actor].provisions.contains(key) {
        assert(!owns(a, key, actor)); assert(!owns(z, key, actor));
        assert forall|n: usize| owns(a, key, n) == owns(z, key, n) by {
            if n != actor && full::registered(a, n) {
                assert(a.tables[n].dom() == z.tables[n].dom());
            }
        }
        if project(a, ISet::full()).dom().contains(key) {
            let n = choose|n: usize| owns(a, key, n);
            assert(n != actor); assert(owns(z, key, n));
            lookup(a, ISet::full(), key, n); lookup(z, ISet::full(), key, n);
            if !a.control.fibers[actor].dependencies.contains(key) {
                assert(a.tables[n][key] == z.tables[n][key]);
            }
        }
        if project(z, ISet::full()).dom().contains(key) {
            let n = choose|n: usize| owns(z, key, n);
            assert(owns(a, key, n));
            lookup(a, ISet::full(), key, n);
        }
    }
}

pub proof fn table_map_observation_frame<V>(a: full::State<V>, z: full::State<V>, actor: usize, keys: ISet<Port>)
    requires inv::well_formed(a), full::registered(a, actor), inv::table_map(a, z, actor),
        keys.disjoint(a.control.fibers[actor].provisions.union(a.control.fibers[actor].dependencies)),
    ensures project(a, keys) == project(z, keys),
{
    restriction(a, keys); restriction(z, keys);
    assert(project(a, keys) =~= project(z, keys)) by {
        assert forall|key: Port| keys.contains(key) implies
            project(a, ISet::full()).dom().contains(key) == project(z, ISet::full()).dom().contains(key)
            && (project(a, ISet::full()).dom().contains(key) ==> project(a, ISet::full())[key] == project(z, ISet::full())[key]) by {
            table_map_footprint(a, z, actor, key);
        }
    }
}

/// Assemble the per-owner relation used by quotient simulation into the paper's
/// single coeffect observation. The control equality fixes provider ownership.
pub proof fn quotient_observation<V>(eq: spec_fn(Port, V, V) -> bool, a: full::State<V>, b: full::State<V>, keys: ISet<Port>)
    requires inv::well_formed(a), crate::quotient::related(eq, a, b),
    ensures observation::context_equal(eq, keys, project(a, ISet::full()), project(b, ISet::full())),
{
    crate::quotient::related_shaped(eq, a, b);
    unique_owner(a); unique_owner(b);
    assert forall|key: Port| keys.contains(key) implies project(a, ISet::full()).dom().contains(key) == project(b, ISet::full()).dom().contains(key) by {
        if project(a, ISet::full()).dom().contains(key) {
            let n = choose|n: usize| owns(a, key, n);
            crate::quotient::table_domains(eq, a, b, n);
            assert(owns(b, key, n));
        }
        if project(b, ISet::full()).dom().contains(key) {
            let n = choose|n: usize| owns(b, key, n);
            crate::quotient::table_domains(eq, a, b, n);
            assert(owns(a, key, n));
        }
    }
    assert forall|key: Port| keys.contains(key) && project(a, ISet::full()).dom().contains(key) implies
        eq(key, project(a, ISet::full())[key], project(b, ISet::full())[key]) by {
        let n = choose|n: usize| owns(a, key, n);
        crate::quotient::table_domains(eq, a, b, n);
        lookup(a, ISet::full(), key, n); lookup(b, ISet::full(), key, n);
        assert(observation::context_equal(eq, ISet::full(), a.tables[n], b.tables[n]));
        assert(ISet::<Port>::full().contains(key));
    }
}

/// Feed the actual registry projection to Definition 30's interpreter. The
/// resulting grammar theorem concerns the services really carried by this
/// State, including unpublished provisions, rather than an unrelated map.
pub proof fn mediated_observation<V, O>(eq: spec_fn(Port, V, V) -> bool,
    program: mediated::Program<Port, V, O>, allowed: mediated::Allowed<Port, V, O>,
    declared: ISet<Port>, provisions: ISet<Port>, observed: ISet<Port>, id: nat,
    a: full::State<V>, b: full::State<V>)
    requires mediated::primitive_theory(eq, allowed), provisions.subset_of(declared),
        mediated::member(program, allowed, declared, provisions, id), mediated::covered(program, observed, id),
        inv::well_formed(a), crate::quotient::related(eq, a, b),
    ensures {
        let left = mediated::run(program(id), project(a, ISet::full()));
        let right = mediated::run(program(id), project(b, ISet::full()));
        &&& left.is_some() == right.is_some()
        &&& (left.is_some() ==> {
            &&& observation::context_equal(eq, observed, left.unwrap().state, right.unwrap().state)
            &&& left.unwrap().next == right.unwrap().next
            &&& (left.unwrap().undo)(left.unwrap().state) == Some(project(a, ISet::full()))
            &&& (right.unwrap().undo)(right.unwrap().state) == Some(project(b, ISet::full()))
        })
    },
{
    quotient_observation(eq, a, b, observed);
    mediated::restricted_admissibility(eq, program, allowed, declared, provisions, observed, id);
}

/// A primitive table update on the actual full state. The owner is explicit;
/// this cannot silently write the same key in a different fiber's table.
pub open spec fn update_slot<V>(s: full::State<V>, n: usize, key: Port, value: Option<V>) -> full::State<V> {
    full::State { control: s.control, effects: s.effects, iterators: s.iterators,
        accumulators: s.accumulators,
        tables: s.tables.insert(n, crate::coeffects::put(s.tables[n], key, value)) }
}

pub proof fn update_slot_confined<V>(a: full::State<V>, actor: usize, n: usize, key: Port, value: Option<V>)
    requires inv::well_formed(a), full::registered(a, actor), full::registered(a, n),
        a.control.fibers[n].provisions.contains(key),
        actor == n || (a.control.fibers[actor].dependencies.contains(key)
            && a.tables[n].dom().contains(key) && value.is_some()),
    ensures inv::table_map(a, update_slot(a, n, key, value), actor), inv::well_formed(update_slot(a, n, key, value)),
{
    let z = update_slot(a, n, key, value);
    assert(a.tables.dom().contains(n));
    assert(a.tables.dom() =~= z.tables.dom());
    assert forall|m: usize| full::registered(a, m) && m != actor implies {
        &&& a.tables[m].dom() == z.tables[m].dom()
        &&& forall|p: Port| a.tables[m].dom().contains(p) && !a.control.fibers[actor].dependencies.contains(p)
            ==> a.tables[m][p] == z.tables[m][p]
    } by {
        if m == n {
            assert(value.is_some());
            assert(a.tables[m].dom() =~= z.tables[m].dom());
            assert forall|p: Port| a.tables[m].dom().contains(p) && !a.control.fibers[actor].dependencies.contains(p)
                implies a.tables[m][p] == z.tables[m][p] by { assert(p != key); }
        }
    }
    assert(z.tables[actor].dom().subset_of(a.control.fibers[actor].provisions)) by {
        assert forall|p: Port| z.tables[actor].dom().contains(p) implies a.control.fibers[actor].provisions.contains(p) by {
            if actor != n || p != key { assert(a.tables[actor].dom().contains(p)); }
        }
    }
    inv::table_preservation(a, z, actor);
}

/// Definition 56's projection square commutes for both a value write and a
/// binding extension/restriction, using the registry's unique declared owner.
pub proof fn update_slot_projection<V>(a: full::State<V>, n: usize, key: Port, value: Option<V>)
    requires inv::well_formed(a), full::registered(a, n), a.control.fibers[n].provisions.contains(key),
    ensures project(update_slot(a, n, key, value), ISet::full())
        == crate::coeffects::put(project(a, ISet::full()), key, value),
{
    update_slot_confined(a, n, n, key, value);
    let z = update_slot(a, n, key, value);
    let desired = crate::coeffects::put(project(a, ISet::full()), key, value);
    unique_owner(a); unique_owner(z);
    assert forall|m: usize| owns(a, key, m) || owns(z, key, m) implies m == n by {
        if owns(a, key, m) { assert(a.control.fibers[m].provisions.contains(key)); }
        if owns(z, key, m) { assert(z.control.fibers[m].provisions.contains(key)); }
    }
    assert(project(z, ISet::full()) =~= desired) by {
        assert forall|p: Port| project(z, ISet::full()).dom().contains(p) == desired.dom().contains(p) by {
            if p == key {
                if value.is_some() { assert(owns(z, key, n)); }
                if project(z, ISet::full()).dom().contains(p) {
                    let m = choose|m: usize| owns(z, p, m);
                    assert(m == n); assert(value.is_some());
                }
            } else {
                if project(z, ISet::full()).dom().contains(p) {
                    let m = choose|m: usize| owns(z, p, m);
                    assert(owns(a, p, m));
                }
                if desired.dom().contains(p) {
                    assert(project(a, ISet::full()).dom().contains(p));
                    let m = choose|m: usize| owns(a, p, m);
                    assert(owns(z, p, m));
                }
            }
        }
        assert forall|p: Port| project(z, ISet::full()).dom().contains(p) implies project(z, ISet::full())[p] == desired[p] by {
            if p == key {
                assert(value.is_some()); lookup(z, ISet::full(), p, n);
            } else {
                let m = choose|m: usize| owns(z, p, m);
                assert(owns(a, p, m));
                lookup(a, ISet::full(), p, m); lookup(z, ISet::full(), p, m);
                assert(a.tables[m][p] == z.tables[m][p]);
            }
        }
    }
}

pub proof fn update_slot_recovery<V>(a: full::State<V>, n: usize, key: Port, value: Option<V>)
    requires a.tables.dom().contains(n),
    ensures update_slot(update_slot(a, n, key, value), n, key, crate::coeffects::get(a.tables[n], key)) == a,
{
    crate::coeffects::update_restore(a.tables[n], key, value);
    assert(a.tables.insert(n, a.tables[n]) =~= a.tables);
    let restored = update_slot(update_slot(a, n, key, value), n, key, crate::coeffects::get(a.tables[n], key));
    assert(restored.tables =~= a.tables);
}

/// An operation stage of the mediated grammar writes its provider's actual
/// full-state table. Its returned value-level inverse restores the full state,
/// and the projected successor is precisely `mediated::run`'s successor.
pub proof fn operation_stage_lift<V, O>(a: full::State<V>, actor: usize, provider: usize, key: Port,
    operation: mediated::Operation<V, O>, select: spec_fn(O) -> Option<nat>)
    requires inv::well_formed(a), full::registered(a, actor), owns(a, key, provider),
        actor == provider || a.control.fibers[actor].dependencies.contains(key),
        operation(a.tables[provider][key]).is_some(),
        (operation(a.tables[provider][key]).unwrap().undo)(operation(a.tables[provider][key]).unwrap().value) == Some(a.tables[provider][key]),
    ensures {
        let y = operation(a.tables[provider][key]).unwrap();
        let z = update_slot(a, provider, key, Some(y.value));
        let projected = mediated::run(mediated::Node::Operation { key, operation, select }, project(a, ISet::full()));
        &&& inv::table_map(a, z, actor) && inv::well_formed(z)
        &&& projected.is_some() && projected.unwrap().state == project(z, ISet::full())
        &&& projected.unwrap().next == select(y.outcome)
        &&& update_slot(z, provider, key, (y.undo)(z.tables[provider][key])) == a
    },
{
    assert(a.control.fibers[provider].provisions.contains(key));
    unique_owner(a); lookup(a, ISet::full(), key, provider);
    let y = operation(a.tables[provider][key]).unwrap();
    update_slot_confined(a, actor, provider, key, Some(y.value));
    update_slot_projection(a, provider, key, Some(y.value));
    update_slot_recovery(a, provider, key, Some(y.value));
}

pub proof fn provision_stage_lift<V, O>(a: full::State<V>, actor: usize, key: Port, value: V, next: Option<nat>)
    requires inv::well_formed(a), full::registered(a, actor), a.control.fibers[actor].provisions.contains(key),
        !a.tables[actor].dom().contains(key),
    ensures {
        let z = update_slot(a, actor, key, Some(value));
        let projected = mediated::run(mediated::Node::<Port, V, O>::Provision { key, value, next }, project(a, ISet::full()));
        &&& inv::table_map(a, z, actor) && inv::well_formed(z)
        &&& projected.is_some() && projected.unwrap().state == project(z, ISet::full())
        &&& projected.unwrap().next == next
        &&& update_slot(z, actor, key, None) == a
    },
{
    unique_owner(a);
    assert(!project(a, ISet::full()).dom().contains(key)) by {
        if project(a, ISet::full()).dom().contains(key) {
            let n = choose|n: usize| owns(a, key, n);
            assert(a.control.fibers[n].provisions.contains(key));
            assert(n == actor);
        }
    }
    update_slot_confined(a, actor, actor, key, Some(value));
    update_slot_projection(a, actor, key, Some(value));
    update_slot_recovery(a, actor, key, Some(value));
}

} // verus!
