//! Full-state deletion with explicit name-observation boundaries.
//!
//! A retired empty entry is invisible to table observations, but may still be
//! read by parent guards or opaque primitives. The contracts below expose those
//! local reads and compose them through actual LIFO restoration and all nine
//! rules. They do not assume a lifecycle simulation or the deleted execution.
#[cfg(verus_keep_ghost)]
use crate::{preservation as p, refinement as c, semantics as s, Binding, Phase};
use vstd::prelude::*;

verus! {

/// Equality of the entire retained entry, including interpreter identities.
pub open spec fn retained_entry<V>(a:s::State<V>,z:s::State<V>,removed:usize) -> bool {
    &&& s::registered(a,removed) && s::registered(z,removed)
    &&& a.control.fibers[removed] == z.control.fibers[removed]
    &&& a.tables.dom().contains(removed) && z.tables.dom().contains(removed)
    &&& a.effects.dom().contains(removed) && z.effects.dom().contains(removed)
    &&& a.iterators.dom().contains(removed) && z.iterators.dom().contains(removed)
    &&& a.accumulators.dom().contains(removed) && z.accumulators.dom().contains(removed)
    &&& a.tables[removed] == z.tables[removed]
    &&& a.effects[removed] == z.effects[removed]
    &&& a.iterators[removed] == z.iterators[removed]
    &&& a.accumulators[removed] == z.accumulators[removed]
}

pub proof fn erase_shaped<V>(a:s::State<V>,removed:usize)
    requires s::shaped(a),
    ensures s::shaped(s::erase(a,removed)),
{
    assert forall|n:usize| s::registered(s::erase(a,removed),n) implies {
        &&& s::erase(a,removed).tables[n].dom().subset_of(s::erase(a,removed).control.fibers[n].provisions)
        &&& (s::erase(a,removed).control.fibers[n].phase == Phase::Inactive ==> s::erase(a,removed).iterators[n].is_none()
            && s::erase(a,removed).accumulators[n].len() == 0 && s::erase(a,removed).control.fibers[n].committed.is_empty())
        &&& (s::erase(a,removed).control.fibers[n].phase == Phase::Loading ==> s::erase(a,removed).iterators[n].is_some())
        &&& (s::erase(a,removed).control.fibers[n].phase == Phase::Active || s::erase(a,removed).control.fibers[n].phase == Phase::Unloading
            ==> s::erase(a,removed).iterators[n].is_none())
    } by { assert(s::registered(a,n)); }
}

pub proof fn erase_observation<V>(a:s::State<V>,removed:usize)
    requires s::vestigial(a,removed),
    ensures s::same_tables(a,s::erase(a,removed)),
{
    assert forall|n:usize,port:crate::Port| #[trigger] s::lookup(a,n,port) == s::lookup(s::erase(a,removed),n,port) by {
        if n == removed { assert(a.tables[n].is_empty()); }
    }
}

pub proof fn erase_edit<V>(a:s::State<V>,removed:usize,actor:usize,phase:Phase,
    view:ISet<Binding>,iterator:Option<nat>,accumulator:Seq<nat>)
    requires actor != removed,
    ensures s::erase(s::edit(a,actor,phase,view,iterator,accumulator),removed)
        == s::edit(s::erase(a,removed),actor,phase,view,iterator,accumulator),
{
    assert(a.control.fibers.insert(actor,s::edit(a,actor,phase,view,iterator,accumulator).control.fibers[actor]).remove(removed)
        =~= s::edit(s::erase(a,removed),actor,phase,view,iterator,accumulator).control.fibers);
    assert(a.iterators.insert(actor,iterator).remove(removed) =~= a.iterators.remove(removed).insert(actor,iterator));
    assert(a.accumulators.insert(actor,accumulator).remove(removed) =~= a.accumulators.remove(removed).insert(actor,accumulator));
}

/// At one iterator call, erasure preserves the actual inverse and continuation.
/// This is a primitive read-footprint law; the full step is not a premise.
pub open spec fn iteration_erases<V>(model:s::Model<V>,a:s::State<V>,actor:usize,removed:usize) -> bool {
    let y = (model.iterate)(actor,a.iterators[actor].unwrap(),a);
    let x = (model.iterate)(actor,a.iterators[actor].unwrap(),s::erase(a,removed));
    y.inverse == x.inverse && y.next == x.next && s::erase(y.state,removed) == x.state
}

/// Only actual restoration positions are constrained. In particular, this
/// does not require every opaque inverse to accept every absent child name.
pub open spec fn inverse_erases<V>(model:s::Model<V>,tokens:Seq<nat>,a:s::State<V>,removed:usize) -> bool
    decreases tokens.len(),
{
    tokens.len() == 0 || (s::erase((model.undo)(tokens.last(),a),removed)
        == (model.undo)(tokens.last(),s::erase(a,removed))
        && inverse_erases(model,tokens.drop_last(),(model.undo)(tokens.last(),a),removed))
}

pub proof fn restore_erases<V>(model:s::Model<V>,tokens:Seq<nat>,a:s::State<V>,removed:usize)
    requires inverse_erases(model,tokens,a,removed),
    ensures s::erase(s::restore(model,tokens,a),removed)
        == s::restore(model,tokens,s::erase(a,removed)),
    decreases tokens.len(),
{
    if tokens.len() > 0 { restore_erases(model,tokens.drop_last(),(model.undo)(tokens.last(),a),removed); }
}

pub proof fn erase_absent<V>(a:s::State<V>,removed:usize)
    requires s::shaped(a),!s::registered(a,removed),
    ensures s::erase(a,removed) == a,
{
    assert(a.control.fibers.remove(removed) =~= a.control.fibers);
    assert(a.tables.remove(removed) =~= a.tables);
    assert(a.effects.remove(removed) =~= a.effects);
    assert(a.iterators.remove(removed) =~= a.iterators);
    assert(a.accumulators.remove(removed) =~= a.accumulators);
}

/// Forward simulation needs only the parent read restriction for insertion;
/// original freshness/provision/no-child guards imply their erased versions.
pub open spec fn step_reads_erase<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,removed:usize) -> bool {
    &&& actor != removed
    &&& (rule == c::Rule::Insert ==> z.control.fibers[actor].parent != Some(removed))
    &&& (rule == c::Rule::Iter || rule == c::Rule::Finish
        || (rule == c::Rule::Divert && z != s::edit(a,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]))
        ==> iteration_erases(model,a,actor,removed))
    &&& (rule == c::Rule::Unload ==> inverse_erases(model,a.accumulators[actor],a,removed))
}

/// Corrected forward Lemma 62, including actual table updates, child creation,
/// both diversion branches, and composed inverse execution. No provision
/// totality or assumptions about successor rule applicability are needed.
#[verifier::rlimit(15)]
pub proof fn full_step_erases<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,removed:usize)
    requires s::shaped(a),(s::vestigial(a,removed) || !s::registered(a,removed)),s::step(model,a,z,actor,rule),
        step_reads_erase(model,a,z,actor,rule,removed),
    ensures s::step(model,s::erase(a,removed),s::erase(z,removed),actor,rule),
{
    let left = s::erase(a,removed);
    let right = s::erase(z,removed);
    if !s::registered(a,removed) { erase_absent(a,removed); }
    else if s::registered(a,actor) { s::vestigial_observations(a,removed,actor,a.control.fibers[actor].committed); }
    match rule {
        c::Rule::Insert => {
            if s::registered(a,removed) { s::vestigial_insert_forward(a.control,z.control,removed,actor); }
            else {
                assert(!s::registered(z,removed));
                erase_absent(z,removed);
            }
            erase_shaped(z,removed);
            assert(s::auxiliary_frame(left,right,actor)) by {
                assert forall|m:usize| m != actor && s::registered(left,m) implies right.tables[m] == left.tables[m]
                    && right.effects[m] == left.effects[m] && right.iterators[m] == left.iterators[m]
                    && right.accumulators[m] == left.accumulators[m] by { assert(s::registered(a,m)); }
            }
            assert(s::step(model,left,right,actor,rule));
        },
        c::Rule::Retire | c::Rule::Remove => {
            assert(c::step(a.control,z.control,actor,rule));
            assert(left.control.fibers[actor] == a.control.fibers[actor]);
            if rule == c::Rule::Retire { assert(right.control.fibers[actor] == z.control.fibers[actor]); }
            assert(c::frame(left.control,right.control,actor)) by {
                assert forall|m:usize| m != actor implies c::registered(left.control,m) == c::registered(right.control,m)
                    && (c::registered(left.control,m) ==> left.control.fibers[m] == right.control.fibers[m]) by {
                    if m != removed { assert(c::registered(a.control,m) == c::registered(z.control,m)); }
                }
            }
            if rule == c::Rule::Remove {
                assert forall|m:usize| s::registered(left,m) implies left.control.fibers[m].parent != Some(actor) by { assert(s::registered(a,m)); }
                assert(a.tables.remove(actor).remove(removed) =~= a.tables.remove(removed).remove(actor));
                assert(a.effects.remove(actor).remove(removed) =~= a.effects.remove(removed).remove(actor));
                assert(a.iterators.remove(actor).remove(removed) =~= a.iterators.remove(removed).remove(actor));
                assert(a.accumulators.remove(actor).remove(removed) =~= a.accumulators.remove(removed).remove(actor));
            }
            if rule == c::Rule::Retire {
                assert(c::registered(left.control,actor));
                assert(c::registered(right.control,actor));
                assert(c::interface_same(left.control.fibers[actor],right.control.fibers[actor]));
                assert(right.control.fibers[actor].retired);
                assert(right.control.fibers[actor].phase == left.control.fibers[actor].phase);
                assert(right.control.fibers[actor].committed == left.control.fibers[actor].committed);
                assert(c::step(left.control,right.control,actor,c::Rule::Retire));
            } else {
                assert(c::registered(left.control,actor));
                assert(!c::registered(right.control,actor));
                assert(left.control.fibers[actor].retired);
                assert(left.control.fibers[actor].phase == Phase::Inactive);
                assert(left.control.fibers[actor].committed.is_empty());
                assert forall|m:usize| c::registered(left.control,m) implies left.control.fibers[m].parent != Some(actor) by { assert(c::registered(a.control,m)); }
                assert(c::step(left.control,right.control,actor,c::Rule::Remove));
            }
            assert(s::step(model,left,right,actor,rule));
        },
        c::Rule::Begin => {
            if s::registered(a,removed) { s::vestigial_observations(a,removed,actor,z.control.fibers[actor].committed); }
            erase_edit(a,removed,actor,Phase::Loading,z.control.fibers[actor].committed,Some(a.effects[actor]),Seq::empty());
            assert(s::step(model,left,right,actor,rule));
        },
        c::Rule::Iter | c::Rule::Finish | c::Rule::Divert => {
            let y = (model.iterate)(actor,a.iterators[actor].unwrap(),a);
            if rule == c::Rule::Divert && z == s::edit(a,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]) {
                erase_edit(a,removed,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]);
            } else {
                let phase = if rule == c::Rule::Iter { Phase::Loading } else if rule == c::Rule::Finish { Phase::Active } else { Phase::Unloading };
                let next = if rule == c::Rule::Iter { y.next } else { None };
                erase_edit(y.state,removed,actor,phase,a.control.fibers[actor].committed,next,a.accumulators[actor].push(y.inverse));
            }
            assert(s::step(model,left,right,actor,rule));
        },
        c::Rule::Leave => { erase_edit(a,removed,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]); },
        c::Rule::Unload => {
            restore_erases(model,a.accumulators[actor],a,removed);
            erase_edit(s::restore(model,a.accumulators[actor],a),removed,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
            assert(s::step(model,left,right,actor,rule));
        },
        _ => {},
    }
}


/// Confinement makes an empty foreign table and its entire entry immutable.
pub proof fn table_preserves_vestigial<V>(a:s::State<V>,z:s::State<V>,actor:usize,removed:usize)
    requires s::shaped(a),s::vestigial(a,removed),actor != removed,p::table_map(a,z,actor),
    ensures s::vestigial(z,removed),retained_entry(a,z,removed),
{
    assert(a.tables[removed].dom() == z.tables[removed].dom());
    assert(a.tables[removed] =~= z.tables[removed]);
    assert forall|m:usize| s::registered(z,m) implies z.control.fibers[m].parent != Some(removed) by { assert(s::registered(a,m)); }
}

pub proof fn forward_preserves_vestigial<V>(a:s::State<V>,z:s::State<V>,actor:usize,removed:usize)
    requires p::well_formed(a),s::registered(a,actor),s::vestigial(a,removed),actor != removed,p::forward_map(a,z,actor),
    ensures p::well_formed(z),s::vestigial(z,removed),retained_entry(a,z,removed),s::registered(z,actor),
{
    p::forward_preservation(a,z,actor);
    if p::table_map(a,z,actor) { table_preserves_vestigial(a,z,actor,removed); }
    else {
        let child = choose|child:usize| p::child_map(a,z,actor,child);
        assert(child != removed);
        assert forall|m:usize| s::registered(z,m) implies z.control.fibers[m].parent != Some(removed) by {
            if m != child { assert(s::registered(a,m)); assert(a.control.fibers[m] == z.control.fibers[m]); }
        }
    }
}

pub proof fn inverse_preserves_vestigial<V>(a:s::State<V>,z:s::State<V>,actor:usize,removed:usize)
    requires p::well_formed(a),s::registered(a,actor),s::vestigial(a,removed),actor != removed,p::inverse_map(a,z,actor),
    ensures p::well_formed(z),s::vestigial(z,removed),retained_entry(a,z,removed),s::registered(z,actor),
{
    p::inverse_preservation(a,z,actor);
    if p::table_map(a,z,actor) { table_preserves_vestigial(a,z,actor,removed); }
    else {
        let child = choose|child:usize| s::child_retire(a,z,child);
        if child == removed { assert(a.control.fibers[removed] == z.control.fibers[removed]); }
        assert forall|m:usize| s::registered(z,m) implies z.control.fibers[m].parent != Some(removed) by {
            assert(s::registered(a,m));
            if m != child { assert(a.control.fibers[m] == z.control.fibers[m]); }
        }
    }
}

pub proof fn restore_preserves_vestigial<V>(model:s::Model<V>,tokens:Seq<nat>,a:s::State<V>,actor:usize,removed:usize)
    requires p::well_formed(a),s::registered(a,actor),s::vestigial(a,removed),actor != removed,
        p::admissible_restore(model,tokens,a,actor),
    ensures p::well_formed(s::restore(model,tokens,a)),s::vestigial(s::restore(model,tokens,a),removed),
        retained_entry(a,s::restore(model,tokens,a),removed),s::registered(s::restore(model,tokens,a),actor),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        let z = (model.undo)(tokens.last(),a);
        inverse_preserves_vestigial(a,z,actor,removed);
        restore_preserves_vestigial(model,tokens.drop_last(),z,actor,removed);
    }
}

pub proof fn edit_preserves_vestigial<V>(a:s::State<V>,removed:usize,actor:usize,phase:Phase,
    view:ISet<Binding>,iterator:Option<nat>,accumulator:Seq<nat>)
    requires s::shaped(a),s::vestigial(a,removed),actor != removed,s::registered(a,actor),
    ensures s::vestigial(s::edit(a,actor,phase,view,iterator,accumulator),removed),
        retained_entry(a,s::edit(a,actor,phase,view,iterator,accumulator),removed),
{
    let z = s::edit(a,actor,phase,view,iterator,accumulator);
    assert forall|m:usize| s::registered(z,m) implies z.control.fibers[m].parent != Some(removed) by {
        assert(s::registered(a,m));
    }
}

/// The survival invariant is derived from primitive footprints, not supplied
/// at every trace position. Child creation is safe because its parent is actor.
#[verifier::rlimit(15)]
pub proof fn step_preserves_vestigial<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,removed:usize)
    requires p::well_formed(a),s::vestigial(a,removed),s::step(model,a,z,actor,rule),
        p::admissible_step(model,a,z,actor,rule),actor != removed,
        rule == c::Rule::Insert ==> z.control.fibers[actor].parent != Some(removed),
    ensures p::well_formed(z),s::vestigial(z,removed),retained_entry(a,z,removed),
{
    p::full_preservation(model,a,z,actor,rule);
    match rule {
        c::Rule::Insert | c::Rule::Retire | c::Rule::Remove => {
            assert forall|m:usize| s::registered(z,m) implies z.control.fibers[m].parent != Some(removed) by {
                if m != actor { assert(s::registered(a,m)); assert(a.control.fibers[m] == z.control.fibers[m]); }
                else if rule != c::Rule::Insert { assert(s::registered(a,m)); }
            }
        },
        c::Rule::Begin => { edit_preserves_vestigial(a,removed,actor,Phase::Loading,z.control.fibers[actor].committed,Some(a.effects[actor]),Seq::empty()); },
        c::Rule::Iter | c::Rule::Finish | c::Rule::Divert => {
            let y = (model.iterate)(actor,a.iterators[actor].unwrap(),a);
            if rule == c::Rule::Divert && z == s::edit(a,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]) {
                edit_preserves_vestigial(a,removed,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]);
            } else {
                forward_preserves_vestigial(a,y.state,actor,removed);
                let phase = if rule == c::Rule::Iter { Phase::Loading } else if rule == c::Rule::Finish { Phase::Active } else { Phase::Unloading };
                let next = if rule == c::Rule::Iter { y.next } else { None };
                edit_preserves_vestigial(y.state,removed,actor,phase,a.control.fibers[actor].committed,next,a.accumulators[actor].push(y.inverse));
            }
        },
        c::Rule::Leave => { edit_preserves_vestigial(a,removed,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]); },
        c::Rule::Unload => {
            restore_preserves_vestigial(model,a.accumulators[actor],a,actor,removed);
            edit_preserves_vestigial(s::restore(model,a.accumulators[actor],a),removed,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
        },
        _ => {},
    }
}


/// An erased name cannot be reallocated by a primitive that satisfies the
/// same erasure read law: on an already absent input the law is ordinary
/// equality. This is the explicit freshness boundary for suffix replay.
#[verifier::rlimit(15)]
pub proof fn step_preserves_absence<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,removed:usize)
    requires p::well_formed(a),!s::registered(a,removed),s::step(model,a,z,actor,rule),
        p::admissible_step(model,a,z,actor,rule),step_reads_erase(model,a,z,actor,rule,removed),
    ensures !s::registered(z,removed),p::well_formed(z),
{
    p::full_preservation(model,a,z,actor,rule);
    erase_absent(a,removed);
    match rule {
        c::Rule::Insert | c::Rule::Retire | c::Rule::Remove => { assert(c::frame(a.control,z.control,actor)); },
        c::Rule::Begin | c::Rule::Leave => {},
        c::Rule::Iter | c::Rule::Finish | c::Rule::Divert => {
            let y = (model.iterate)(actor,a.iterators[actor].unwrap(),a);
            if !(rule == c::Rule::Divert && z == s::edit(a,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor])) {
                assert(s::erase(y.state,removed) == y.state);
                assert(!s::registered(y.state,removed));
            }
        },
        c::Rule::Unload => {
            restore_erases(model,a.accumulators[actor],a,removed);
            assert(!s::registered(s::restore(model,a.accumulators[actor],a),removed));
        },
        _ => {},
    }
}

/// The only legal actions on a vestigial entry are idempotent retirement and
/// removal. Their complete payload outside that entry is unchanged.
pub proof fn vestigial_step_is_silent<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,removed:usize,rule:c::Rule)
    requires s::shaped(a),s::vestigial(a,removed),s::step(model,a,z,removed,rule),
    ensures rule == c::Rule::Retire || rule == c::Rule::Remove,
        s::erase(a,removed) == s::erase(z,removed),
        s::vestigial(z,removed) || !s::registered(z,removed),
{
    assert(!s::coherent(a,removed));
    if rule == c::Rule::Retire || rule == c::Rule::Remove {
        assert(a.control.fibers.remove(removed) =~= z.control.fibers.remove(removed)) by {
            assert forall|m:usize| a.control.fibers.remove(removed).dom().contains(m)
                == z.control.fibers.remove(removed).dom().contains(m) by {
                if m != removed { assert(s::registered(a,m) == s::registered(z,m)); }
            }
            assert forall|m:usize| a.control.fibers.remove(removed).dom().contains(m)
                implies a.control.fibers.remove(removed)[m] == z.control.fibers.remove(removed)[m] by {
                assert(m != removed);
                assert(s::registered(a,m));
                assert(c::frame(a.control,z.control,removed));
                assert(a.control.fibers[m] == z.control.fibers[m]);
            }
        }
        if rule == c::Rule::Retire {
            assert forall|m:usize| s::registered(z,m) implies z.control.fibers[m].parent != Some(removed) by {
                assert(s::registered(a,m));
                if m != removed { assert(a.control.fibers[m] == z.control.fibers[m]); }
            }
        } else {
            assert(a.tables.remove(removed).remove(removed) =~= a.tables.remove(removed));
            assert(a.effects.remove(removed).remove(removed) =~= a.effects.remove(removed));
            assert(a.iterators.remove(removed).remove(removed) =~= a.iterators.remove(removed));
            assert(a.accumulators.remove(removed).remove(removed) =~= a.accumulators.remove(removed));
        }
    }
}

pub open spec fn suffix_admissible<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,removed:usize) -> bool {
    &&& p::execution(model,states,labels)
    &&& forall|i:int| 0 <= i < labels.len() ==> if labels[i].0 == removed {
        labels[i].1 != c::Rule::Insert
    } else { step_reads_erase(model,states[i],states[i+1],labels[i].0,labels[i].1,removed) }
}

pub open spec fn surviving_labels(labels:Seq<(usize,c::Rule)>,removed:usize) -> Seq<(usize,c::Rule)>
    decreases labels.len(),
{
    if labels.len() == 0 { Seq::empty() }
    else {
        let prefix = surviving_labels(labels.drop_last(),removed);
        if labels.last().0 == removed { prefix } else { prefix.push(labels.last()) }
    }
}

/// This construction drops exactly the steps acting on the erased name and
/// keeps the original successor with that entry erased at every retained step.
pub open spec fn surviving_states<V>(states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,removed:usize) -> Seq<s::State<V>>
    recommends states.len() == labels.len()+1,
    decreases labels.len(),
{
    if labels.len() == 0 { seq![s::erase(states.first(),removed)] }
    else {
        let prefix = surviving_states(states.drop_last(),labels.drop_last(),removed);
        if labels.last().0 == removed { prefix } else { prefix.push(s::erase(states.last(),removed)) }
    }
}

/// Corrected full-state suffix of Lemma 79. The original suffix is the only
/// execution premise; the reduced suffix is constructed and proved legal.
/// Vestigiality is derived along the trace and may become permanent absence.
#[verifier::rlimit(40)]
pub proof fn suffix_deletion<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,removed:usize)
    requires suffix_admissible(model,states,labels,removed),p::well_formed(states.first()),
        s::vestigial(states.first(),removed) || !s::registered(states.first(),removed),
    ensures {
        let out = surviving_states(states,labels,removed);
        let kept = surviving_labels(labels,removed);
        &&& s::execution(model,out,kept)
        &&& out.first() == s::erase(states.first(),removed)
        &&& out.last() == s::erase(states.last(),removed)
        &&& s::same_tables(states.last(),out.last())
        &&& p::well_formed(states.last())
        &&& (s::vestigial(states.last(),removed) || !s::registered(states.last(),removed))
    },
    decreases labels.len(),
{
    let out = surviving_states(states,labels,removed);
    let kept = surviving_labels(labels,removed);
    if labels.len() == 0 {
        assert(states.first() == states.last());
        if s::vestigial(states.last(),removed) { erase_observation(states.last(),removed); }
        else { erase_absent(states.last(),removed); }
        assert forall|i:int| 0 <= i < kept.len() implies s::step(model,out[i],out[i+1],kept[i].0,kept[i].1) by { }
    } else {
        let previous = states.drop_last();
        let prefix_labels = labels.drop_last();
        assert(suffix_admissible(model,previous,prefix_labels,removed)) by {
            assert forall|i:int| 0 <= i < prefix_labels.len() implies
                s::step(model,previous[i],previous[i+1],prefix_labels[i].0,prefix_labels[i].1)
                    && p::admissible_step(model,previous[i],previous[i+1],prefix_labels[i].0,prefix_labels[i].1) by { }
            assert forall|i:int| 0 <= i < prefix_labels.len() implies if prefix_labels[i].0 == removed {
                prefix_labels[i].1 != c::Rule::Insert
            } else { step_reads_erase(model,previous[i],previous[i+1],prefix_labels[i].0,prefix_labels[i].1,removed) } by { }
        }
        suffix_deletion(model,previous,prefix_labels,removed);
        let prefix = surviving_states(previous,prefix_labels,removed);
        let prefix_kept = surviving_labels(prefix_labels,removed);
        let a = previous.last();
        let z = states.last();
        let actor = labels.last().0;
        let rule = labels.last().1;
        assert(s::step(model,a,z,actor,rule));
        assert(p::admissible_step(model,a,z,actor,rule));
        p::full_preservation(model,a,z,actor,rule);
        if actor == removed {
            assert(rule != c::Rule::Insert);
            assert(s::registered(a,removed));
            vestigial_step_is_silent(model,a,z,removed,rule);
        } else {
            assert(step_reads_erase(model,a,z,actor,rule,removed));
            full_step_erases(model,a,z,actor,rule,removed);
            if s::vestigial(a,removed) { step_preserves_vestigial(model,a,z,actor,rule,removed); }
            else { step_preserves_absence(model,a,z,actor,rule,removed); }
            assert(out.len() == kept.len()+1);
            assert forall|i:int| 0 <= i < kept.len() implies s::step(model,out[i],out[i+1],kept[i].0,kept[i].1) by {
                if i < prefix_kept.len() {
                    assert(out[i] == prefix[i]); assert(out[i+1] == prefix[i+1]); assert(kept[i] == prefix_kept[i]);
                } else { assert(i == prefix_kept.len()); assert(out[i] == prefix.last()); }
            }
        }
        assert(out.last() == s::erase(z,removed));
        if s::vestigial(z,removed) { erase_observation(z,removed); }
        else { erase_absent(z,removed); }
    }
}


/// Concrete Definition 52 retirement commutes with deleting any other name.
/// Deleting the inverse's own child instead needs the retention protocol.
pub proof fn child_retirement_erases<V>(a:s::State<V>,child:usize,removed:usize)
    requires child != removed,
    ensures s::erase(s::with_control(a,crate::global::retire_fiber(a.control,child)),removed)
        == s::with_control(s::erase(a,removed),crate::global::retire_fiber(s::erase(a,removed).control,child)),
{
    let z = s::with_control(a,crate::global::retire_fiber(a.control,child));
    assert(z.control.fibers.remove(removed)
        =~= crate::global::retire_fiber(s::erase(a,removed).control,child).fibers);
}

pub proof fn map_erasure_injective<K,V>(a:IMap<K,V>,z:IMap<K,V>,removed:K)
    requires a.dom().contains(removed),z.dom().contains(removed),a[removed] == z[removed],
        a.remove(removed) == z.remove(removed),
    ensures a == z,
{
    assert(a =~= z) by {
        assert forall|k:K| a.dom().contains(k) == z.dom().contains(k) by {
            if k != removed {
                assert(a.remove(removed).dom().contains(k) == a.dom().contains(k));
                assert(z.remove(removed).dom().contains(k) == z.dom().contains(k));
                assert(a.remove(removed).dom().contains(k) == z.remove(removed).dom().contains(k));
            }
        }
        assert forall|k:K| a.dom().contains(k) implies a[k] == z[k] by {
            if k != removed {
                assert(a.remove(removed).dom().contains(k));
                assert(z.remove(removed).dom().contains(k));
                assert(a.remove(removed)[k] == a[k]);
                assert(z.remove(removed)[k] == z[k]);
                assert(a.remove(removed)[k] == z.remove(removed)[k]);
            }
        }
    }
}

pub proof fn state_erasure_injective<V>(a:s::State<V>,z:s::State<V>,removed:usize)
    requires retained_entry(a,z,removed),s::erase(a,removed) == s::erase(z,removed),
    ensures a == z,
{
    map_erasure_injective(a.control.fibers,z.control.fibers,removed);
    map_erasure_injective(a.tables,z.tables,removed);
    map_erasure_injective(a.effects,z.effects,removed);
    map_erasure_injective(a.iterators,z.iterators,removed);
    map_erasure_injective(a.accumulators,z.accumulators,removed);
}

/// Primitive contracts needed in the converse direction. The control edit
/// cannot hide a modification of the retained entry by an opaque iterator.
pub open spec fn converse_primitives<V>(model:s::Model<V>,a:s::State<V>,actor:usize,rule:c::Rule,removed:usize) -> bool {
    &&& (rule == c::Rule::Iter || rule == c::Rule::Finish || rule == c::Rule::Divert ==> {
        let y = (model.iterate)(actor,a.iterators[actor].unwrap(),a);
        p::forward_map(a,y.state,actor) && iteration_erases(model,a,actor,removed)
    })
    &&& (rule == c::Rule::Unload ==> p::admissible_restore(model,a.accumulators[actor],a,actor)
        && inverse_erases(model,a.accumulators[actor],a,removed))
}

/// Corrected converse of full Lemma 62. The additional parent-removal and
/// insertion-name/provision reads are precisely the explicit control boundary.
#[verifier::rlimit(30)]
pub proof fn full_step_lifts<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,removed:usize)
    requires p::well_formed(a),s::shaped(z),s::vestigial(a,removed),retained_entry(a,z,removed),
        p::erasure_compatible(a.control,z.control,removed,actor,rule),
        converse_primitives(model,a,actor,rule,removed),
        s::step(model,s::erase(a,removed),s::erase(z,removed),actor,rule),
    ensures s::step(model,a,z,actor,rule),
{
    let left = s::erase(a,removed);
    let right = s::erase(z,removed);
    assert(a.control.fibers[removed].committed.is_empty());
    assert forall|m:usize| c::registered(a.control,m) implies a.control.fibers[m].parent != Some(removed) by { assert(s::registered(a,m)); }
    assert(p::vestigial(a.control,removed));
    if s::registered(a,actor) { s::vestigial_observations(a,removed,actor,a.control.fibers[actor].committed); }
    match rule {
        c::Rule::Insert => {
            p::vestigial_control_bisimulation(a.control,z.control,removed,actor,rule);
            assert(s::auxiliary_frame(a,z,actor)) by {
                assert forall|m:usize| m != actor && s::registered(a,m) implies z.tables[m] == a.tables[m]
                    && z.effects[m] == a.effects[m] && z.iterators[m] == a.iterators[m]
                    && z.accumulators[m] == a.accumulators[m] by {
                    if m != removed { assert(s::registered(left,m)); }
                }
            }
        },
        c::Rule::Retire => {
            p::vestigial_control_bisimulation(a.control,z.control,removed,actor,rule);
            map_erasure_injective(a.tables,z.tables,removed);
            map_erasure_injective(a.effects,z.effects,removed);
            map_erasure_injective(a.iterators,z.iterators,removed);
            map_erasure_injective(a.accumulators,z.accumulators,removed);
        },
        c::Rule::Remove => {
            p::vestigial_control_bisimulation(a.control,z.control,removed,actor,rule);
            assert(a.tables.remove(actor).remove(removed) =~= a.tables.remove(removed).remove(actor));
            assert(a.effects.remove(actor).remove(removed) =~= a.effects.remove(removed).remove(actor));
            assert(a.iterators.remove(actor).remove(removed) =~= a.iterators.remove(removed).remove(actor));
            assert(a.accumulators.remove(actor).remove(removed) =~= a.accumulators.remove(removed).remove(actor));
            map_erasure_injective(a.tables.remove(actor),z.tables,removed);
            map_erasure_injective(a.effects.remove(actor),z.effects,removed);
            map_erasure_injective(a.iterators.remove(actor),z.iterators,removed);
            map_erasure_injective(a.accumulators.remove(actor),z.accumulators,removed);
        },
        c::Rule::Begin => {
            let view = z.control.fibers[actor].committed;
            s::vestigial_observations(a,removed,actor,view);
            let b = s::edit(a,actor,Phase::Loading,view,Some(a.effects[actor]),Seq::empty());
            erase_edit(a,removed,actor,Phase::Loading,view,Some(a.effects[actor]),Seq::empty());
            assert(retained_entry(b,z,removed));
            state_erasure_injective(b,z,removed);
        },
        c::Rule::Iter | c::Rule::Finish | c::Rule::Divert => {
            let y = (model.iterate)(actor,a.iterators[actor].unwrap(),a);
            let abort = s::edit(a,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]);
            erase_edit(a,removed,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]);
            if rule == c::Rule::Divert && right == s::erase(abort,removed) {
                assert(retained_entry(abort,z,removed));
                state_erasure_injective(abort,z,removed);
            } else {
                forward_preserves_vestigial(a,y.state,actor,removed);
                let phase = if rule == c::Rule::Iter { Phase::Loading } else if rule == c::Rule::Finish { Phase::Active } else { Phase::Unloading };
                let next = if rule == c::Rule::Iter { y.next } else { None };
                let b = s::edit(y.state,actor,phase,a.control.fibers[actor].committed,next,a.accumulators[actor].push(y.inverse));
                erase_edit(y.state,removed,actor,phase,a.control.fibers[actor].committed,next,a.accumulators[actor].push(y.inverse));
                assert(retained_entry(b,z,removed));
                state_erasure_injective(b,z,removed);
            }
        },
        c::Rule::Leave => {
            let b = s::edit(a,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]);
            erase_edit(a,removed,actor,Phase::Unloading,a.control.fibers[actor].committed,None,a.accumulators[actor]);
            assert(retained_entry(b,z,removed));
            state_erasure_injective(b,z,removed);
        },
        c::Rule::Unload => {
            restore_erases(model,a.accumulators[actor],a,removed);
            restore_preserves_vestigial(model,a.accumulators[actor],a,actor,removed);
            let b = s::edit(s::restore(model,a.accumulators[actor],a),actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
            erase_edit(s::restore(model,a.accumulators[actor],a),removed,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
            assert(retained_entry(b,z,removed));
            state_erasure_injective(b,z,removed);
        },
        _ => {},
    }
}

pub proof fn full_step_bisimulation<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,removed:usize)
    requires p::well_formed(a),s::shaped(z),s::vestigial(a,removed),retained_entry(a,z,removed),
        p::erasure_compatible(a.control,z.control,removed,actor,rule),
        converse_primitives(model,a,actor,rule,removed),
    ensures s::step(model,a,z,actor,rule) == s::step(model,s::erase(a,removed),s::erase(z,removed),actor,rule),
{
    if s::step(model,a,z,actor,rule) { full_step_erases(model,a,z,actor,rule,removed); }
    else if s::step(model,s::erase(a,removed),s::erase(z,removed),actor,rule) { full_step_lifts(model,a,z,actor,rule,removed); }
}


/// A closed creator episode whose never-activated child acquires an external
/// descendant. This input is permitted by the paper's non-root O-Insert.
pub open spec fn deletion_counterexample_states() -> Seq<s::State<u64>> {
    let a4 = crate::paper_counterexamples::descendant_inserted();
    let a5 = s::with_control(a4,crate::global::retire_fiber(a4.control,2));
    let a6 = s::with_control(a5,crate::global::retire_fiber(a5.control,0));
    let a7 = s::edit(a6,0,Phase::Unloading,ISet::empty(),None,seq![1nat]);
    let restored = (crate::paper_counterexamples::creation_model().undo)(1,a7);
    let a8 = s::edit(restored,0,Phase::Inactive,ISet::empty(),None,Seq::empty());
    seq![s::empty_state::<u64>(),crate::paper_counterexamples::creator_inserted(),
        crate::paper_counterexamples::creator_loading(),crate::paper_counterexamples::creator_finished(),
        a4,a5,a6,a7,a8]
}

pub open spec fn deletion_counterexample_labels() -> Seq<(usize,c::Rule)> {
    seq![(0usize,c::Rule::Insert),(0usize,c::Rule::Begin),(0usize,c::Rule::Finish),
        (2usize,c::Rule::Insert),(2usize,c::Rule::Retire),(0usize,c::Rule::Retire),
        (0usize,c::Rule::Leave),(0usize,c::Rule::Unload)]
}

/// Printed Lemma 79 has a missing name-read hypothesis. All eight transitions
/// are actual full rules, including the child birth inside Finish and the
/// actual child-retire inverse inside Unload. The creator has one closed
/// episode [2,7]; no other fiber ever has an episode; all provisions are empty
/// (therefore total), and the endpoint is quiet. Child 1 is not vestigial,
/// because the permitted external Insert(2,parent=1) retained a descendant.
#[verifier::rlimit(35)]
pub proof fn deletion_counterexample_quiet()
    ensures p::execution(crate::paper_counterexamples::creation_model(),deletion_counterexample_states(),deletion_counterexample_labels()),
        s::reaches(crate::paper_counterexamples::creation_model(),s::empty_state::<u64>(),deletion_counterexample_states().last(),8),
        p::well_formed(deletion_counterexample_states().last()),s::quiet(deletion_counterexample_states().last()),
        s::total_active(deletion_counterexample_states().last()),
        forall|i:int,n:usize| 0 <= i < deletion_counterexample_states().len() && s::registered(deletion_counterexample_states()[i],n)
            ==> deletion_counterexample_states()[i].control.fibers[n].provisions.is_empty(),
        forall|i:int| 2 <= i <= 7 ==> deletion_counterexample_states()[i].control.fibers[0usize].phase != Phase::Inactive,
        deletion_counterexample_states()[1].control.fibers[0usize].phase == Phase::Inactive,
        deletion_counterexample_states()[8].control.fibers[0usize].phase == Phase::Inactive,
        forall|i:int,n:usize| 0 <= i < deletion_counterexample_states().len() && n != 0 && s::registered(deletion_counterexample_states()[i],n)
            ==> deletion_counterexample_states()[i].control.fibers[n].phase == Phase::Inactive,
        forall|provider:usize,consumer:usize| !crate::global::predecessor(deletion_counterexample_states().last().control,provider,consumer),
        s::registered(deletion_counterexample_states().last(),1),
        deletion_counterexample_states().last().control.fibers[1usize].retired,
        deletion_counterexample_states().last().control.fibers[1usize].phase == Phase::Inactive,
        deletion_counterexample_states().last().tables[1usize].is_empty(),
        !s::vestigial(deletion_counterexample_states().last(),1),
        deletion_counterexample_states().last().control.fibers[2usize].parent == Some(1usize),
{
    crate::paper_counterexamples::transposition_parent_counterexample();
    let states = deletion_counterexample_states();
    let labels = deletion_counterexample_labels();
    let model = crate::paper_counterexamples::creation_model();
    p::empty_well_formed::<u64>();
    assert(p::well_formed(states[0]));
    assert(p::insert_map(states[0],states[1],0));
    assert(s::auxiliary_frame(states[0],states[1],0));
    assert(s::step(model,states[0],states[1],0,c::Rule::Insert));
    assert(s::step(model,states[1],states[2],0,c::Rule::Begin));
    assert(p::child_map(states[2],(model.iterate)(0,0,states[2]).state,0,1));
    assert(p::admissible_step(model,states[2],states[3],0,c::Rule::Finish));
    assert(p::insert_map(states[3],states[4],2));
    assert(s::step(model,states[4],states[5],2,c::Rule::Retire));
    p::retire_preservation(states[4],states[5],2);
    assert(s::step(model,states[5],states[6],0,c::Rule::Retire));
    p::retire_preservation(states[5],states[6],0);
    assert(!s::coherent(states[6],0));
    assert(s::step(model,states[6],states[7],0,c::Rule::Leave));
    p::full_preservation(model,states[6],states[7],0,c::Rule::Leave);
    assert(!c::relied(states[7].control,0)) by {
        assert forall|n:usize| s::registered(states[7],n) implies states[7].control.fibers[n].committed.is_empty() by { }
    }
    crate::child_history::concrete_child_retirement(states[7],1);
    assert(s::child_retire(states[7],(model.undo)(1,states[7]),1));
    assert(p::inverse_map(states[7],(model.undo)(1,states[7]),0));
    assert(states[7].accumulators[0usize] == seq![1nat]);
    assert(p::admissible_restore(model,Seq::empty(),(model.undo)(1,states[7]),0));
    reveal_with_fuel(p::admissible_restore,2);
    assert(p::admissible_restore(model,states[7].accumulators[0usize],states[7],0));
    reveal_with_fuel(s::restore,2);
    assert(s::restore(model,states[7].accumulators[0usize],states[7]) == (model.undo)(1,states[7]));
    assert(s::step(model,states[7],states[8],0,c::Rule::Unload));
    p::full_preservation(model,states[7],states[8],0,c::Rule::Unload);
    assert(p::execution(model,states,labels)) by {
        assert forall|i:int| 0 <= i < labels.len() implies s::step(model,states[i],states[i+1],labels[i].0,labels[i].1)
            && p::admissible_step(model,states[i],states[i+1],labels[i].0,labels[i].1) by { }
    }
    assert(s::execution(model,states,labels)) by {
        assert forall|i:int| 0 <= i < labels.len() implies s::step(model,states[i],states[i+1],labels[i].0,labels[i].1) by { }
    }
    s::execution_reaches(model,states,labels);
    let end = states.last();
    assert forall|n:usize| s::registered(end,n) implies n == 0 || n == 1 || n == 2 by { }
    assert forall|n:usize| s::registered(end,n) implies end.control.fibers[n].retired
        && end.control.fibers[n].phase == Phase::Inactive by { }
    assert(s::quiet(end)) by {
        assert forall|n:usize| s::registered(end,n) implies match end.control.fibers[n].phase {
            Phase::Inactive => !(exists|view:ISet<Binding>| s::target(end,n,view)),
            Phase::Active => s::coherent(end,n),
            _ => false,
        } by { }
    }
    assert forall|i:int,n:usize| 0 <= i < states.len() && s::registered(states[i],n)
        implies states[i].control.fibers[n].provisions.is_empty() by { }
    assert forall|i:int| 2 <= i <= 7 implies states[i].control.fibers[0usize].phase != Phase::Inactive by { }
    assert forall|i:int,n:usize| 0 <= i < states.len() && n != 0 && s::registered(states[i],n)
        implies states[i].control.fibers[n].phase == Phase::Inactive by { }
    assert forall|provider:usize,consumer:usize| !crate::global::predecessor(end.control,provider,consumer) by {
        if s::registered(end,provider) { assert(end.control.fibers[provider].provisions.is_empty()); }
    }
    assert(s::registered(end,2));
    assert(end.control.fibers[2usize].parent == Some(1usize));
}

/// Deleting the creator's activation removes the only birth of 1. The first
/// surviving external insertion still requests parent 1, so it is impossible.
/// This obstruction also holds if the opening Begin is retained literally
/// (the printed episode indices start immediately after that Begin).
pub proof fn deletion_counterexample_prefix_impossible()
    ensures !exists|first:s::State<u64>,second:s::State<u64>|
        s::step(crate::paper_counterexamples::creation_model(),s::empty_state::<u64>(),first,0,c::Rule::Insert)
        && s::step(crate::paper_counterexamples::creation_model(),first,second,2,c::Rule::Insert)
        && second.control.fibers[2usize].parent == Some(1usize),
        !exists|first:s::State<u64>,begun:s::State<u64>,second:s::State<u64>|
        s::step(crate::paper_counterexamples::creation_model(),s::empty_state::<u64>(),first,0,c::Rule::Insert)
        && s::step(crate::paper_counterexamples::creation_model(),first,begun,0,c::Rule::Begin)
        && s::step(crate::paper_counterexamples::creation_model(),begun,second,2,c::Rule::Insert)
        && second.control.fibers[2usize].parent == Some(1usize),
{
    crate::paper_counterexamples::canonical_orchestration_prefix_impossible();
    assert forall|first:s::State<u64>,begun:s::State<u64>,second:s::State<u64>|
        s::step(crate::paper_counterexamples::creation_model(),s::empty_state::<u64>(),first,0,c::Rule::Insert)
        && s::step(crate::paper_counterexamples::creation_model(),first,begun,0,c::Rule::Begin)
        && s::step(crate::paper_counterexamples::creation_model(),begun,second,2,c::Rule::Insert)
        implies second.control.fibers[2usize].parent != Some(1usize) by {
        assert(!s::registered(first,1));
        assert(!s::registered(begun,1));
    }
}


/// LIFO restoration cannot add or remove keys in a foreign table. This derives
/// the empty-child part of the deletion boundary from actual inverse maps.
pub proof fn restore_foreign_domain<V>(model:s::Model<V>,tokens:Seq<nat>,a:s::State<V>,actor:usize,child:usize)
    requires p::well_formed(a),s::registered(a,actor),s::registered(a,child),actor != child,
        p::admissible_restore(model,tokens,a,actor),
    ensures s::restore(model,tokens,a).tables[child].dom() == a.tables[child].dom(),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        let b = (model.undo)(tokens.last(),a);
        p::inverse_preservation(a,b,actor);
        if p::table_map(a,b,actor) { assert(a.tables[child].dom() == b.tables[child].dom()); }
        else {
            let retired = choose|retired:usize| s::child_retire(a,b,retired);
            assert(a.tables == b.tables);
        }
        restore_foreign_domain(model,tokens.drop_last(),b,actor,child);
    }
}

/// Actual birth history and retained inverse identities discharge retirement
/// at the close of the creator's episode. Empty/Inactive children become
/// vestigial exactly when no external descendant still names them as parent.
/// The latter condition is essential, as the full counterexample demonstrates.
pub proof fn unload_born_leaf_vestigial<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,
    history:crate::child_history::History,a:s::State<V>,z:s::State<V>,actor:usize,child:usize)
    requires p::well_formed(a),crate::child_history::valid(kind,history,a),
        crate::child_history::retained(kind,a),crate::child_history::primitive_inverses(model,kind),
        history.births.dom().contains(child),history.births[child].parent == actor,actor != child,
        a.control.fibers[child].phase == Phase::Inactive,a.tables[child].is_empty(),
        forall|m:usize| s::registered(a,m) ==> a.control.fibers[m].parent != Some(child),
        s::step(model,a,z,actor,c::Rule::Unload),
    ensures p::well_formed(z),s::vestigial(z,child),s::same_tables(z,s::erase(z,child)),
{
    let tokens = a.accumulators[actor];
    assert forall|token:nat| tokens.contains(token) implies a.accumulators[actor].contains(token) by { }
    crate::child_history::retained_recovery(model,kind,tokens,a,actor);
    crate::child_history::recovery_consequences(model,kind,tokens,a,actor);
    restore_foreign_domain(model,tokens,a,actor,child);
    let restored = s::restore(model,tokens,a);
    if !a.control.fibers[child].retired {
        let token = history.births[child].inverse;
        assert(tokens.contains(token));
        assert(kind(token) == Some(child));
        crate::child_history::recovery_retires_token(model,kind,tokens,a,actor,token,child);
    }
    assert(restored.control.fibers[child].retired);
    assert(restored.tables[child].is_empty());
    assert forall|m:usize| s::registered(restored,m) implies restored.control.fibers[m].parent != Some(child) by {
        assert(s::registered(a,m));
        assert(c::interface_same(a.control.fibers[m],restored.control.fibers[m]));
    }
    p::full_preservation(model,a,z,actor,c::Rule::Unload);
    assert(s::vestigial(restored,child));
    p::restore_preservation(model,tokens,a,actor);
    edit_preserves_vestigial(restored,child,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
    erase_observation(z,child);
}


/// Composition from a real closing Unload through the constructed surviving
/// suffix. This discharges the child-boundary premise from birth and inverse
/// history; deleting the creator's interleaved prefix is a separate obligation.
pub proof fn closing_episode_suffix<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,
    history:crate::child_history::History,before:s::State<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,actor:usize,child:usize)
    requires p::well_formed(before),crate::child_history::valid(kind,history,before),
        crate::child_history::retained(kind,before),crate::child_history::primitive_inverses(model,kind),
        history.births.dom().contains(child),history.births[child].parent == actor,actor != child,
        before.control.fibers[child].phase == Phase::Inactive,before.tables[child].is_empty(),
        forall|m:usize| s::registered(before,m) ==> before.control.fibers[m].parent != Some(child),
        s::step(model,before,states.first(),actor,c::Rule::Unload),
        suffix_admissible(model,states,labels,child),
    ensures s::execution(model,surviving_states(states,labels,child),surviving_labels(labels,child)),
        surviving_states(states,labels,child).first() == s::erase(states.first(),child),
        surviving_states(states,labels,child).last() == s::erase(states.last(),child),
        s::same_tables(states.last(),surviving_states(states,labels,child).last()),
{
    unload_born_leaf_vestigial(model,kind,history,before,states.first(),actor,child);
    suffix_deletion(model,states,labels,child);
}


/// Definition 56's concrete single-slot implementation satisfies the erasure
/// square directly, for both operations and provision/restriction inverses.
pub proof fn table_slot_erases<V>(a:s::State<V>,owner:usize,key:crate::Port,value:Option<V>,removed:usize)
    requires owner != removed,
    ensures s::erase(crate::projection::update_slot(a,owner,key,value),removed)
        == crate::projection::update_slot(s::erase(a,removed),owner,key,value),
{
    assert(crate::projection::update_slot(a,owner,key,value).tables.remove(removed)
        =~= crate::projection::update_slot(s::erase(a,removed),owner,key,value).tables);
}

/// An actual retained child token different from the deleted child has the
/// erasure law by its concrete retirement interpretation, not by an assumed
/// simulation property of the entire Unload.
pub proof fn retained_child_inverse_erases<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,
    a:s::State<V>,owner:usize,token:nat,removed:usize)
    requires crate::child_history::primitive_inverses(model,kind),crate::child_history::retained(kind,a),
        crate::child_history::remove_unreferenced(kind,a,removed),s::registered(a,owner),
        a.accumulators[owner].contains(token),kind(token).is_some(),
    ensures s::erase((model.undo)(token,a),removed) == (model.undo)(token,s::erase(a,removed)),
{
    let child = kind(token).unwrap();
    assert(kind(token) == Some(child));
    assert(child != removed);
    assert(s::registered(a,child));
    assert(s::registered(s::erase(a,removed),child));
    child_retirement_erases(a,child,removed);
}


pub proof fn erased_projection_equal<V>(a:s::State<V>,child:usize)
    requires p::well_formed(a),s::vestigial(a,child) || !s::registered(a,child),
    ensures crate::projection::project(a,ISet::full()) == crate::projection::project(s::erase(a,child),ISet::full()),
{
    if s::vestigial(a,child) {
        crate::projection::unique_owner(a);
        crate::projection::empty_erasure(a,child,ISet::full());
    } else { erase_absent(a,child); }
}

/// Integrated boundary: the actual episode's returned inverse journal recovers
/// its foreign value replay; real birth history retires its leaf child; the
/// actual remaining suffix becomes a constructed legal child-erased execution.
/// The foreign value replay is not asserted to be a legal lifecycle prefix.
pub proof fn recovery_and_child_suffix<V>(model:s::Model<V>,kind:spec_fn(nat)->Option<usize>,
    meaning:spec_fn(nat)->crate::entangled::Action<V>,forward:crate::entangled::ForwardMeaning<V>,
    history:crate::child_history::History,episode_states:Seq<s::State<V>>,episode_labels:Seq<(usize,c::Rule)>,
    suffix_states:Seq<s::State<V>>,suffix_labels:Seq<(usize,c::Rule)>,actor:usize,child:usize)
    requires crate::entangled::episode_profile(model,meaning,forward,episode_states,episode_labels,actor),
        crate::child_history::valid(kind,history,episode_states.last()),
        crate::child_history::retained(kind,episode_states.last()),crate::child_history::primitive_inverses(model,kind),
        history.births.dom().contains(child),history.births[child].parent == actor,actor != child,
        episode_states.last().control.fibers[child].phase == Phase::Inactive,episode_states.last().tables[child].is_empty(),
        forall|m:usize| s::registered(episode_states.last(),m) ==> episode_states.last().control.fibers[m].parent != Some(child),
        s::step(model,episode_states.last(),suffix_states.first(),actor,c::Rule::Unload),
        crate::entangled::restore_projection_contract(model,meaning,episode_states.last().accumulators[actor],episode_states.last()),
        suffix_admissible(model,suffix_states,suffix_labels,child),
    ensures s::execution(model,surviving_states(suffix_states,suffix_labels,child),surviving_labels(suffix_labels,child)),
        crate::projection::project(surviving_states(suffix_states,suffix_labels,child).first(),ISet::full())
            == crate::entangled::foreign_state(crate::entangled::events_of(model,meaning,forward,episode_states,episode_labels,actor),
                crate::projection::project(episode_states.first(),ISet::full())),
        surviving_states(suffix_states,suffix_labels,child).last() == s::erase(suffix_states.last(),child),
        s::same_tables(suffix_states.last(),surviving_states(suffix_states,suffix_labels,child).last()),
        crate::projection::project(suffix_states.last(),ISet::full())
            == crate::projection::project(surviving_states(suffix_states,suffix_labels,child).last(),ISet::full()),
{
    p::execution_preservation(model,episode_states,episode_labels);
    let before = episode_states.last();
    assert(p::well_formed(before));
    assert(s::registered(before,actor));
    assert forall|token:nat| before.accumulators[actor].contains(token)
        implies before.accumulators[actor].contains(token) by { }
    crate::child_history::retained_recovery(model,kind,before.accumulators[actor],before,actor);
    crate::entangled::full_terminal_recovery(model,meaning,forward,episode_states,episode_labels,actor,suffix_states.first());
    unload_born_leaf_vestigial(model,kind,history,before,suffix_states.first(),actor,child);
    erased_projection_equal(suffix_states.first(),child);
    suffix_deletion(model,suffix_states,suffix_labels,child);
    erased_projection_equal(suffix_states.last(),child);
}

} // verus!
