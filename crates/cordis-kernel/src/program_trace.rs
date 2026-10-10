//! Finite successful API traces of the fixed-program driver under one model.
//!
//! The catalog records immutable code/layout/initial values for every allocated
//! identity, including removed identities. Administrative calls are erased and
//! atomic landing performs target-drift acknowledgement before returning.
use crate::program::LandOutcome;
#[cfg(verus_keep_ghost)]
use crate::resources::Cell;
#[cfg(verus_keep_ghost)]
use crate::{program_refinement as p, refinement as c, semantics as s};
use vstd::prelude::*;

verus! {
/// A raw driver acknowledgement; no full semantic step is assumed here.
pub open spec fn atomic_ack(a:p::Snapshot,z:p::Snapshot,n:usize,result:LandOutcome) -> bool {
    match result {
        LandOutcome::Advanced => p::landed(a,z,n) && c::coherent(a.control,n),
        LandOutcome::Terminal => p::terminal_poll(a,z,n) && c::coherent(a.control,n),
        LandOutcome::Diverted => exists|middle:p::Snapshot| p::wf(middle)
            && (p::landed(a,middle,n) || p::terminal_poll(a,middle,n))
            && p::depart_ack(middle,z,n),
    }
}

pub enum Event {
    Insert(usize), Retire(usize), Remove(usize), Begin(usize),
    Admit(usize), Land(usize,LandOutcome), Finish(usize), Depart(usize), Unload(usize),
}

pub open spec fn actor(event:Event) -> usize {
    match event {
        Event::Insert(n) | Event::Retire(n) | Event::Remove(n) | Event::Begin(n)
        | Event::Admit(n) | Event::Land(n,_) | Event::Finish(n) | Event::Depart(n) | Event::Unload(n) => n,
    }
}

pub open spec fn ack(a:p::Snapshot,z:p::Snapshot,event:Event) -> bool {
    match event {
        Event::Insert(n) => p::passive_ack(a,z,n,c::Rule::Insert),
        Event::Retire(n) => p::passive_ack(a,z,n,c::Rule::Retire),
        Event::Remove(n) => p::passive_ack(a,z,n,c::Rule::Remove),
        Event::Begin(n) => p::begin_ack(a,z,n),
        Event::Admit(n) => p::administrative(a,z,n),
        Event::Land(n,result) => atomic_ack(a,z,n,result),
        Event::Finish(n) => p::finish_ack(a,z,n),
        Event::Depart(n) => p::depart_ack(a,z,n),
        Event::Unload(n) => p::unload_ack(a,z,n),
    }
}

pub open spec fn label(a:p::Snapshot,event:Event) -> Option<(usize,c::Rule)> {
    let n=actor(event);
    match event {
        Event::Insert(_) => Some((n,c::Rule::Insert)),
        Event::Retire(_) => Some((n,c::Rule::Retire)),
        Event::Remove(_) => Some((n,c::Rule::Remove)),
        Event::Begin(_) => Some((n,c::Rule::Begin)),
        Event::Admit(_) | Event::Land(_,LandOutcome::Terminal) => None,
        Event::Land(_,LandOutcome::Advanced) => Some((n,c::Rule::Iter)),
        Event::Land(_,LandOutcome::Diverted) => Some((n,c::Rule::Divert)),
        Event::Finish(_) => Some((n,c::Rule::Finish)),
        Event::Depart(_) => Some((n,if a.control.fibers[n].phase == crate::Phase::Loading {c::Rule::Divert} else {c::Rule::Leave})),
        Event::Unload(_) => Some((n,c::Rule::Unload)),
    }
}

pub proof fn local_refinement(a:p::Snapshot,z:p::Snapshot,event:Event)
    requires p::wf(a),p::wf(z),ack(a,z,event),
    ensures match label(a,event) {
        None => p::project(a) == p::project(z),
        Some(l) => s::step(p::model(a),p::project(a),p::project(z),l.0,l.1),
    },
{
    match event {
        Event::Insert(n) => p::passive_rule(a,z,n,c::Rule::Insert),
        Event::Retire(n) => p::passive_rule(a,z,n,c::Rule::Retire),
        Event::Remove(n) => p::passive_rule(a,z,n,c::Rule::Remove),
        Event::Begin(n) => p::begun(a,z,n),
        Event::Admit(n) => p::administrative_stutter(a,z,n),
        Event::Finish(n) => p::finished(a,z,n),
        Event::Depart(n) => p::departed(a,z,n),
        Event::Unload(n) => p::unloaded(a,z,n),
        Event::Land(n,result) => match result {
            LandOutcome::Advanced => p::landed_iter(a,z,n),
            LandOutcome::Terminal => p::administrative_stutter(a,z,n),
            LandOutcome::Diverted => {
                let middle=choose|middle:p::Snapshot| p::wf(middle)
                    && (p::landed(a,middle,n) || p::terminal_poll(a,middle,n))
                    && p::depart_ack(middle,z,n);
                if p::landed(a,middle,n) { p::landed_divert(a,middle,z,n); }
                else {
                    p::administrative_stutter(a,middle,n);
                    p::departed(middle,z,n);
                    // Terminal polling changes only `ended`; its model uses
                    // immutable code/layout/initial values, which are framed.
                    model_step_transport(middle,a,p::project(a),p::project(z),n,c::Rule::Divert);
                }
            },
        },
    }
}

pub open spec fn configuration_equal(a:p::Snapshot,b:p::Snapshot,n:usize) -> bool {
    a.codes[n] == b.codes[n] && a.layouts[n] == b.layouts[n]
        && a.initial[n] == b.initial[n] && a.owners[n] == b.owners[n]
}

/// A single immutable catalog can cover names inserted later in the trace.
/// This is a data-consistency requirement, never a step or confluence premise.
pub open spec fn catalog_agrees(catalog:p::Snapshot,x:p::Snapshot) -> bool {
    forall|n:usize| c::registered(x.control,n) ==> configuration_equal(catalog,x,n)
}

pub proof fn restore_transport(a:p::Snapshot,b:p::Snapshot,state:s::State<Cell>,n:usize,count:nat)
    requires configuration_equal(a,b,n),count <= p::base(),
    ensures s::restore(p::model(a),p::tokens(n,count),state) == s::restore(p::model(b),p::tokens(n,count),state),
    decreases count,
{
    if count > 0 {
        let id=p::token(n,(count-1) as nat);
        p::token_round_trip(n,(count-1) as nat);
        assert(p::tokens(n,count).last() == id);
        assert(p::tokens(n,count).drop_last() =~= p::tokens(n,(count-1) as nat));
        assert((p::model(a).undo)(id,state) == (p::model(b).undo)(id,state));
        restore_transport(a,b,(p::model(a).undo)(id,state),n,(count-1) as nat);
    }
}

pub proof fn model_step_transport(a:p::Snapshot,b:p::Snapshot,x:s::State<Cell>,z:s::State<Cell>,n:usize,rule:c::Rule)
    requires configuration_equal(a,b,n),s::step(p::model(a),x,z,n,rule),
        rule == c::Rule::Unload ==> exists|count:nat| count <= p::base() && x.accumulators[n] == p::tokens(n,count),
    ensures s::step(p::model(b),x,z,n,rule),
{
    assert((p::model(a).iterate)(n,x.iterators[n].unwrap(),x) == (p::model(b).iterate)(n,x.iterators[n].unwrap(),x));
    if rule == c::Rule::Unload {
        let count=choose|count:nat| count <= p::base() && x.accumulators[n] == p::tokens(n,count);
        restore_transport(a,b,x,n,count);
    }
}

pub proof fn fixed_model_refinement(catalog:p::Snapshot,a:p::Snapshot,z:p::Snapshot,event:Event)
    requires p::wf(a),p::wf(z),catalog_agrees(catalog,a),ack(a,z,event),
    ensures match label(a,event) {
        None => p::project(a) == p::project(z),
        Some(l) => s::step(p::model(catalog),p::project(a),p::project(z),l.0,l.1),
    },
{
    local_refinement(a,z,event);
    if label(a,event).is_some() {
        let l=label(a,event).unwrap();
        if l.1 == c::Rule::Insert {
            assert(s::step(p::model(catalog),p::project(a),p::project(z),l.0,l.1));
        } else {
            assert(c::registered(a.control,l.0));
            assert(p::row_wf(a,l.0));
            let count=a.depths[l.0]+if p::extra_terminal(a,l.0) {1nat} else {0nat};
            assert(count <= p::base());
            assert(p::project(a).accumulators[l.0] == p::tokens(l.0,count));
            model_step_transport(a,catalog,p::project(a),p::project(z),l.0,l.1);
        }
    }
}

/// This finite API history records concrete acknowledgements only. Allocation
/// watermarks come from the real monotone Kernel allocator in each snapshot.
pub open spec fn raw_execution(states:Seq<p::Snapshot>,events:Seq<Event>) -> bool {
    &&& states.len() == events.len()+1
    &&& forall|i:int| 0 <= i < states.len() ==> p::wf(states[i])
    &&& forall|i:int| 0 <= i < events.len() ==> ack(states[i],states[i+1],events[i])
}

pub proof fn acknowledgement_frame(a:p::Snapshot,z:p::Snapshot,event:Event)
    requires p::wf(a),p::wf(z),ack(a,z,event),
    ensures a.allocated <= z.allocated,
        forall|n:usize| c::registered(a.control,n) && c::registered(z.control,n) ==> configuration_equal(a,z,n),
        forall|n:usize| n < a.allocated && !c::registered(a.control,n) ==> !c::registered(z.control,n),
{
    match event {
        Event::Land(n,LandOutcome::Diverted) => {
            let middle=choose|middle:p::Snapshot| p::wf(middle)
                && (p::landed(a,middle,n) || p::terminal_poll(a,middle,n))
                && p::depart_ack(middle,z,n);
            assert forall|m:usize| c::registered(a.control,m) && c::registered(z.control,m)
                implies configuration_equal(a,z,m) by {
                assert(c::registered(middle.control,m));
            }
        },
        _ => {},
    }
}

pub proof fn allocation_monotone(states:Seq<p::Snapshot>,events:Seq<Event>)
    requires raw_execution(states,events),
    ensures forall|i:int| 0 <= i < states.len() ==> states[i].allocated <= states.last().allocated,
    decreases events.len(),
{
    // Compose the proved acknowledgement contract without unfolding every
    // event's transition relation again in the trace induction.
    hide(ack);
    if events.len() > 0 {
        allocation_monotone(states.drop_last(),events.drop_last());
        acknowledgement_frame(states[events.len()-1],states.last(),events.last());
        assert forall|i:int| 0 <= i < states.len() implies states[i].allocated <= states.last().allocated by {
            if i < states.len()-1 {
                assert(states.drop_last()[i].allocated <= states.drop_last().last().allocated);
            }
        }
    } else {
        assert forall|i:int| 0 <= i < states.len() implies states[i].allocated <= states.last().allocated by {assert(i == 0);}
    }
}

/// A name below an earlier allocation watermark cannot be recreated. Following
/// a live final name backwards therefore preserves its immutable code, including
/// histories that remove other fibers and insert later ones.
pub proof fn historical_configuration(states:Seq<p::Snapshot>,events:Seq<Event>,index:int,n:usize)
    requires raw_execution(states,events),0 <= index < states.len(),
        n < states[index].allocated,c::registered(states.last().control,n),
    ensures c::registered(states[index].control,n),configuration_equal(states[index],states.last(),n),
    decreases events.len(),
{
    if index < states.len()-1 {
        let previous=states.drop_last();let prior=events.drop_last();
        allocation_monotone(previous,prior);
        acknowledgement_frame(previous.last(),states.last(),events.last());
        assert(previous[index].allocated <= previous.last().allocated);
        assert(previous[index] == states[index]);
        assert(n < previous.last().allocated);
        assert(c::registered(previous.last().control,n));
        historical_configuration(previous,prior,index,n);
    }
}

pub open spec fn seen(states:Seq<p::Snapshot>,n:usize) -> bool {
    exists|i:int| 0 <= i < states.len() && c::registered(states[i].control,n)
}
pub open spec fn occurrence(states:Seq<p::Snapshot>,n:usize) -> int {
    choose|i:int| 0 <= i < states.len() && c::registered(states[i].control,n)
}

/// Recover the immutable catalog from this finite execution itself. It need not
/// be a reachable state: only its immutable fields parameterize the interpreter.
pub open spec fn history_catalog(states:Seq<p::Snapshot>) -> p::Snapshot {
    let x=states.last();
    p::Snapshot {
        allocated:x.allocated,control:x.control,
        layouts:IMap::new(|n:usize|seen(states,n),|n:usize|states[occurrence(states,n)].layouts[n]),
        codes:IMap::new(|n:usize|seen(states,n),|n:usize|states[occurrence(states,n)].codes[n]),
        initial:IMap::new(|n:usize|seen(states,n),|n:usize|states[occurrence(states,n)].initial[n]),
        owners:IMap::new(|n:usize|seen(states,n),|n:usize|states[occurrence(states,n)].owners[n]),
        cells:x.cells,positions:x.positions,depths:x.depths,ended:x.ended,
    }
}

#[verifier::spinoff_prover]
pub proof fn catalog_from_history(states:Seq<p::Snapshot>,events:Seq<Event>)
    requires raw_execution(states,events),
    ensures api_execution(history_catalog(states),states,events),
{
    assert forall|i:int| 0 <= i < states.len() implies catalog_agrees(history_catalog(states),states[i]) by {
        assert forall|n:usize| c::registered(states[i].control,n)
            implies configuration_equal(history_catalog(states),states[i],n) by {
            assert(seen(states,n));
            let j=occurrence(states,n);
            assert(0 <= j < states.len());
            assert(c::registered(states[j].control,n));
            if i <= j {
                let xs=states.subrange(0,j+1);let es=events.subrange(0,j);
                assert(raw_execution(xs,es)) by {
                    assert forall|k:int| 0 <= k < xs.len() implies p::wf(xs[k]) by {
                        assert(xs[k] == states[k]);
                    }
                    assert forall|k:int| 0 <= k < es.len() implies ack(xs[k],xs[k+1],es[k]) by {
                        assert(xs[k] == states[k]);
                        assert(xs[k+1] == states[k+1]);
                        assert(es[k] == events[k]);
                    }
                }
                assert(xs[i] == states[i]);
                assert(xs.last() == states[j]);
                assert(n < states[i].allocated);
                historical_configuration(xs,es,i,n);
            } else {
                let xs=states.subrange(0,i+1);let es=events.subrange(0,i);
                assert(raw_execution(xs,es)) by {
                    assert forall|k:int| 0 <= k < xs.len() implies p::wf(xs[k]) by {
                        assert(xs[k] == states[k]);
                    }
                    assert forall|k:int| 0 <= k < es.len() implies ack(xs[k],xs[k+1],es[k]) by {
                        assert(xs[k] == states[k]);
                        assert(xs[k+1] == states[k+1]);
                        assert(es[k] == events[k]);
                    }
                }
                assert(xs[j] == states[j]);
                assert(xs.last() == states[i]);
                assert(n < states[j].allocated);
                historical_configuration(xs,es,j,n);
            }
            assert(configuration_equal(states[i],states[j],n));
            assert(history_catalog(states).layouts[n] == states[j].layouts[n]);
            assert(history_catalog(states).codes[n] == states[j].codes[n]);
            assert(history_catalog(states).initial[n] == states[j].initial[n]);
            assert(history_catalog(states).owners[n] == states[j].owners[n]);
        }
    }
}

pub open spec fn api_execution(catalog:p::Snapshot,states:Seq<p::Snapshot>,events:Seq<Event>) -> bool {
    &&& states.len() == events.len()+1
    &&& forall|i:int| 0 <= i < states.len() ==> p::wf(states[i]) && catalog_agrees(catalog,states[i])
    &&& forall|i:int| 0 <= i < events.len() ==> ack(states[i],states[i+1],events[i])
}

pub open spec fn paper_states(states:Seq<p::Snapshot>,events:Seq<Event>) -> Seq<s::State<Cell>>
    decreases events.len(),
{
    if events.len() == 0 {seq![p::project(states[0])]}
    else {
        let previous=paper_states(states.drop_last(),events.drop_last());
        if label(states[events.len()-1],events.last()).is_some() {previous.push(p::project(states.last()))} else {previous}
    }
}

pub open spec fn paper_labels(states:Seq<p::Snapshot>,events:Seq<Event>) -> Seq<(usize,c::Rule)>
    decreases events.len(),
{
    if events.len() == 0 {Seq::empty()}
    else {
        let previous=paper_labels(states.drop_last(),events.drop_last());
        let last=label(states[events.len()-1],events.last());
        if last.is_some() {previous.push(last.unwrap())} else {previous}
    }
}

/// Erase administration and construct a legal full-rule execution, preserving
/// both endpoint payloads. The model stays fixed even across insert/remove.
pub proof fn trace_refinement(catalog:p::Snapshot,states:Seq<p::Snapshot>,events:Seq<Event>)
    requires api_execution(catalog,states,events),
    ensures s::execution(p::model(catalog),paper_states(states,events),paper_labels(states,events)),
        paper_states(states,events).first() == p::project(states.first()),
        paper_states(states,events).last() == p::project(states.last()),
        paper_labels(states,events).len() <= events.len(),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix=states.drop_last();let prior=events.drop_last();
        assert(api_execution(catalog,prefix,prior));
        trace_refinement(catalog,prefix,prior);
        let a=states[events.len()-1];let z=states.last();let event=events.last();
        assert(ack(a,z,event));
        fixed_model_refinement(catalog,a,z,event);
        let xs=paper_states(states,events);let ls=paper_labels(states,events);
        assert forall|i:int| 0 <= i < ls.len() implies s::step(p::model(catalog),xs[i],xs[i+1],ls[i].0,ls[i].1) by {
            if i < paper_labels(prefix,prior).len() {
                assert(s::step(p::model(catalog),paper_states(prefix,prior)[i],paper_states(prefix,prior)[i+1],paper_labels(prefix,prior)[i].0,paper_labels(prefix,prior)[i].1));
            } else {
                assert(i == ls.len()-1);assert(label(a,event).is_some());
            }
        }
    }
}

/// End-to-end finite trace theorem with a constructed, single fixed model.
/// Successful calls may interleave insertion, removal, admission and landing;
/// neither a whole paper step nor a supplied catalog is a premise.
pub proof fn driver_trace_refinement(states:Seq<p::Snapshot>,events:Seq<Event>)
    requires raw_execution(states,events),
    ensures s::execution(p::model(history_catalog(states)),paper_states(states,events),paper_labels(states,events)),
        paper_states(states,events).first() == p::project(states.first()),
        paper_states(states,events).last() == p::project(states.last()),
        s::reaches(p::model(history_catalog(states)),p::project(states.first()),p::project(states.last()),paper_labels(states,events).len()),
{
    catalog_from_history(states,events);
    trace_refinement(history_catalog(states),states,events);
    s::execution_reaches(p::model(history_catalog(states)),paper_states(states,events),paper_labels(states,events));
}

} // verus!
