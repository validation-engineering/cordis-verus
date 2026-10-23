//! Actual Restore origins for a typed gap whose semantic head was recovered.
#[cfg(verus_keep_ghost)]
use super::{restored_head, Step};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, managed::ResultStep, payload};
use vstd::prelude::*;

verus! {
pub open spec fn interference<T:?Sized>(earlier:Step<T>,later:Step<T>)->bool {
    restored_head(earlier,later) && match (earlier.result,later.result) {
        (ResultStep::Payload(a),ResultStep::Payload(b))=>a.inverse().after().revision<b.inverse().before().revision,
        _=>false,
    }
}
pub open spec fn origin<T:?Sized>(earlier:Step<T>,later:Step<T>,index:nat)->bool {
    earlier.write().at()<index<later.write().at()
        && later.write().events()[index as int].event.key==earlier.address().key
        && later.write().events()[index as int].event.change==joint::Change::PayloadRestore
}
/// Increasing revision and a returned semantic head identify an actual Restore
/// in the common history. A repeated payload value cannot serve as that proof.
pub proof fn between<T:?Sized>(earlier:Step<T>,later:Step<T>)->(index:nat)
    requires earlier.recorded_values(),later.recorded_values(),earlier.address()==later.address(),
        later.write().follows(&earlier.write()),interference(earlier,later),
    ensures origin(earlier,later,index),
{
    hide(joint::valid);hide(joint::step);
    let ar=earlier.write();let br=later.write();let frames=br.events();let key=ar.event().key;
    br.included(&ar);
    match (earlier.result,later.result) {
        (ResultStep::Payload(x),ResultStep::Payload(y))=>{
            let a=x.inverse();let b=y.inverse();a.source_history();b.source_history();
            let revision=b.before().revision as int;let previous=a.after().revision as int;
            let positions=b.after().positions;let states=b.after().states;
            assert(states[revision]==b.before().state());
            assert(states[revision].head==previous);
            payload::semantic_history::restored(states,positions,frames,revision);
            joint::payload::unique_revision(frames,ar.at(),positions[previous],key);
            joint::payload::unique_revision(frames,br.at(),positions[b.after().revision as int],key);
            assert(positions[previous]<positions[revision]);
            assert(positions[revision]<positions[b.after().revision as int]);
            positions[revision]
        },_=>{assert(false);0},
    }
}
}
