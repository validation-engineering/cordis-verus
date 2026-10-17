//! Complete classification of the actual native Journal carrier. The state
//! contains every Record and outstanding managed inverse, not only the scalar
//! heap or control projection. Host/configuration steps retain their explicit
//! semantics; a projection stutter is never promoted to a whole-state stutter.
//! Opaque payload interiors, JS callbacks and foreign Journals are not this
//! carrier. The paper's named-port lift still needs its alias condition.
use super::Record;
#[cfg(verus_keep_ghost)]
use super::{Change, Frame, Step};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{access, alias, effect, Event, ValueState};
#[cfg(verus_keep_ghost)]
use crate::{dependent_grammar as d, refinement as r};
use vstd::prelude::*;

verus! {
/// Both parts are observed at the same real Journal commit. Removing pending
/// obligations from this carrier would hide inverse registration effects.
pub ghost struct Observation {pub records:Map<nat,Record>,pub pending:Map<nat,nat>}
pub open spec fn at(frames:Seq<Frame>,index:nat)->Observation {
    Observation {records:super::state_at(frames,index),pending:super::pending_at(frames,index)}
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Class {Allocation,Forward,Restore,Rejection,Replacement,PayloadReplacement,PayloadForward,PayloadRestoration,PayloadRetirement,NativeRule,NativeRestart,
    Recipes,Configuration,Sources,Work,Cleanup,Groups,Host,Control,InverseRegistration}
pub open spec fn class(event:Step)->Class {
    match event.change {
        Change::Allocate=>Class::Allocation,
        Change::Value {event}=>match event {
            Event::Forward {..}|Event::Computed {..}=>Class::Forward,
            Event::Restore {..}=>Class::Restore,
            Event::Rejected {..}|Event::Blocked {..}|Event::ComputationRejected {..}|Event::StaleComputation {..}=>Class::Rejection,
        },
        Change::Replace=>Class::Replacement,
        Change::PayloadReplace=>Class::PayloadReplacement,
        Change::PayloadApply=>Class::PayloadForward,Change::PayloadRestore=>Class::PayloadRestoration,
        Change::PayloadRetire=>Class::PayloadRetirement,
        Change::Native {rule,..}=>if rule==r::Rule::Restart {Class::NativeRestart} else {Class::NativeRule},
        Change::Recipes {..}=>Class::Recipes,Change::Configuration {..}=>Class::Configuration,
        Change::Sources {..}=>Class::Sources,Change::Work {..}=>Class::Work,
        Change::Cleanup {..}=>Class::Cleanup,Change::Groups {..}=>Class::Groups,
        Change::Host {..}=>Class::Host,Change::Control {..}=>Class::Control,
        Change::RegisterInverse {..}=>Class::InverseRegistration,
    }
}
/// Strict whole-record framing also preserves allocation presence. It covers
/// every record kind, including future observers of retained retired entries.
pub open spec fn frame(before:Observation,after:Observation,key:nat)->bool {
    forall|other:nat| other!=key ==> {
        &&& before.records.contains_key(other)==after.records.contains_key(other)
        &&& before.records.contains_key(other) ==> #[trigger] after.records[other]==before.records[other]
    }
}
pub open spec fn stutters(before:Observation,after:Observation)->bool {before==after}

/// Successful operations use the R1 dependent grammar on qualified local
/// allocations. Restoration and rejection keep their exact partial domains.
#[verifier::opaque]
pub open spec fn value_law(before:Map<nat,Record>,after:Map<nat,Record>,step:Step)->bool {
    let event=step.change->Value_event;
    &&& before.contains_key(step.key) && before[step.key] is Object
    &&& after.contains_key(step.key) && after[step.key] is Object
    &&& before[step.key]->Object_source==after[step.key]->Object_source
    &&& access::objects(before).contains_pair(step.key,event.before())
    &&& access::objects(after)==access::objects(before).insert(step.key,event.after())
    &&& match event {
        Event::Forward {..}|Event::Computed {..}=>{
            let run=d::run(alias::library(),alias::node(step.key,alias::event_code(event),alias::event_branch(event)),access::objects(before));
            &&& run.is_some() && run.unwrap().state==access::objects(after)
            &&& run.unwrap().next==alias::event_branch(event).selected(alias::event_outcome(event))
            &&& effect::operation(alias::event_code(event))(access::objects(before)[step.key]).unwrap().outcome==alias::event_outcome(event)
            &&& forall|input:Map<nat,ValueState>| #[trigger] (run.unwrap().undo)(input)==
                if input.contains_key(step.key) && input[step.key]==event.after() {Some(input.insert(step.key,event.before()))} else {None}
        },
        Event::Restore {inverse,before:input,after:output}=>inverse.undo(input)==Some(output),
        Event::Rejected {operation,before:input}=>crate::reversible_value::operation(operation)(input).is_none(),
        Event::Blocked {inverse,before:input}=>inverse.undo(input).is_none(),
        Event::ComputationRejected {code,before:input}=>effect::operation(code)(input).is_none(),
        Event::StaleComputation {expected,before:input}=>expected!=input,
    }
}
/// These are observable owner transitions. Their checked guards and complete
/// records are retained; no arbitrary callback receives a paper stutter law.
#[verifier::opaque]
pub open spec fn record_law(before:Map<nat,Record>,after:Map<nat,Record>,event:Step)->bool {
    match event.change {
        Change::Allocate=>!before.contains_key(event.key) && after.contains_pair(event.key,event.after),
        Change::Value {..}=>value_law(before,after,event),
        Change::Replace=>before[event.key] is Slot && event.after is Slot
            && event.after->Slot_source==before[event.key]->Slot_source
            && before[event.key]->Slot_revision<u64::MAX
            && event.after->Slot_revision==before[event.key]->Slot_revision+1,
        Change::PayloadReplace|Change::PayloadApply|Change::PayloadRestore=>before[event.key] is Payload && event.after is Payload
            && event.after->Payload_source==before[event.key]->Payload_source
            && before[event.key]->Payload_revision<u64::MAX
            && event.after->Payload_revision==before[event.key]->Payload_revision+1,
        Change::PayloadRetire=>before[event.key] is Payload && event.after is RetiredPayload
            && event.after->RetiredPayload_source==before[event.key]->Payload_source
            && event.after->RetiredPayload_revision==before[event.key]->Payload_revision,
        Change::Native {actor,rule}=>before[event.key] is Native && event.after is Native
            && super::native::step(before[event.key]->Native_state,event.after->Native_state,actor,rule)
            && r::labelled_step(before[event.key]->Native_state.control,event.after->Native_state.control,(actor,rule),class(event)==Class::NativeRestart),
        Change::Recipes {event:change}=>before[event.key] is Recipes && event.after is Recipes
            && super::recipes::step(before[event.key]->Recipes_state,event.after->Recipes_state,change),
        Change::Configuration {event:change}=>before[event.key] is Configuration && event.after is Configuration
            && super::configuration::step(before[event.key]->Configuration_state,event.after->Configuration_state,change),
        Change::Sources {event:change}=>before[event.key] is Sources && event.after is Sources
            && super::sources::step(before[event.key]->Sources_state,event.after->Sources_state,change),
        Change::Work {event:change}=>before[event.key] is Work && event.after is Work
            && super::episode::work_step(before[event.key]->Work_state,event.after->Work_state,change),
        Change::Cleanup {event:change}=>before[event.key] is Cleanup && event.after is Cleanup
            && super::episode::cleanup_step(before[event.key]->Cleanup_state,event.after->Cleanup_state,change),
        Change::Groups {event:change}=>before[event.key] is Groups && event.after is Groups
            && super::groups::step(before[event.key]->Groups_state,event.after->Groups_state,change),
        Change::Host {event:change}=>before[event.key] is Host && event.after is Host
            && super::host::step(before[event.key]->Host_state,event.after->Host_state,change),
        Change::Control {event:change}=>before[event.key] is Control && event.after is Control
            && super::control::step(before[event.key]->Control_state,event.after->Control_state,change),
        Change::RegisterInverse {..}=>before[event.key] is Cleanup && event.after is Cleanup
            && super::episode::cleanup_step(before[event.key]->Cleanup_state,event.after->Cleanup_state,super::episode::CleanupChange::Register),
    }
}
#[verifier::opaque]
pub open spec fn classified(frames:Seq<Frame>,index:nat)->bool {
    let before=at(frames,index);let after=at(frames,index+1);let event=frames[index as int].event;
    &&& index<frames.len()
    &&& after.records==before.records.insert(event.key,event.after)
    &&& frame(before,after,event.key)
    &&& record_law(before.records,after.records,event)
    &&& event.change!=Change::Allocate ==> before.records.contains_key(event.key)
        && super::guard(before.records,before.records[event.key],event.change)
    &&& super::pending_step(before.pending,after.pending,event,index)
    &&& event.change is RegisterInverse ==> {
        let write=event.change->RegisterInverse_write;
        &&& write<index && super::forward(frames[write as int].event)
        &&& event.settled.is_some() ==> before.pending.contains_pair(write,frames[write as int].event.key)
    }
    &&& stutters(before,after)==(before.records.contains_pair(event.key,event.after) && before.pending==after.pending)
    &&& class(event)==Class::Rejection ==> stutters(before,after)
    &&& (class(event)==Class::Allocation || class(event)==Class::Forward || class(event)==Class::Replacement || class(event)==Class::PayloadReplacement || class(event)==Class::PayloadForward || class(event)==Class::PayloadRestoration || class(event)==Class::PayloadRetirement
        || class(event)==Class::NativeRule || class(event)==Class::NativeRestart || class(event)==Class::InverseRegistration)
        ==> !stutters(before,after)
}
proof fn value_step(before:Map<nat,Record>,after:Map<nat,Record>,event:Step)
    requires super::step(before,after,event),event.change is Value,
    ensures value_law(before,after,event),
{
    reveal(super::changes);reveal(value_law);
    let value=event.change->Value_event;
    assert(access::objects(after) =~= access::objects(before).insert(event.key,value.after()));
    if value is Forward || value is Computed {alias::managed_step(before,after,event);}
}
proof fn record_step(before:Map<nat,Record>,after:Map<nat,Record>,event:Step)
    requires super::step(before,after,event),
    ensures record_law(before,after,event),
{
    reveal(record_law);reveal(super::changes);
    match event.change {
        Change::Value {..}=>value_step(before,after,event),
        Change::Native {..}=>{reveal(super::native::step);},
        Change::Allocate|Change::Replace|Change::PayloadReplace|Change::PayloadApply|Change::PayloadRestore|Change::PayloadRetire|Change::Recipes {..}|Change::Configuration {..}|Change::Sources {..}
            |Change::Work {..}|Change::Cleanup {..}|Change::Groups {..}|Change::Host {..}|Change::Control {..}|Change::RegisterInverse {..}=>{},
    }
}
proof fn framed_step(before:Observation,after:Observation,event:Step)
    requires super::step(before.records,after.records,event),
    ensures frame(before,after,event.key),
        stutters(before,after)==(before.records.contains_pair(event.key,event.after) && before.pending==after.pending),
{
    if before.records.contains_pair(event.key,event.after) {assert(before.records =~= after.records);}
}
proof fn rejection_stutters(before:Observation,after:Observation,event:Step,index:nat)
    requires super::step(before.records,after.records,event),super::pending_step(before.pending,after.pending,event,index),
        class(event)==Class::Rejection,
    ensures stutters(before,after),
{
    reveal(super::changes);assert(before.records =~= after.records);
}
proof fn registration_cause(frames:Seq<Frame>,index:nat)
    requires super::valid(frames),index<frames.len(),frames[index as int].event.change is RegisterInverse,
    ensures {
        let event=frames[index as int].event;let write=event.change->RegisterInverse_write;
        &&& write<index && super::forward(frames[write as int].event)
        &&& event.settled.is_some() ==> at(frames,index).pending.contains_pair(write,frames[write as int].event.key)
    },
{
    let event=frames[index as int].event;let write=event.change->RegisterInverse_write;
    assert(super::step(super::state_at(frames,index),frames[index as int].state,event));
    assert(super::caused(frames.take(index as int),event));
    assert(super::pending_step(super::pending_at(frames,index),frames[index as int].pending,event,index));
    if event.settled.is_some() {super::pending_since(frames,write,index);}
}
/// Equal scalar contents or unchanged control do not erase the actual depth,
/// slot/native revision, allocation or queue registration from the observation.
proof fn changing_step(before:Observation,after:Observation,event:Step)
    requires super::step(before.records,after.records,event),
        class(event)==Class::Allocation || class(event)==Class::Forward || class(event)==Class::Replacement || class(event)==Class::PayloadReplacement || class(event)==Class::PayloadForward || class(event)==Class::PayloadRestoration || class(event)==Class::PayloadRetirement
            || class(event)==Class::NativeRule || class(event)==Class::NativeRestart || class(event)==Class::InverseRegistration,
    ensures !stutters(before,after),
{
    reveal(super::changes);reveal(super::native::step);
    match event.change {
        Change::Allocate=>{assert(!before.records.contains_key(event.key));},
        Change::Value {event:value}=>{
            assert(value is Forward || value is Computed);
            assert(value.before().depth<value.after().depth);
        },
        Change::Replace|Change::PayloadReplace|Change::PayloadApply|Change::PayloadRestore|Change::PayloadRetire=>{},Change::Native {..}=>{},Change::RegisterInverse {..}=>{},
        _=>{assert(false);},
    }
}
pub proof fn classify_step(frames:Seq<Frame>,index:nat)
    requires super::valid(frames),index<frames.len(),
    ensures classified(frames,index),
{
    let before=at(frames,index);let after=at(frames,index+1);let event=frames[index as int].event;
    assert(super::step(before.records,after.records,event));
    assert(super::pending_step(before.pending,after.pending,event,index));
    record_step(before.records,after.records,event);framed_step(before,after,event);
    if class(event)==Class::Rejection {rejection_stutters(before,after,event,index);}
    if event.change is RegisterInverse {registration_cause(frames,index);}
    if class(event)==Class::Allocation || class(event)==Class::Forward || class(event)==Class::Replacement || class(event)==Class::PayloadReplacement || class(event)==Class::PayloadForward || class(event)==Class::PayloadRestoration || class(event)==Class::PayloadRetirement
        || class(event)==Class::NativeRule || class(event)==Class::NativeRestart || class(event)==Class::InverseRegistration {
        changing_step(before,after,event);
    }
    reveal(classified);
}
#[verifier::opaque]
pub open spec fn history(frames:Seq<Frame>)->bool {
    forall|index:nat| index<frames.len() ==> #[trigger] classified(frames,index)
}
pub proof fn classify_history(frames:Seq<Frame>)
    requires super::valid(frames),ensures history(frames),
{
    reveal(history);
    assert forall|index:nat| index<frames.len() implies #[trigger] classified(frames,index) by {classify_step(frames,index);}
}
impl super::Snapshot {
    /// This proof reads the authenticated production prefix. The caller cannot
    /// replace its initial state, omit interleavings or choose event labels.
    pub proof fn classify(&self)
        requires self.certified(),ensures history(self.events()),
    {self.valid_history();classify_history(self.events());}
    pub proof fn classified_step(&self,index:nat)
        requires self.certified(),index<self.events().len(),
        ensures classified(self.events(),index),
    {self.valid_history();classify_step(self.events(),index);}
    pub proof fn interpreted_trajectory(&self)->(states:Seq<Observation>)
        requires self.certified(),
        ensures states.len()==self.events().len()+1,
            states.first()==(Observation {records:Map::empty(),pending:Map::empty()}),
            states.last()==(Observation {records:self.last(),pending:self.pending()}),
            forall|i:int| 0<=i<states.len() ==> #[trigger] states[i]==at(self.events(),i as nat),
            forall|i:nat| i<self.events().len() ==> #[trigger] classified(self.events(),i),
    {
        self.classify();reveal(history);
        Seq::new(self.events().len()+1,|i:int|at(self.events(),i as nat))
    }
}
impl super::Receipt {
    /// Actual root/Child returns and status observations retain this same
    /// complete classification for their real member prefix.
    pub proof fn classify(&self)
        requires self.wf(),ensures history(self.events()),
    {classify_history(self.events());}
}
} // verus!
