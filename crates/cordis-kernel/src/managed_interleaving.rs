//! A source-linked projected history including foreign managed writes,
//! blocked attempts, foreign restoration and successful retries.
use super::{cleanup_path::Turn, root::RegisteredReport, Report, Step};
#[cfg(verus_keep_ghost)]
use super::{semantics::Value, trace, Action, Owner, ResultStep};
use crate::reversible_value::{self as scalar, effect::ScalarEffect, joint, payload};
#[cfg(verus_keep_ghost)]
use crate::{
    cleanup_groups::payload::{self as cleanup, recovery as r},
    lifecycle_state::registration::shared_child::ChildCleanup,
    reversible_value::service_composition::Address,
};
use vstd::prelude::*;

#[path = "managed_interleaving_completion.rs"]
pub mod completion;
#[path = "managed_interleaving_endpoint.rs"]
pub mod endpoint;
#[path = "managed_cleanup_history.rs"]
pub mod history;
#[path = "recovery_obligations.rs"]
pub mod obligations;
#[path = "managed_release_path.rs"]
pub mod release;
#[path = "managed_value_sources.rs"]
pub mod sources;

verus! {
/// Both variants are actual captured inverses returned by running storage.
pub ghost enum Forward<T:?Sized> {Scalar(scalar::Inverse),Payload(payload::restoration::Inverse<T>)}
impl<T:?Sized> Forward<T> {
    pub open spec fn source(&self)->bool {match self {Self::Scalar(i)=>i.recorded(),Self::Payload(i)=>i.wf()}}
    pub open spec fn write(&self)->joint::Receipt {match self {Self::Scalar(i)=>i.origin(),Self::Payload(i)=>i.after().commit}}
    pub open spec fn inverse(&self)->obligations::Inverse<T> {
        match self {
            Self::Scalar(i)=>obligations::Inverse {address:Address {journal:i.target().journal_spec(),key:i.target().object().key},before:Value::Scalar(i.state().before),after:Value::Scalar(i.state().after),origin:i.origin().at()},
            Self::Payload(i)=>obligations::Inverse {address:Address {journal:i.owner().journal_spec(),key:i.owner().key()},before:Value::Payload(i.before().state()),after:Value::Payload(i.after().state()),origin:i.after().commit.at()},
        }
    }
    pub proof fn facts(&self)
        requires self.source(),
        ensures self.inverse().valid(),self.write().wf(),self.write().journal()==self.inverse().address.journal,self.write().event().key==self.inverse().address.key,
    {
        match self {Self::Scalar(i)=>{},Self::Payload(i)=>{i.provenance();i.source_history();}}
    }
}
pub open spec fn forward_action<A,R,T:?Sized,M,X>(action:Action<A,R,T,M,X>)->Forward<T> {
    match action {ChildCleanup::Value(i)=>Forward::Scalar(i),ChildCleanup::Callback(cleanup::Cleanup::Payload {inverse,..})=>Forward::Payload(inverse),_=>arbitrary()}
}
pub open spec fn inverse_action<A,R,T:?Sized,M,X>(action:Action<A,R,T,M,X>)->obligations::Inverse<T> {forward_action(action).inverse()}

/// Raw restore entry points expose exactly these erased attempt receipts. The
/// legacy restore methods delegate to them, so this includes real foreign code.
pub ghost enum Attempt<T:?Sized> {Scalar {inverse:scalar::Inverse,receipt:joint::Receipt},Payload(payload::restoration::attempt::Attempt<T>)}
impl<T:?Sized> Attempt<T> {
    pub open spec fn succeeded(&self)->bool {
        match self {Self::Scalar {receipt,..}=>receipt.event().change is Value && receipt.event().change->Value_event is Restore,Self::Payload(a)=>a.result().is_ok()}
    }
    pub open spec fn source(&self)->bool {
        match self {Self::Scalar {inverse,receipt}=>scalar::restoration::attempted(receipt,*inverse,self.succeeded()),Self::Payload(a)=>a.wf()}
    }
    pub open spec fn forward(&self)->Forward<T> {match self {Self::Scalar {inverse,..}=>Forward::Scalar(*inverse),Self::Payload(a)=>Forward::Payload(a.inverse())}}
    pub open spec fn observed(&self)->Option<Value<T>> {
        match self {Self::Scalar {receipt,..}=>Some(Value::Scalar(receipt.event().change->Value_event.before())),Self::Payload(a)=>match a.read().value() {Some(v)=>Some(Value::Payload(v.state())),None=>None}}
    }
    pub open spec fn landed(&self)->Option<Value<T>> {
        match self {Self::Scalar {receipt,..}=>Some(Value::Scalar(receipt.event().change->Value_event.after())),Self::Payload(a)=>match a.result() {Ok(v)=>Some(Value::Payload(v.after().state())),Err(_)=>self.observed()}}
    }
    pub open spec fn checkpoint(&self)->joint::Receipt {match self {Self::Scalar {receipt,..}=>*receipt,Self::Payload(a)=>a.endpoint()}}
    pub open spec fn read_cut(&self)->nat {match self {Self::Scalar {receipt,..}=>receipt.at(),Self::Payload(a)=>a.read().checkpoint().events().len()}}
    pub proof fn facts(&self)
        requires self.source(),
        ensures self.checkpoint().wf(),self.read_cut()<=self.checkpoint().events().len(),
            self.succeeded()==(self.observed()==Some(self.forward().inverse().after)),
            self.landed()==if self.succeeded() {Some(self.forward().inverse().before)} else {self.observed()},
    {
        match self {Self::Scalar {..}=>{},Self::Payload(a)=>{a.facts();a.strict_domain();a.boundaries();}}
    }
}
pub ghost enum Event<A,R,T:?Sized,M,X> {Forward(Forward<T>),Managed(Turn<A,R,T,M,X>),Restore(Attempt<T>),Produced(sources::produced::Produced<T>)}
impl<A,R,T:?Sized,M,X> Event<A,R,T,M,X> {
    pub open spec fn source(&self)->bool {
        match self {Self::Forward(f)=>f.source(),Self::Managed(d)=>d.authentic() && d.managed(),Self::Restore(a)=>a.source(),Self::Produced(e)=>e.wf()}
    }
    pub open spec fn forward(&self)->bool {self is Forward || self is Produced && self->Produced_0.forward()}
    pub open spec fn inverse(&self)->obligations::Inverse<T> {
        match self {Self::Forward(f)=>f.inverse(),Self::Managed(d)=>inverse_action(d.before_queue().slots()[d.ticket().token as int].unwrap()),Self::Restore(a)=>a.forward().inverse(),Self::Produced(e)=>e.inverse()}
    }
    pub open spec fn succeeded(&self)->bool {match self {Self::Forward(_)=>true,Self::Managed(d)=>d.succeeded(),Self::Restore(a)=>a.succeeded(),Self::Produced(_)=>true}}
    pub open spec fn observed(&self)->Option<Value<T>> {match self {Self::Forward(f)=>Some(f.inverse().before),Self::Managed(d)=>d.observed(),Self::Restore(a)=>a.observed(),Self::Produced(e)=>Some(e.before())}}
    pub open spec fn landed(&self)->Option<Value<T>> {match self {Self::Forward(f)=>Some(f.inverse().after),Self::Managed(d)=>d.landed(),Self::Restore(a)=>a.landed(),Self::Produced(e)=>Some(e.after())}}
    pub open spec fn checkpoint(&self)->joint::Receipt {match self {Self::Forward(f)=>f.write(),Self::Managed(d)=>d.checkpoint(),Self::Restore(a)=>a.checkpoint(),Self::Produced(e)=>e.receipt}}
    pub open spec fn read_cut(&self)->nat {match self {Self::Forward(f)=>f.write().at(),Self::Managed(d)=>d.read_cut(),Self::Restore(a)=>a.read_cut(),Self::Produced(e)=>e.receipt.at()}}
    pub proof fn facts(&self)
        requires self.source(),
        ensures self.checkpoint().wf(),self.read_cut()<=self.checkpoint().events().len(),
            self.forward() ==> self.inverse().valid() && self.observed()==Some(self.inverse().before) && self.landed()==Some(self.inverse().after),
            !self.forward() ==> self.succeeded()==(self.observed()==Some(self.inverse().after))
                && self.landed()==if self.succeeded() {Some(self.inverse().before)} else {self.observed()},
    {
        match self {
            Self::Forward(f)=>f.facts(),Self::Restore(a)=>a.facts(),Self::Produced(e)=>e.facts(),Self::Managed(d)=>{
                reveal(cleanup::Dispatch::recovery);
                let action=d.before_queue().slots()[d.ticket().token as int].unwrap();
                assert(r::managed(action));
                assert(r::expected(action)==self.inverse().after && r::original(action)==self.inverse().before);
            },
        }
    }
    pub open spec fn observes(&self,heap:Map<Address,Value<T>>)->bool {
        self.observed()==if heap.contains_key(self.inverse().address) {Some(heap[self.inverse().address])} else {None}
    }
    pub open spec fn apply(&self,heap:Map<Address,Value<T>>,keys:Set<Address>)->Map<Address,Value<T>> {
        let key=self.inverse().address;
        if !keys.contains(key) {heap} else {match self.landed() {Some(v)=>heap.insert(key,v),None=>heap.remove(key)}}
    }
}
pub open spec fn slot_of<T:?Sized>(slots:Seq<Option<obligations::Inverse<T>>>,inverse:obligations::Inverse<T>)->int {
    choose|i:int|0<=i<slots.len() && #[trigger] slots[i]==Some(inverse)
}
pub open spec fn contains<T:?Sized>(slots:Seq<Option<obligations::Inverse<T>>>,inverse:obligations::Inverse<T>)->bool {
    exists|i:int|0<=i<slots.len() && #[trigger] slots[i]==Some(inverse)
}
pub open spec fn outstanding<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,initial:Seq<Option<obligations::Inverse<T>>>,keys:Set<Address>,n:nat)->Seq<Option<obligations::Inverse<T>>>
    decreases n,
{
    if n==0 {initial} else {
        let previous=outstanding(events,initial,keys,(n-1) as nat);let event=events[n-1];let inv=event.inverse();
        if !keys.contains(inv.address) {previous} else if event.forward() {previous.push(Some(inv))}
        else if event.succeeded() {previous.update(slot_of(previous,inv),None)} else {previous}
    }
}
pub open spec fn values<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,initial:Map<Address,Value<T>>,n:nat)->Map<Address,Value<T>>
    decreases n,
{if n==0 {initial} else {events[n-1].apply(values(events,initial,(n-1) as nat),initial.dom())}}
/// These are actual receipt/order/read conditions. A successful restoration
/// must name an inverse retained by the prefix, not a caller-chosen expected map.
pub open spec fn linked<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,initial:Map<Address,Value<T>>,slots:Seq<Option<obligations::Inverse<T>>>)->bool {
    start.wf() && forall|i:int|0<=i<events.len() ==> {
        let event=#[trigger] events[i];let checkpoint=event.checkpoint();let previous=if i==0 {start} else {events[i-1].checkpoint()};
        &&& event.source() && checkpoint.journal()==start.journal() && checkpoint.covers(&previous)
        &&& previous.events().len()<=event.read_cut()
        &&& initial.contains_key(event.inverse().address) ==> event.observes(values(events,initial,i as nat))
        &&& initial.contains_key(event.inverse().address) && !event.forward() && event.succeeded() ==>
            contains(outstanding(events,slots,initial.dom(),i as nat),event.inverse())
    }
}
proof fn prefix<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,initial:Map<Address,Value<T>>,slots:Seq<Option<obligations::Inverse<T>>>,n:nat)
    requires linked(events,start,initial,slots),obligations::valid(slots),obligations::recover(slots,initial).is_some(),n<=events.len(),
    ensures obligations::valid(outstanding(events,slots,initial.dom(),n)),
        obligations::recover(outstanding(events,slots,initial.dom(),n),values(events,initial,n))==obligations::recover(slots,initial),
        values(events,initial,n).dom()==initial.dom(),
    decreases n,
{
    if n>0 {
        prefix(events,start,initial,slots,(n-1) as nat);
        let event=events[n-1];event.facts();let inv=event.inverse();
        let before=outstanding(events,slots,initial.dom(),(n-1) as nat);let heap=values(events,initial,(n-1) as nat);
        if initial.contains_key(inv.address) {
            if event.forward() {
                assert(inv.forward(heap).is_some());obligations::forward(before,inv,heap);
                assert(obligations::valid(before.push(Some(inv)))) by {
                    assert forall|i:int|0<=i<before.push(Some(inv)).len() && (#[trigger] before.push(Some(inv))[i]).is_some() implies before.push(Some(inv))[i].unwrap().valid() by {
                        if i<before.len() {assert(before[i].unwrap().valid());}
                    }
                }
            } else if event.succeeded() {
                let i=slot_of(before,inv);assert(0<=i<before.len() && before[i]==Some(inv));
                assert(inv.undo(heap).is_some());obligations::consume(before,heap,i);
            } else {assert(event.apply(heap,initial.dom()) =~= heap);}
        }
    }
}
/// Encode the actual retained slots; callbacks are excluded by the actual
/// managed report relation, rather than silently assumed to be reversible.
pub open spec fn encode<A,R,T:?Sized,M,X>(slots:Seq<Option<Action<A,R,T,M,X>>>)->Seq<Option<obligations::Inverse<T>>> {
    slots.map(|_:int,slot:Option<Action<A,R,T,M,X>>|match slot {Some(a)=>Some(inverse_action(a)),None=>None})
}
proof fn queue_defined<A,R,T:?Sized,M,X>(slots:Seq<Option<Action<A,R,T,M,X>>>,heap:Map<Address,Value<T>>)
    requires trace::queued_undo(slots,heap).is_some(),
    ensures obligations::recover(encode(slots),heap)==trace::queued_undo(slots,heap),
    decreases slots.len(),
{
    if slots.len()>0 {
        let action=slots.last().unwrap();assert(r::managed(action));
        assert(inverse_action(action).undo(heap)==trace::undo_action(action,heap));
        queue_defined(slots.drop_last(),inverse_action(action).undo(heap).unwrap());
        assert(encode(slots).drop_last() =~= encode(slots.drop_last()));
    }
}
impl<T:?Sized> Step<T> {
    pub open spec fn forward_inverse(&self)->Forward<T> {match self.result {ResultStep::Scalar {inverse,..}=>Forward::Scalar(inverse@),ResultStep::Payload(a)=>Forward::Payload(a.inverse())}}
    pub proof fn source_inverse<A,R,M,X>(&self,slot:Option<Action<A,R,T,M,X>>)
        requires self.recorded_values(),self.in_slot(slot),
        ensures r::managed(slot.unwrap()),self.forward_inverse().source(),inverse_action(slot.unwrap())==self.forward_inverse().inverse(),inverse_action(slot.unwrap()).valid(),
    {self.forward_inverse().facts();}
}
proof fn encoded_valid<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,slots:Seq<Option<Action<A,R,T,M,X>>>)
    requires steps.len()==slots.len(),forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).recorded_values() && steps[i].in_slot(slots[i]),
    ensures obligations::valid(encode(slots)),
{
    hide(inverse_action);hide(Forward::inverse);
    assert forall|i:int|0<=i<encode(slots).len() && (#[trigger] encode(slots)[i]).is_some() implies encode(slots)[i].unwrap().valid() by {
        steps[i].source_inverse(slots[i]);
    }
}
impl<T:?Sized> Report<T> {
    proof fn inverse_sources(&self)
        requires self.recovery_history(),
        ensures forall|i:int|0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).recorded_values(),
    {reveal(Report::recovery_history);}
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    pub open spec fn obligations<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat)->Seq<Option<obligations::Inverse<T>>> {
        let slots=owner.cleanup_state().queues()[id].slots();encode(slots.subrange(offset as int,slots.len() as int))
    }
    proof fn initial<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat)
        requires owner.wf(),owner.cleanup_state().live(id),self.endpoint_source(),self.retained_recovery(owner,id,offset),
            self.result->Ok_0.recovery_history(),super::retained(self.result->Ok_0.steps@,owner,id,offset),
        ensures obligations::valid(self.obligations(owner,id,offset)),
            obligations::recover(self.obligations(owner,id,offset),self.return_values())==Some(self.begin_values()),
    {
        hide(joint::valid);hide(joint::step);hide(obligations::recover);hide(trace::queued_undo);
        self.recover_begin(owner,id,offset);self.result->Ok_0.inverse_sources();
        let slots=owner.cleanup_state().queues()[id].slots().subrange(offset as int,owner.cleanup_state().queues()[id].slots().len() as int);
        queue_defined(slots,self.return_values());
        encoded_valid(self.result->Ok_0.steps@,slots);
    }
    /// Foreign writes append their actual inverses; blocked attempts stutter;
    /// enabled restores remove their actual inverse, even across independent
    /// allocations. The proof derives the needed ordering from semantic depth.
    pub proof fn interleaved_progress<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,events:Seq<Event<A,R,T,M,X>>)
        requires owner.wf(),owner.cleanup_state().live(id),self.endpoint_source(),self.retained_recovery(owner,id,offset),
            self.result->Ok_0.recovery_history(),super::retained(self.result->Ok_0.steps@,owner,id,offset),
            linked(events,self.completion(),self.return_values(),self.obligations(owner,id,offset)),
        ensures obligations::recover(outstanding(events,self.obligations(owner,id,offset),self.return_values().dom(),events.len()),values(events,self.return_values(),events.len()))==Some(self.begin_values()),
    {
        self.initial(owner,id,offset);prefix(events,self.completion(),self.return_values(),self.obligations(owner,id,offset),events.len());
    }
    pub proof fn interleaved_recovers_begin<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,events:Seq<Event<A,R,T,M,X>>)
        requires owner.wf(),owner.cleanup_state().live(id),self.endpoint_source(),self.retained_recovery(owner,id,offset),
            self.result->Ok_0.recovery_history(),super::retained(self.result->Ok_0.steps@,owner,id,offset),
            linked(events,self.completion(),self.return_values(),self.obligations(owner,id,offset)),
            forall|i:int|0<=i<outstanding(events,self.obligations(owner,id,offset),self.return_values().dom(),events.len()).len() ==>
                (#[trigger] outstanding(events,self.obligations(owner,id,offset),self.return_values().dom(),events.len())[i]).is_none(),
        ensures values(events,self.return_values(),events.len())==self.begin_values(),
    {
        self.interleaved_progress(owner,id,offset,events);
        obligations::empty(outstanding(events,self.obligations(owner,id,offset),self.return_values().dom(),events.len()),values(events,self.return_values(),events.len()));
    }
}
}
