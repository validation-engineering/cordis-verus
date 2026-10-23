//! Derive local restoration coverage from the actual release guard and emitted
//! managed acknowledgements. Raw host confirmations are not restoration evidence.
use super::Event;
#[cfg(verus_keep_ghost)]
use super::{completion, linked, obligations};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::native::runtime::episode::Unload;
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    joint,
    managed::{Action, Owner, Step},
};
use vstd::prelude::*;

verus! {
pub open spec fn registered(end:&Unload,receipt:joint::Receipt,id:usize,token:usize)->bool {
    &&& end.wf() && end.cleanup_checkpoint().is_some() && receipt.wf()
    &&& end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal()
    &&& end.cleanup_checkpoint().unwrap().covers(&receipt)
    &&& joint::groups::recorded(receipt.events(),receipt.events().len(),end.cleanup_link().unwrap().1)
    &&& joint::groups::at(receipt.events(),receipt.events().len(),end.cleanup_link().unwrap().1).queues.contains_key(id)
    &&& receipt.event().change is RegisterInverse && receipt.event().after is Cleanup
    &&& joint::groups::at(receipt.events(),receipt.events().len(),end.cleanup_link().unwrap().1).queues[id]==
        (receipt.event().key,receipt.event().after->Cleanup_state.domain)
    &&& token<receipt.event().after->Cleanup_state.occupied.len() && receipt.event().after->Cleanup_state.occupied[token as int]
}
pub open spec fn acknowledges<A,R,T:?Sized,M,X>(event:Event<A,R,T,M,X>,end:joint::Receipt,at:nat,inverse:obligations::Inverse<T>)->bool {
    match event {
        Event::Managed(d)=>event.source() && event.inverse()==inverse && d.queue_link().is_some()
            && d.acknowledgement().is_some() && end.covers(&d.acknowledgement().unwrap()) && d.acknowledgement().unwrap().at()==at,
        _=>false,
    }
}
/// The still-explicit event-source coverage condition is separate from the
/// registration ownership now exported by actual managed execution.
pub open spec fn emitted<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,end:&Unload,receipt:joint::Receipt,token:usize,inverse:obligations::Inverse<T>)->bool {
    forall|at:nat|receipt.events().len()<=at<end.at()
        && joint::episode::release::completes(#[trigger] end.checkpoint().events()[at as int].event,receipt.event().key,token) ==>
            exists|i:int|0<=i<events.len() && #[trigger] acknowledges(events[i],end.checkpoint(),at,inverse)
}
/// Completeness is checked by actual queue/slot/Journal identities. It does
/// not require any event's restoration to be successful; the guard derives it.
#[verifier::opaque]
pub open spec fn covered<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,end:&Unload,receipt:joint::Receipt,id:usize,token:usize,inverse:obligations::Inverse<T>)->bool {
    registered(end,receipt,id,token) && emitted(events,end,receipt,token,inverse)
}
impl<A,R,T:?Sized,M,X> Event<A,R,T,M,X> {
    pub(crate) proof fn completed_restoration(&self,end:joint::Receipt,at:nat,key:nat,token:usize,inverse:obligations::Inverse<T>)
        requires end.wf(),at<end.events().len(),acknowledges(*self,end,at,inverse),
            joint::episode::release::completes(end.events()[at as int].event,key,token),
        ensures completion::restores(*self,inverse),
    {
        match self {
            Self::Managed(d)=>{d.acknowledgement_records();end.included(&d.acknowledgement().unwrap());},_=>{},
        }
    }
}
pub proof fn restored_before_unload<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,end:&Unload,receipt:joint::Receipt,id:usize,token:usize,inverse:obligations::Inverse<T>)
    requires covered(events,end,receipt,id,token,inverse),
    ensures completion::later(events,inverse,0),
{
    reveal(covered);
    let at=end.registered_token_completed(&receipt,id,token);end.facts();
    let i=choose|i:int|0<=i<events.len() && #[trigger] acknowledges(events[i],end.checkpoint(),at,inverse);
    events[i].completed_restoration(end.checkpoint(),at,receipt.event().key,token,inverse);
}
/// Locate the actual restoration required by a terminal registration and
/// prove its write precedes the successful native Unload.
#[verifier::spinoff_prover]
pub proof fn restoration_before_unload<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,end:&Unload,receipt:joint::Receipt,id:usize,token:usize,inverse:obligations::Inverse<T>)->(i:int)
    requires covered(events,end,receipt,id,token,inverse),inverse.address.journal==end.checkpoint().journal(),
    ensures 0<=i<events.len(),events[i] is Managed,completion::restores(events[i],inverse),end.checkpoint().covers(&events[i].checkpoint()),
{
    hide(joint::valid);hide(joint::step);reveal(covered);
    let at=end.registered_token_completed(&receipt,id,token);end.facts();
    let i=choose|i:int|0<=i<events.len() && #[trigger] acknowledges(events[i],end.checkpoint(),at,inverse);
    let event=events[i];event.completed_restoration(end.checkpoint(),at,receipt.event().key,token,inverse);
    let d=event->Managed_0;d.acknowledgement_records();event.recorded_output();
    match d {
        crate::cleanup_groups::payload::Dispatch::Payload(c)=>{
            reveal(crate::reversible_value::payload::restoration::attempt::protocol::Evidence::certified);c.evidence().attempt().boundaries();
        },_=>{},
    }
    assert(d.acknowledgement().unwrap().covers(&event.checkpoint()));
    end.checkpoint().cover_through(&d.acknowledgement().unwrap(),&event.checkpoint());i
}
proof fn encoded_settled<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,slots:Seq<Option<Action<A,R,T,M,X>>>,events:Seq<Event<A,R,T,M,X>>,end:&Unload,id:usize)
    requires steps.len()==slots.len(),forall|i:int|0<=i<steps.len() ==> {
        let step=#[trigger] steps[i];
        step.recorded_values() && step.in_slot(slots[i]) && step.insertion().is_some()
            && covered(events,end,step.insertion().unwrap(),id,step.token(),step.forward_inverse().inverse())
    },
    ensures forall|i:int|0<=i<super::encode(slots).len() && (#[trigger] super::encode(slots)[i]).is_some() ==>
        completion::later(events,super::encode(slots)[i].unwrap(),0),
{
    hide(completion::later);hide(super::inverse_action);hide(super::Forward::inverse);
    assert forall|i:int|0<=i<super::encode(slots).len() && (#[trigger] super::encode(slots)[i]).is_some() implies
        completion::later(events,super::encode(slots)[i].unwrap(),0) by {
        let step=steps[i];step.source_inverse(slots[i]);
        restored_before_unload(events,end,step.insertion().unwrap(),id,step.token(),step.forward_inverse().inverse());
    }
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    /// Each source is the receipt of this actual step's inverse insertion.
    /// An unrelated queue or an opaque callback acknowledgement does not cover it.
    pub open spec fn cleanup_covered<A,R,M,X>(&self,events:Seq<Event<A,R,T,M,X>>,end:&Unload,id:usize)->bool {
        self.result.is_ok() && forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> {
            let step=#[trigger] self.result->Ok_0.steps@[i];
            step.insertion().is_some() && covered(events,end,step.insertion().unwrap(),id,step.token(),step.forward_inverse().inverse())
        }
    }
    pub proof fn cleanup_settled<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,events:Seq<Event<A,R,T,M,X>>,end:&Unload)
        requires self.result.is_ok(),self.result->Ok_0.recovery_history(),super::super::retained(self.result->Ok_0.steps@,owner,id,offset),
            self.cleanup_covered(events,end,id),completion::foreign_settled(events,self.return_values().dom()),
        ensures completion::settled(events,self.obligations(owner,id,offset),self.return_values().dom()),
    {
        hide(RegisteredReport::return_values);hide(Step::recorded_values);hide(Step::in_slot);
        self.result->Ok_0.inverse_sources();
        let steps=self.result->Ok_0.steps@;let slots=owner.cleanup_state().queues()[id].slots();
        let suffix=slots.subrange(offset as int,slots.len() as int);
        assert forall|i:int|0<=i<steps.len() implies {
            let step=#[trigger] steps[i];
            step.recorded_values() && step.in_slot(suffix[i]) && step.insertion().is_some()
                && covered(events,end,step.insertion().unwrap(),id,step.token(),step.forward_inverse().inverse())
        } by {assert(suffix[i]==slots[offset+i]);}
        encoded_settled(steps,suffix,events,end,id);
    }
    /// Local successful restores follow from actual release and complete
    /// acknowledgement coverage. Only foreign closure remains a separate
    /// finite-history condition: native release does not schedule foreign code.
    pub proof fn unload_recovers_from_cleanup<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,events:Seq<Event<A,R,T,M,X>>,end:&Unload)
        requires owner.wf(),owner.cleanup_state().live(id),self.start().owner().owns(&owner),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner,id,offset),super::super::retained(self.result->Ok_0.steps@,owner,id,offset),
            linked(events,self.completion(),self.return_values(),self.obligations(owner,id,offset)),self.unload_source(events,end),
            self.cleanup_covered(events,end,id),completion::foreign_settled(events,self.return_values().dom()),
        ensures self.unload_values(events,end)==self.begin_values(),
            self.start().recorded(end.checkpoint().events()),end.recorded(end.checkpoint().events()),self.start().at()<end.at(),
    {
        self.cleanup_settled(owner,id,offset,events,end);
        self.unload_recovers_begin(owner,id,offset,events,end);
    }
}
}

#[path = "managed_release_membership.rs"]
pub mod membership;
