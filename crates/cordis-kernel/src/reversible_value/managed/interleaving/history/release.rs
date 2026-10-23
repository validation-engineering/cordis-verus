//! Construct complete local acknowledgement coverage from a checked slot path
//! and the actual release guard. No supplied list of successful tokens is used.
use super::History;
#[cfg(verus_keep_ghost)]
use super::{consumed, Action};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::native::runtime::episode::Unload;
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::{
    cleanup_groups::{drained, payload::recovery as cleanup},
    cleanup_queue::CleanupQueue,
    reversible_value::{
        joint,
        managed::{
            interleaving::{self as trajectory, release},
            Owner, Step,
        },
    },
};
use vstd::prelude::*;

verus! {
impl<A,R,T:?Sized,M,X> History<A,R,T,M,X> {
    pub proof fn drained_slots(&self,queue:CleanupQueue<Action<A,R,T,M,X>>)
        requires self.wf(),self.matches(queue),drained(queue),
        ensures forall|token:int|0<=token<self.current().len() ==> (#[trigger] self.current()[token]).is_none(),
    {queue.empty_payloads();}
    pub proof fn consuming_index(&self,token:int)->(i:int)
        requires self.wf(),0<=token<self.initial().len(),self.initial()[token].is_some(),cleanup::managed(self.initial()[token].unwrap()),self.current()[token].is_none(),
        ensures consumed(self.events(),self.receipts(),self.link(),token,self.initial()[token].unwrap(),i),
    {
        self.extent();self.conservation(token);
        choose|i:int|#[trigger] consumed(self.events(),self.receipts(),self.link(),token,self.initial()[token].unwrap(),i)
    }
    /// Iterate over the finite actual report outside a quantified proof block:
    /// each comparison borrows persistent tracked witnesses from the collector.
    proof fn emitted_prefix(tracked &self,tracked end:&Unload,steps:Seq<Step<T>>,id:usize,count:nat)
        requires self.wf(),count<=steps.len(),
            forall|i:int|0<=i<count ==> {
                let step=#[trigger] steps[i];
                step.recorded_values() && step.token()<self.initial().len() && step.in_slot(self.initial()[step.token() as int])
                    && self.current()[step.token() as int].is_none() && step.inserted_into(self.link())
                    && step.insertion().is_some() && release::registered(end,step.insertion().unwrap(),id,step.token())
            },
        ensures forall|i:int|0<=i<count ==> {
            let step=#[trigger] steps[i];
            step.insertion().is_some() && release::emitted(self.events(),end,step.insertion().unwrap(),step.token(),step.forward_inverse().inverse())
        },
        decreases count,
    {
        hide(joint::valid);hide(joint::step);hide(Step::recorded_values);hide(Step::in_slot);
        hide(release::emitted);hide(trajectory::inverse_action);hide(trajectory::Forward::inverse);
        if count>0 {
            self.emitted_prefix(end,steps,id,(count-1) as nat);
            let step=steps[count-1];step.source_inverse(self.initial()[step.token() as int]);
            reveal(Step::in_slot);assert(self.initial()[step.token() as int].is_some());
            self.emitted(end,step.insertion().unwrap(),id,step.token());
        }
    }
    /// Compare the actual persistent receipts, then use token non-reuse to
    /// identify the recorded managed acknowledgement with the release-required
    /// completion. This also derives that acknowledgement precedes Unload.
    pub proof fn emitted(tracked &self,tracked end:&Unload,registration:joint::Receipt,id:usize,token:usize)
        requires self.wf(),self.link().is_some(),release::registered(end,registration,id,token),
            self.link()==Some((registration.journal(),registration.event().key)),
            token<self.initial().len(),self.initial()[token as int].is_some(),cleanup::managed(self.initial()[token as int].unwrap()),self.current()[token as int].is_none(),
        ensures release::emitted(self.events(),end,registration,token,trajectory::inverse_action(self.initial()[token as int].unwrap())),
    {
        hide(joint::valid);hide(joint::step);
        let i=self.consuming_index(token as int);let event=self.events()[i];let dispatch=event->Managed_0;
        end.facts();dispatch.acknowledgement_records();dispatch.consuming_acknowledgement();
        let tracked acknowledgement=self.receipts.tracked_borrow(i);let tracked endpoint=end.receipt();
        endpoint.compare(acknowledgement);
        let cut=end.registered_token_completed(&registration,id,token);let key=registration.event().key;
        let at=acknowledgement.at();
        if endpoint.covers(acknowledgement) {
            endpoint.included(acknowledgement);
            joint::episode::release::unique_consumption(endpoint.events(),at,cut,key,token);
        } else {
            assert(acknowledgement.covers(&endpoint));
            assert(acknowledgement.events()[cut as int].event==endpoint.events()[cut as int].event);
            joint::episode::release::unique_consumption(acknowledgement.events(),at,cut,key,token);
            assert(false);
        }
        assert(endpoint.covers(acknowledgement));assert(at==cut);
        end.checkpoint().cover_through(&end.cleanup_checkpoint().unwrap(),&registration);
        crate::reversible_value::managed::recovery::frame_update(registration.events(),registration.at());
        assert(joint::state_at(endpoint.events(),registration.events().len())==joint::state_at(registration.events(),registration.events().len()));
        assert forall|other:nat|registration.events().len()<=other<end.at()
            && joint::episode::release::completes(#[trigger] end.checkpoint().events()[other as int].event,key,token) implies
                exists|j:int|0<=j<self.events().len() && #[trigger] release::acknowledges(self.events()[j],end.checkpoint(),other,trajectory::inverse_action(self.initial()[token as int].unwrap())) by {
            joint::episode::release::bound_between(endpoint.events(),registration.events().len(),other+1,key,token);
            crate::reversible_value::managed::recovery::frame_update(endpoint.events(),other);
            joint::episode::release::unique_consumption(endpoint.events(),at,other,key,token);
            assert(release::acknowledges(self.events()[i],end.checkpoint(),other,trajectory::inverse_action(self.initial()[token as int].unwrap())));
        }
    }
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    pub proof fn emitted_from_history<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,tracked history:&History<A,R,T,M,X>,terminal:CleanupQueue<Action<A,R,T,M,X>>,tracked end:&Unload)
        requires owner.wf(),owner.cleanup_state().live(id),self.result.is_ok(),
            crate::reversible_value::managed::retained(self.result->Ok_0.steps@,owner,id,offset),self.result->Ok_0.recovery_history(),
            self.result->Ok_0.queued_sources(owner.cleanup_state().queues()[id].link()),
            self.result->Ok_0.registered(end.cleanup_link(),id),self.completed(),self.effects_before_return(),self.result->Ok_0.witnessed(),
            end.wf(),end.cleanup_checkpoint().is_some(),end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal(),end.checkpoint().covers(&self.completion()),
            forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> (#[trigger] self.result->Ok_0.steps@[i]).write().journal()==self.completion().journal(),
            history.wf(),history.starts_with(owner.cleanup_state().queues()[id].slots()),history.link()==owner.cleanup_state().queues()[id].link(),history.matches(terminal),drained(terminal),
        ensures self.cleanup_emitted(history.events(),end),
    {
        hide(joint::valid);hide(joint::step);hide(Step::recorded_values);hide(Step::in_slot);
        hide(release::emitted);hide(trajectory::inverse_action);hide(trajectory::Forward::inverse);
        self.registered_sources(end,id);history.drained_slots(terminal);history.extent();self.result->Ok_0.inverse_sources();
        let steps=self.result->Ok_0.steps@;
        assert forall|token:int|0<=token<owner.cleanup_state().queues()[id].slots().len() implies history.initial()[token]==(#[trigger] owner.cleanup_state().queues()[id].slots()[token]) by {}
        assert forall|i:int|0<=i<steps.len() implies {
            let step=#[trigger] steps[i];
            step.recorded_values() && step.token()<history.initial().len() && step.in_slot(history.initial()[step.token() as int])
                && history.current()[step.token() as int].is_none() && step.inserted_into(history.link())
                && step.insertion().is_some() && release::registered(end,step.insertion().unwrap(),id,step.token())
        } by {}
        history.emitted_prefix(end,steps,id,steps.len());
    }
    /// Compose the actual recorded dispatcher path with the actual Unload.
    /// Neither local success nor a list covering every Complete is supplied.
    /// Foreign closure and value-read/quiet-tail conditions remain explicit.
    pub proof fn unload_recovers_from_history<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,
        tracked history:&History<A,R,T,M,X>,terminal:CleanupQueue<Action<A,R,T,M,X>>,tracked end:&Unload)
        requires owner.wf(),owner.cleanup_state().live(id),self.start().owner().owns(&owner),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner,id,offset),crate::reversible_value::managed::retained(self.result->Ok_0.steps@,owner,id,offset),
            trajectory::linked(history.events(),self.completion(),self.return_values(),self.obligations(owner,id,offset)),self.unload_source(history.events(),end),
            self.result->Ok_0.registered(owner.cleanup_state().link(),id),end.cleanup_link()==owner.cleanup_state().link(),
            self.result->Ok_0.queued_sources(owner.cleanup_state().queues()[id].link()),
            end.cleanup_checkpoint().is_some(),end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal(),
            history.wf(),history.starts_with(owner.cleanup_state().queues()[id].slots()),history.link()==owner.cleanup_state().queues()[id].link(),history.matches(terminal),drained(terminal),
            trajectory::completion::foreign_settled(history.events(),self.return_values().dom()),
        ensures self.unload_values(history.events(),end)==self.begin_values(),
            self.start().recorded(end.checkpoint().events()),end.recorded(end.checkpoint().events()),self.start().at()<end.at(),
    {
        self.emitted_from_history(owner,id,offset,history,terminal,end);
        self.unload_recovers_registered(owner,id,offset,history.events(),end);
    }

    /// Consume the bundle returned by the ordinary production release path.
    /// Its actual guard supplies all_drained and the pre-release queue map;
    /// callers do not assemble a terminal queue or assert its drain status.
    pub proof fn unload_recovers_from_release<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,
        tracked history:&History<A,R,T,M,X>,
        tracked observation:&crate::lifecycle_state::native::runtime::ReleaseObservation<crate::reversible_value::managed::Slot<T,M>,Action<A,R,T,M,X>>)
        requires crate::lifecycle_state::native::runtime::released(*observation),
            owner.wf(),owner.cleanup_state().live(id),self.start().owner().owns(&owner),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner,id,offset),crate::reversible_value::managed::retained(self.result->Ok_0.steps@,owner,id,offset),
            trajectory::linked(history.events(),self.completion(),self.return_values(),self.obligations(owner,id,offset)),self.unload_source(history.events(),&observation.1@.unwrap()),
            self.result->Ok_0.registered(owner.cleanup_state().link(),id),observation.1@.unwrap().cleanup_link()==owner.cleanup_state().link(),
            self.result->Ok_0.queued_sources(owner.cleanup_state().queues()[id].link()),
            observation.1@.unwrap().cleanup_checkpoint().is_some(),observation.1@.unwrap().cleanup_checkpoint().unwrap().journal()==observation.1@.unwrap().checkpoint().journal(),
            history.wf(),history.starts_with(owner.cleanup_state().queues()[id].slots()),history.link()==owner.cleanup_state().queues()[id].link(),
            observation.2@.unwrap().live(id),history.matches(observation.2@.unwrap().queues()[id]),
            trajectory::completion::foreign_settled(history.events(),self.return_values().dom()),
        ensures self.unload_values(history.events(),&observation.1@.unwrap())==self.begin_values(),
            self.start().recorded(observation.1@.unwrap().checkpoint().events()),observation.1@.unwrap().recorded(observation.1@.unwrap().checkpoint().events()),self.start().at()<observation.1@.unwrap().at(),
    {
        let terminal=observation.2@.unwrap().queues()[id];
        let tracked endpoint=observation.1.borrow();
        match endpoint {Some(end)=>self.unload_recovers_from_history(owner,id,offset,history,terminal,end),None=>{}}
    }

}
}
