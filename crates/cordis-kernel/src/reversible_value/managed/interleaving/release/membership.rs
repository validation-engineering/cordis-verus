//! Registration ownership is emitted by real scalar/typed insertion and carried
//! through the interpreter. Sealing cannot precede one of those registrations.
#[cfg(verus_keep_ghost)]
use super::Event;
#[cfg(verus_keep_ghost)]
use super::{covered, emitted, registered};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::native::runtime::episode::Unload;
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, managed::Owner};
use vstd::prelude::*;

verus! {
pub proof fn before_seal(end:&Unload,receipt:joint::Receipt,id:usize,token:usize)
    requires end.wf(),end.cleanup_checkpoint().is_some(),
        end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal(),
        joint::groups::registration(Some(receipt),end.cleanup_link(),id),end.checkpoint().covers(&receipt),
        receipt.event().change is RegisterInverse,receipt.event().after is Cleanup,
        token<receipt.event().after->Cleanup_state.occupied.len(),receipt.event().after->Cleanup_state.occupied[token as int],
    ensures registered(end,receipt,id,token),
{
    hide(joint::valid);hide(joint::step);reveal(joint::groups::registration);end.facts();
    let groups=end.cleanup_checkpoint().unwrap();let frames=end.checkpoint().events();let key=end.cleanup_link().unwrap().1;
    end.checkpoint().included(&groups);end.checkpoint().included(&receipt);
    crate::reversible_value::managed::recovery::frame_update(groups.events(),groups.at());
    assert(joint::state_at(frames,groups.events().len())==joint::state_at(groups.events(),groups.events().len()));
    assert(joint::state_at(frames,receipt.events().len())==joint::state_at(receipt.events(),receipt.events().len()));
    if groups.events().len()<=receipt.events().len() {
        joint::groups::sealed_later(frames,groups.events().len(),receipt.events().len(),key);
        assert(false);
    }
    assert(groups.events().take(receipt.events().len() as int) =~= receipt.events());
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    pub open spec fn cleanup_emitted<A,R,M,X>(&self,events:Seq<Event<A,R,T,M,X>>,end:&Unload)->bool {
        self.result.is_ok() && forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> {
            let step=#[trigger] self.result->Ok_0.steps@[i];
            step.insertion().is_some() && emitted(events,end,step.insertion().unwrap(),step.token(),step.forward_inverse().inverse())
        }
    }
    /// Source ownership and ordering are derived before inspecting cleanup.
    pub proof fn registered_sources(&self,end:&Unload,id:usize)
        requires self.result.is_ok(),self.result->Ok_0.registered(end.cleanup_link(),id),
            self.completed(),self.effects_before_return(),self.result->Ok_0.witnessed(),
            end.wf(),end.cleanup_checkpoint().is_some(),end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal(),
            end.checkpoint().covers(&self.completion()),
            forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> (#[trigger] self.result->Ok_0.steps@[i]).write().journal()==self.completion().journal(),
        ensures forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> {
            let step=#[trigger] self.result->Ok_0.steps@[i];
            step.insertion().is_some() && registered(end,step.insertion().unwrap(),id,step.token())
        },
    {
        hide(joint::valid);hide(joint::step);self.execution_interval();
        assert forall|i:int|0<=i<self.result->Ok_0.steps.len() implies {
            let step=#[trigger] self.result->Ok_0.steps@[i];
            step.insertion().is_some() && registered(end,step.insertion().unwrap(),id,step.token())
        } by {
            let step=self.result->Ok_0.steps@[i];let receipt=step.insertion().unwrap();
            reveal(joint::groups::registration);
            end.checkpoint().cover_through(&self.completion(),&receipt);before_seal(end,receipt,id,step.token());
        }
    }
    /// Membership and token identity are postconditions of the running
    /// interpreter. Only emitted acknowledgement coverage remains a source input.
    pub proof fn registered_cleanup_coverage<A,R,M,X>(&self,events:Seq<Event<A,R,T,M,X>>,end:&Unload,id:usize)
        requires self.result.is_ok(),self.result->Ok_0.registered(end.cleanup_link(),id),
            self.completed(),self.effects_before_return(),self.result->Ok_0.witnessed(),
            end.wf(),end.cleanup_checkpoint().is_some(),end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal(),
            end.checkpoint().covers(&self.completion()),self.cleanup_emitted(events,end),
            forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> (#[trigger] self.result->Ok_0.steps@[i]).write().journal()==self.completion().journal(),
        ensures self.cleanup_covered(events,end,id),
    {self.registered_sources(end,id);reveal(covered);}
    pub proof fn unload_recovers_registered<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,events:Seq<Event<A,R,T,M,X>>,end:&Unload)
        requires owner.wf(),owner.cleanup_state().live(id),self.start().owner().owns(&owner),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner,id,offset),crate::reversible_value::managed::retained(self.result->Ok_0.steps@,owner,id,offset),
            super::super::linked(events,self.completion(),self.return_values(),self.obligations(owner,id,offset)),self.unload_source(events,end),
            self.result->Ok_0.registered(owner.cleanup_state().link(),id),end.cleanup_link()==owner.cleanup_state().link(),
            end.cleanup_checkpoint().is_some(),end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal(),
            self.cleanup_emitted(events,end),super::super::completion::foreign_settled(events,self.return_values().dom()),
        ensures self.unload_values(events,end)==self.begin_values(),
            self.start().recorded(end.checkpoint().events()),end.recorded(end.checkpoint().events()),self.start().at()<end.at(),
    {
        self.registered_cleanup_coverage(events,end,id);
        self.unload_recovers_from_cleanup(owner,id,offset,events,end);
    }
}
}
