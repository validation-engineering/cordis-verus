//! Authentic Begin and Unload provenance from the production native host.
use super::{owner::EpisodeOwner, NativeRuntime};
#[cfg(verus_keep_ghost)]
use crate::refinement::Rule;
use crate::reversible_value::joint;
use vstd::prelude::*;

verus! {
/// The retained prefix is an actual persistent Journal receipt. The Begin
/// position is derived from the host's history, never supplied by its caller.
#[allow(dead_code)] // Persistent provenance is erased with the proof state.
pub tracked struct Begin {
    receipt:joint::Receipt,
    ghost at:nat,
    ghost native:nat,
    ghost owner:EpisodeOwner,
}
impl Begin {
    pub closed spec fn checkpoint(&self)->joint::Receipt {self.receipt}
    pub closed spec fn at(&self)->nat {self.at}
    pub closed spec fn native(&self)->nat {self.native}
    pub closed spec fn owner(&self)->EpisodeOwner {self.owner}
    pub open spec fn recorded(&self,frames:Seq<joint::Frame>)->bool {
        self.at()<frames.len()
            && frames[self.at() as int].event.key==self.native()
            && frames[self.at() as int].event.change==(joint::Change::Native {actor:self.owner().origin.id,rule:Rule::Begin})
            && frames[self.at() as int].event.after is Native
            && frames[self.at() as int].event.after->Native_state.owners.contains_pair(self.owner().origin.id,self.owner())
    }
    pub closed spec fn wf(&self)->bool {self.checkpoint().wf() && self.recorded(self.checkpoint().events())}
    pub proof fn facts(&self)
        requires self.wf(),ensures self.checkpoint().wf(),self.recorded(self.checkpoint().events()),
    {}
    pub proof fn receipt(tracked &self)->(tracked out:joint::Receipt)
        requires self.wf(),ensures out.wf(),out.same(&self.checkpoint()),
    {self.receipt.duplicate()}
    pub proof fn extend(&self,later:&joint::Receipt)
        requires self.wf(),later.covers(&self.checkpoint()),
        ensures self.recorded(later.events()),
    {
        self.facts();assert(later.events()[self.at() as int]==self.checkpoint().events()[self.at() as int]);
    }
}
/// A successful release exposes the exact native commit, including the owner
/// immediately before it. A different plugin or a later generation cannot be
/// substituted as the endpoint of a registered invocation.
#[allow(dead_code)] // This persistent source witness is erased by Cargo.
pub tracked struct Unload {
    receipt:joint::Receipt,
    groups:Option<joint::Receipt>,
    ghost native:nat,
    ghost owner:EpisodeOwner,
}
impl Unload {
    pub open spec fn same_source(&self,other:&Self)->bool {
        self.wf() && other.wf() && self.native()==other.native() && self.owner()==other.owner()
            && self.checkpoint().same(&other.checkpoint()) && self.cleanup_link()==other.cleanup_link()
    }

    pub proof fn duplicate(tracked &self)->(tracked out:Self)
        requires self.wf(),
        ensures out.same_source(self),out.wf(),out.native()==self.native(),out.owner()==self.owner(),out.checkpoint().same(&self.checkpoint()),
            out.cleanup_link()==self.cleanup_link(),out.before()==self.before(),out.after()==self.after(),
    {
        let tracked groups=match &self.groups {Some(receipt)=>Some(receipt.duplicate()),None=>None};
        Self {receipt:self.receipt.duplicate(),groups,native:self.native,owner:self.owner}
    }

    pub closed spec fn checkpoint(&self)->joint::Receipt {self.receipt}
    pub open spec fn before(&self)->joint::native::State {joint::native::at(self.checkpoint().events(),self.at(),self.native())}
    pub open spec fn after(&self)->joint::native::State {self.checkpoint().event().after->Native_state}
    pub open spec fn lifecycle_source(&self)->bool {
        joint::native::step(self.before(),self.after(),self.owner().origin.id,Rule::Unload)
            && crate::refinement::step(self.before().control,self.after().control,self.owner().origin.id,Rule::Unload)
    }
    pub open spec fn at(&self)->nat {self.checkpoint().at()}
    pub closed spec fn native(&self)->nat {self.native}
    pub closed spec fn owner(&self)->EpisodeOwner {self.owner}
    pub closed spec fn cleanup_checkpoint(&self)->Option<joint::Receipt> {self.groups}
    pub open spec fn cleanup_link(&self)->Option<(joint::Journal,nat)> {
        match self.cleanup_checkpoint() {Some(receipt)=>Some((receipt.journal(),receipt.event().key)),None=>None}
    }
    pub open spec fn cleanup_source(&self)->bool {
        sealed_groups(self.cleanup_checkpoint(),self.owner())
            && (self.cleanup_checkpoint().is_some() && self.cleanup_checkpoint().unwrap().journal()==self.checkpoint().journal() ==>
                self.checkpoint().follows(&self.cleanup_checkpoint().unwrap()))
    }
    pub open spec fn recorded(&self,frames:Seq<joint::Frame>)->bool {
        let before=joint::state_at(frames,self.at());
        self.at()<frames.len()
            && frames[self.at() as int].event.key==self.native()
            && frames[self.at() as int].event.change==(joint::Change::Native {actor:self.owner().origin.id,rule:Rule::Unload})
            && before.contains_key(self.native()) && before[self.native()] is Native
            && before[self.native()]->Native_state.owners.contains_pair(self.owner().origin.id,self.owner())
            && frames[self.at() as int].event.after is Native
            && !frames[self.at() as int].event.after->Native_state.owners.contains_key(self.owner().origin.id)
            && !frames[self.at() as int].event.after->Native_state.publications.contains_key(self.owner().origin.id)
    }
    pub closed spec fn wf(&self)->bool {self.checkpoint().wf() && self.recorded(self.checkpoint().events()) && self.cleanup_source() && self.lifecycle_source()}
    pub proof fn facts(&self)
        requires self.wf(),ensures self.checkpoint().wf(),self.recorded(self.checkpoint().events()),self.cleanup_source(),self.lifecycle_source(),
    {}
    /// Follow a queue present in an actual registration prefix until its
    /// membership disappears. Both early Remove and final Seal are covered.
    pub proof fn queue_drained_before(&self,earlier:&joint::Receipt,id:usize)->(cut:nat)
        requires self.wf(),self.cleanup_checkpoint().is_some(),earlier.wf(),
            self.cleanup_checkpoint().unwrap().journal()==self.checkpoint().journal(),
            self.cleanup_checkpoint().unwrap().covers(earlier),
            joint::groups::recorded(earlier.events(),earlier.events().len(),self.cleanup_link().unwrap().1),
            joint::groups::at(earlier.events(),earlier.events().len(),self.cleanup_link().unwrap().1).queues.contains_key(id),
        ensures earlier.events().len()<=cut<self.at(),
            joint::groups::drained(joint::state_at(self.checkpoint().events(),cut),
                joint::groups::at(earlier.events(),earlier.events().len(),self.cleanup_link().unwrap().1).queues[id]),
            self.checkpoint().events()[cut as int].event.key==self.cleanup_link().unwrap().1,
            self.checkpoint().events()[cut as int].event.change==(joint::Change::Groups {event:joint::groups::Event::Remove {id}})
                || self.checkpoint().events()[cut as int].event.change==(joint::Change::Groups {event:joint::groups::Event::Seal}),
    {
        hide(joint::valid);hide(joint::step);self.facts();
        let groups=self.cleanup_checkpoint().unwrap();let frames=groups.events();let key=groups.event().key;
        let start=earlier.events().len();let entry=joint::groups::at(earlier.events(),start,key).queues[id];
        assert(joint::state_at(frames,start)==joint::state_at(earlier.events(),start));
        crate::reversible_value::managed::recovery::frame_update(frames,groups.at());
        let cut=joint::groups::release::drained_before_exit(frames,start,frames.len(),key,id,entry);
        assert(joint::state_at(self.checkpoint().events(),cut)==joint::state_at(frames,cut));
        assert(self.checkpoint().events()[cut as int]==frames[cut as int]);cut
    }
    /// Locate the actual completion needed to discharge an occupied registered
    /// token before release. A callback Drained outcome is not called success.
    pub proof fn registered_token_completed(&self,registration:&joint::Receipt,id:usize,token:usize)->(cut:nat)
        requires self.wf(),self.cleanup_checkpoint().is_some(),registration.wf(),
            self.cleanup_checkpoint().unwrap().journal()==self.checkpoint().journal(),
            self.cleanup_checkpoint().unwrap().covers(registration),
            joint::groups::recorded(registration.events(),registration.events().len(),self.cleanup_link().unwrap().1),
            joint::groups::at(registration.events(),registration.events().len(),self.cleanup_link().unwrap().1).queues.contains_key(id),
            registration.event().change is RegisterInverse,registration.event().after is Cleanup,
            joint::groups::at(registration.events(),registration.events().len(),self.cleanup_link().unwrap().1).queues[id]==
                (registration.event().key,registration.event().after->Cleanup_state.domain),
            token<registration.event().after->Cleanup_state.occupied.len(),registration.event().after->Cleanup_state.occupied[token as int],
        ensures registration.events().len()<=cut<self.at(),
            joint::episode::release::completes(self.checkpoint().events()[cut as int].event,registration.event().key,token),
            self.checkpoint().events()[cut as int].event.after is Cleanup,
            token<self.checkpoint().events()[cut as int].event.after->Cleanup_state.occupied.len(),
    {
        hide(joint::valid);hide(joint::step);self.facts();
        let end=self.queue_drained_before(registration,id);let frames=self.checkpoint().events();let start=registration.events().len();
        self.checkpoint().cover_through(&self.cleanup_checkpoint().unwrap(),registration);
        assert(joint::state_at(frames,start)==joint::state_at(registration.events(),start));
        crate::reversible_value::managed::recovery::frame_update(registration.events(),registration.at());
        joint::episode::release::completed_before_drain(frames,start,end,registration.event().key,token)
    }
    pub proof fn receipt(tracked &self)->(tracked out:joint::Receipt)
        requires self.wf(),ensures out.wf(),out.same(&self.checkpoint()),
    {self.receipt.duplicate()}
    pub proof fn extend(&self,later:&joint::Receipt)
        requires self.wf(),later.covers(&self.checkpoint()),
        ensures self.recorded(later.events()),
    {
        self.facts();assert(later.events()[self.at() as int]==self.checkpoint().events()[self.at() as int]);
        assert(joint::state_at(later.events(),self.at())==joint::state_at(self.checkpoint().events(),self.at()));
    }
}
pub open spec fn sealed_groups(groups:Option<joint::Receipt>,owner:EpisodeOwner)->bool {
    groups.is_some() ==> {
        let receipt=groups.unwrap();
        &&& receipt.wf() && receipt.event().after is Groups
        &&& receipt.event().after->Groups_state.origin==Some(owner.origin)
        &&& receipt.event().after->Groups_state.sealed && receipt.event().after->Groups_state.queues.is_empty()
    }
}
impl<R,H,V> NativeRuntime<R,H,V> {
    /// Only the real successful release calls this constructor. The index is
    /// obtained from the host history and its actual final native commit.
    pub(crate) proof fn current_unload(tracked &self,id:usize,tracked groups:Option<joint::Receipt>)->(tracked out:Unload)
        requires self.core_wf(),self.execution_history().labels.len()>0,
            self.execution_history().labels.last()==(id,Rule::Unload),
            self.execution_history().states[self.execution_history().states.len()-2].owners.contains_key(id),
            self.execution_history().states[self.execution_history().states.len()-2].owners[id].origin.id==id,
            self.history_positions().last()+1==self.joint_events().len(),
            sealed_groups(groups,self.execution_history().states[self.execution_history().states.len()-2].owners[id]),
            groups.is_some() && groups.unwrap().journal()==self.journal_spec() ==>
                groups.unwrap().events().len()<self.joint_events().len()
                && self.joint_events().take(groups.unwrap().events().len() as int)==groups.unwrap().events(),
        ensures out.wf(),out.cleanup_checkpoint()==groups,out.owner()==self.execution_history().states[self.execution_history().states.len()-2].owners[id],
            out.native()==self.joint_key(),out.checkpoint().journal()==self.journal_spec(),
            out.checkpoint().events()==self.joint_events(),
            out.before()==self.execution_history().states[self.execution_history().states.len()-2].project((self.execution_history().labels.len()-1) as nat),
            out.after()==self.observation().project(self.execution_history().labels.len()),
    {
        hide(joint::valid);hide(joint::step);
        reveal(NativeRuntime::joint_valid);reveal(NativeRuntime::observation);reveal(NativeRuntime::joint_events);
        let history=self.execution_history();let last=history.labels.len()-1;
        let tracked receipt=self.joint.receipt();
        history.interval(self.history_positions(),receipt.events(),self.joint.key(),last);
        assert(history.indexed(self.history_positions(),receipt.events(),self.joint_key()));
        assert(super::history::step(history.states[last],history.states[last+1],id,Rule::Unload));
        super::history::project_step(history.states[last],history.states[last+1],id,Rule::Unload,last as nat);
        assert(self.history_positions()[last+1]==receipt.at());
        let tracked out=Unload {receipt,groups,native:self.joint_key(),owner:history.states[last].owners[id]};
        assert(out.lifecycle_source());out
    }
    /// Used by real registered dispatch before admitting any managed effect.
    pub(crate) proof fn current_begin(tracked &self,id:usize)->(tracked out:Begin)
        requires self.wf(),self.episode_owners().contains_key(id),
        ensures out.wf(),out.owner()==self.episode_owners()[id],
            out.native()==self.joint_key(),out.checkpoint().journal()==self.journal_spec(),
    {
        reveal(NativeRuntime::joint_valid);reveal(NativeRuntime::observation);reveal(NativeRuntime::joint_events);
        let history=self.execution_history();let last=history.states.len()-1;
        history.owner_has_begin(last,id);
        let at=choose|at:int|0<=at<last && history.labels[at]==(id,Rule::Begin)
            && history.states[at+1].owners.contains_key(id)
            && history.states[at+1].owners[id]==history.states[last].owners[id];
        let index=self.history_positions()[at+1];
        assert(history.indexed(self.history_positions(),self.joint.events(),self.joint_key()));
        assert(self.linked(id));
        let tracked receipt=self.joint.receipt();
        Begin {receipt,at:index,native:self.joint_key(),owner:self.episode_owners()[id]}
    }
}
}
