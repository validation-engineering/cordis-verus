//! Derive foreign restoration from actual registered slots and drained owners.
//! Observation coverage names dispatch sources, never successful outcomes.
use crate::reversible_value::managed::interleaving::history::lifecycle::RecordedExecution;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    managed::{
        interleaving::{completion, history::History, Event},
        Step,
    },
    service_composition::Address,
};
use vstd::prelude::*;

verus! {
/// Every actual dispatch of this original queue/token is present after the
/// observed forward. Failed attempts are included; success is not a premise.
pub open spec fn dispatches_after<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:nat,history:&History<A,R,T,M,X>,token:usize)->bool {
    forall|i:int|0<=i<history.events().len() && (#[trigger] history.events()[i]) is Managed
        && history.events()[i]->Managed_0.queue_link()==history.link()
        && history.events()[i]->Managed_0.ticket().token==token ==>
            exists|j:int|start<=j<events.len() && #[trigger] events[j]==history.events()[i]
}

/// The executable observed entry points append the same actual observations
/// to both owners. This maintains coverage for arbitrary finite call sequences.
pub proof fn extend_dispatch_coverage<A,R,T:?Sized,M,X>(before:Seq<Event<A,R,T,M,X>>,after:Seq<Event<A,R,T,M,X>>,
    source_before:&History<A,R,T,M,X>,source_after:&History<A,R,T,M,X>,suffix:Seq<Event<A,R,T,M,X>>,start:nat,token:usize)
    requires dispatches_after(before,start,source_before,token),start<=before.len(),
        source_after.link()==source_before.link(),source_after.events()==source_before.events()+suffix,after==before+suffix,
    ensures dispatches_after(after,start,source_after,token),
{
    assert forall|i:int|0<=i<source_after.events().len() && (#[trigger] source_after.events()[i]) is Managed
        && source_after.events()[i]->Managed_0.queue_link()==source_after.link()
        && source_after.events()[i]->Managed_0.ticket().token==token implies
            exists|j:int|start<=j<after.len() && #[trigger] after[j]==source_after.events()[i] by {
        if i<source_before.events().len() {
            assert(source_after.events()[i]==source_before.events()[i]);
            let j=choose|j:int|start<=j<before.len() && #[trigger] before[j]==source_before.events()[i];
            assert(after[j]==source_after.events()[i]);
        } else {
            let offset=i-source_before.events().len();let j=before.len()+offset;
            assert(source_after.events()[i]==suffix[offset]);assert(after[j]==suffix[offset]);
        }
    }
}


impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    #[verifier::opaque]
    pub open spec fn observations_extend<C2,G2>(&self,prior:&Self,observer:&RecordedExecution<C2,G2,A,R,T,M,X>,before:&RecordedExecution<C2,G2,A,R,T,M,X>)->bool {
        forall|id:usize,group:usize,start:nat,token:usize|#![trigger prior.histories()[id],before.histories()[group],dispatches_after(before.histories()[group].events(),start,&prior.histories()[id],token)]
            prior.histories().contains_key(id) && before.histories().contains_key(group)
                && start<=before.histories()[group].events().len()
                && dispatches_after(before.histories()[group].events(),start,&prior.histories()[id],token) ==>
                    self.histories().contains_key(id) && observer.histories().contains_key(group)
                        && dispatches_after(observer.histories()[group].events(),start,&self.histories()[id],token)
    }

    pub(crate) proof fn shared_observations<C2,G2>(&self,prior:&Self,observer:&RecordedExecution<C2,G2,A,R,T,M,X>,before:&RecordedExecution<C2,G2,A,R,T,M,X>,suffix:Seq<Event<A,R,T,M,X>>)
        requires self.wf(),prior.wf(),self.origins()==prior.origins(),self.histories().dom()==prior.histories().dom(),
            observer.histories().dom()==before.histories().dom(),
            forall|id:usize|#[trigger] prior.histories().contains_key(id) ==> self.histories()[id].events()==prior.histories()[id].events()+suffix,
            forall|id:usize|#[trigger] before.histories().contains_key(id) ==> observer.histories()[id].events()==before.histories()[id].events()+suffix,
        ensures self.observations_extend(prior,observer,before),
    {
        self.facts();prior.facts();reveal(RecordedExecution::observations_extend);
        assert forall|id:usize,group:usize,start:nat,token:usize|#![trigger prior.histories()[id],before.histories()[group],dispatches_after(before.histories()[group].events(),start,&prior.histories()[id],token)]
            prior.histories().contains_key(id) && before.histories().contains_key(group)
                && start<=before.histories()[group].events().len()
                && dispatches_after(before.histories()[group].events(),start,&prior.histories()[id],token) implies
                    self.histories().contains_key(id) && observer.histories().contains_key(group)
                        && dispatches_after(observer.histories()[group].events(),start,&self.histories()[id],token) by {
            assert(self.entry(id));assert(prior.entry(id));
            extend_dispatch_coverage(before.histories()[group].events(),observer.histories()[group].events(),
                &prior.histories()[id],&self.histories()[id],suffix,start,token);
        }
    }


    /// A real function step identifies its retained original action and exact
    /// registration source. Later queue removal keeps this original slot.
    pub open spec fn owns_forward(&self,id:usize,step:Step<T>)->bool {
        self.wf() && self.histories().contains_key(id) && step.recorded_values()
            && step.token()<self.histories()[id].initial().len()
            && step.in_slot(self.histories()[id].initial()[step.token() as int])
            && step.registered(self.baseline().cleanup_state().link(),id)
            && step.inserted_into(self.histories()[id].link())
    }

    pub proof fn retain_forward_source(&self,earlier:&Self,id:usize,step:Step<T>)
        requires earlier.owns_forward(id,step),self.wf(),self.histories().contains_key(id),
            self.histories()[id].starts_with(earlier.histories()[id].initial()),
            self.histories()[id].link()==earlier.histories()[id].link(),
            self.baseline().cleanup_state().link()==earlier.baseline().cleanup_state().link(),
        ensures self.owns_forward(id,step),
    {
        hide(Step::recorded_values);
        assert(self.histories()[id].initial()[step.token() as int]==earlier.histories()[id].initial()[step.token() as int]);
    }

    /// A terminal queue came from successful actual removal or Unload. Its
    /// drain guard plus slot conservation forces an authentic managed success.
    pub proof fn drained_forward(&self,id:usize,step:Step<T>)->(index:int)
        requires self.owns_forward(id,step),self.terminal().contains_key(id),
        ensures 0<=index<self.histories()[id].events().len(),
            self.histories()[id].events()[index] is Managed,
            self.histories()[id].events()[index]->Managed_0.queue_link()==self.histories()[id].link(),
            self.histories()[id].events()[index]->Managed_0.ticket().token==step.token(),
            completion::restores(self.histories()[id].events()[index],step.forward_inverse().inverse()),
    {
        self.facts();let history=self.histories()[id];let token=step.token() as int;
        assert(!self.core().cleanup_state().live(id));
        history.drained_slots(self.terminal()[id]);
        step.source_inverse(history.initial()[token]);
        reveal(Step::in_slot);
        let index=history.consuming_index(token);index
    }

    /// Transport the source-derived success into an observing execution. The
    /// caller supplies complete dispatch coverage, not a successful restore.
    pub proof fn observed_forward_closed(&self,id:usize,step:Step<T>,events:Seq<Event<A,R,T,M,X>>,start:nat)
        requires self.owns_forward(id,step),self.terminal().contains_key(id),
            dispatches_after(events,start,&self.histories()[id],step.token()),
        ensures completion::later(events,step.forward_inverse().inverse(),start),
    {
        let index=self.drained_forward(id,step);
        let j=choose|j:int|start<=j<events.len() && #[trigger] events[j]==self.histories()[id].events()[index];
        assert(completion::restores(events[j],step.forward_inverse().inverse()));
    }
}

/// Each relevant forward selects a real report step and a recorded terminal
/// owner. The map permits several providers and dynamically removed groups.
pub open spec fn covered<C,G,A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,keys:Set<Address>,owners:Map<usize,RecordedExecution<C,G,A,R,T,M,X>>)->bool {
    forall|i:int|0<=i<events.len() && (#[trigger] events[i]).forward() && keys.contains(events[i].inverse().address) ==>
        exists|source:usize,id:usize,step:Step<T>|owners.contains_key(source)
            && #[trigger] owners[source].owns_forward(id,step)
            && owners[source].terminal().contains_key(id)
            && events[i]==Event::Forward(step.forward_inverse())
            && dispatches_after(events,(i+1) as nat,&owners[source].histories()[id],step.token())
}

pub proof fn closed_from_owners<C,G,A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,keys:Set<Address>,owners:Map<usize,RecordedExecution<C,G,A,R,T,M,X>>)
    requires covered(events,keys,owners),
    ensures completion::foreign_settled(events,keys),
{
    assert forall|i:int|0<=i<events.len() && (#[trigger] events[i]).forward() && keys.contains(events[i].inverse().address) implies
        completion::later(events,events[i].inverse(),(i+1) as nat) by {
        let (source,id,step)=choose|source:usize,id:usize,step:Step<T>|owners.contains_key(source)
            && #[trigger] owners[source].owns_forward(id,step)
            && owners[source].terminal().contains_key(id)
            && events[i]==Event::Forward(step.forward_inverse())
            && dispatches_after(events,(i+1) as nat,&owners[source].histories()[id],step.token());
        owners[source].observed_forward_closed(id,step,events,(i+1) as nat);
    }
}
}
