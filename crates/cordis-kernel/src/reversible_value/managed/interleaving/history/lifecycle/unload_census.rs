//! Complete value recovery and original Child completion at one actual native
//! snapshot. Local restoration comes from Unload; foreign writes and Child
//! endpoints are checked from complete producer and native ownership sources.
#[cfg(verus_keep_ghost)]
use super::RecordedExecution;
use crate::reversible_value::managed::interleaving::sources::interval::{Interval, Issue};
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::{
    lifecycle_state::native::runtime::{
        child_history::{completion::Resolution, Ledger},
        episode::Unload,
        history::Snapshot,
    },
    reversible_value::{
        joint,
        managed::{
            self,
            interleaving::{self as trajectory, completion, endpoint, release, sources::coverage},
            Step,
        },
        service_composition::Address,
    },
};
use vstd::prelude::*;

verus! {
pub ghost enum Obstruction<T:?Sized> {
    Boundary(Issue<T>),
    /// An actual interval creation has no matching successful restore by cut.
    Foreign {index:int},
    /// An original native inverse has no matching collected terminal source.
    Child {group:usize,token:int},
}
pub ghost struct FinalCensus<A,R,T:?Sized,M,X> {pub interval:Interval<A,R,T,M,X>,pub issue:Option<Obstruction<T>>}
impl<A,R,T:?Sized,M,X> FinalCensus<A,R,T,M,X> {
    pub open spec fn diagnosed<C,G>(&self,owner:&RecordedExecution<C,G,A,R,T,M,X>,slots:Seq<Option<trajectory::obligations::Inverse<T>>>,ledger:&Ledger)->bool {
        match self.issue {
            None=>false,
            Some(Obstruction::Boundary(issue))=>self.interval.diagnosed(issue,slots),
            Some(Obstruction::Foreign {index})=>0<=index<self.interval.events.len() && self.interval.events[index].forward()
                && !completion::later(self.interval.events,self.interval.events[index].inverse(),(index+1) as nat),
            Some(Obstruction::Child {group,token})=>owner.native_child_source(group,token).is_some()
                && !(exists|resolution:Resolution|owner.native_child_completion(ledger,group,token,resolution)),
        }
    }
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    /// Sources exported by the actual registered call, recorded owner and its
    /// actual successful native release. This does not assume restored values,
    /// a drained inverse word, foreign success, or Child completion.
    pub open spec fn unload_input<C,G,A,R,M,X>(&self,owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,end:&Unload)->bool {
        &&& owner.wf() && owner.histories().contains_key(id) && owner.baseline().cleanup_state().live(id) && owner.terminal().contains_key(id)
        &&& self.start().owner().owns(&owner.baseline())
        &&& self.completed() && self.effects_before_return() && self.episode_interval() && self.endpoint_source()
        &&& self.result->Ok_0.witnessed() && self.result->Ok_0.recovery_history()
        &&& self.retained_recovery(owner.baseline(),id,offset) && managed::retained(self.result->Ok_0.steps@,owner.baseline(),id,offset)
        &&& self.result->Ok_0.registered(owner.baseline().cleanup_state().link(),id)
        &&& self.result->Ok_0.queued_sources(owner.baseline().cleanup_state().queues()[id].link())
        &&& end.wf() && end.owner()==self.start().owner() && end.native()==self.start().native()
        &&& end.cleanup_link()==owner.baseline().cleanup_state().link() && end.checkpoint().covers(&self.completion())
        &&& end.cleanup_checkpoint().is_some() && end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal()
        &&& owner.source_order(id,self.completion())
        &&& forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> (#[trigger] self.result->Ok_0.steps@[i]).carrier().covered(owner.value_sources())
    }
    pub open spec fn interval_source<C,G,A,R,M,X>(&self,owner:&RecordedExecution<C,G,A,R,T,M,X>,interval:Interval<A,R,T,M,X>)->bool {
        interval.wf() && interval.start==self.completion() && interval.producers.dom()==self.return_values().dom()
            && forall|key:Address|#[trigger] interval.producers.contains_key(key) ==> interval.producers[key].carrier().covered(owner.value_sources())
    }
    /// Import the successful restores forced by real terminal queue ownership
    /// into the independent producer projection, including prior failed retries.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    pub proof fn local_census_settled<C,G,A,R,M,X>(&self,tracked owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,tracked end:&Unload,interval:Interval<A,R,T,M,X>)
        requires self.unload_input(owner,id,offset,end),self.interval_source(owner,interval),interval.end.covers(&end.checkpoint()),
        ensures forall|i:int|0<=i<self.obligations(owner.baseline(),id,offset).len() && (#[trigger] self.obligations(owner.baseline(),id,offset)[i]).is_some() ==>
            completion::later(interval.events,self.obligations(owner.baseline(),id,offset)[i].unwrap(),0),
    {
        hide(joint::valid);hide(joint::step);hide(Step::recorded_values);
        hide(Interval::wf);hide(trajectory::Forward::inverse);hide(trajectory::inverse_action);
        hide(completion::later);hide(release::emitted);
        owner.facts();self.source_bounds();
        end.facts();
        let tracked history=owner.history(id);let steps=self.result->Ok_0.steps@;
        managed::episode::endpoint::final_observation(steps,self.completion());
        managed::episode::endpoint::landed_domain(steps,managed::recovery::word::initial(steps));
        managed::recovery::word::initial_inputs(steps);
        self.emitted_from_history(owner.baseline(),id,offset,history,owner.terminal()[id],end);
        self.registered_sources(end,id);
        assert forall|i:int|0<=i<steps.len() implies completion::later(interval.events,(#[trigger] steps[i]).forward_inverse().inverse(),0) by {
            let step=steps[i];let registration=step.insertion().unwrap();
            step.source_inverse(owner.baseline().cleanup_state().queues()[id].slots()[offset+i]);
            step.forward_inverse().facts();
            assert(step.forward_inverse().inverse().address==step.address()) by {reveal(Step::recorded_values);}
            assert(self.return_values().contains_key(step.address()));
            assert(release::covered(history.events(),end,registration,id,step.token(),step.forward_inverse().inverse())) by {reveal(release::covered);}
            let k=release::restoration_before_unload(history.events(),end,registration,id,step.token(),step.forward_inverse().inverse());
            let event=history.events()[k];event.actual_attempt();event.attempt().mutation_record();
            interval.end.cover_through(&end.checkpoint(),&event.checkpoint());
            let j=interval.includes_restore(event,owner.value_sources());
            assert(completion::restores(interval.events[j],step.forward_inverse().inverse()));
            reveal(completion::later);
        }
        let slots=owner.baseline().cleanup_state().queues()[id].slots();
        assert forall|i:int|0<=i<self.obligations(owner.baseline(),id,offset).len() && (#[trigger] self.obligations(owner.baseline(),id,offset)[i]).is_some() implies
            completion::later(interval.events,self.obligations(owner.baseline(),id,offset)[i].unwrap(),0) by {
            let step=steps[i];step.source_inverse(slots[offset+i]);
            assert(self.obligations(owner.baseline(),id,offset)[i]==Some(step.forward_inverse().inverse()));
        }
    }
    #[verifier::spinoff_prover]
    pub proof fn settled_census_values<C,G,A,R,M,X,V>(&self,owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,cut:&Snapshot<V>,interval:Interval<A,R,T,M,X>)
        requires owner.wf(),owner.baseline().cleanup_state().live(id),self.endpoint_source(),self.completed(),self.effects_before_return(),self.episode_interval(),
            self.retained_recovery(owner.baseline(),id,offset),self.result->Ok_0.recovery_history(),self.result->Ok_0.witnessed(),
            managed::retained(self.result->Ok_0.steps@,owner.baseline(),id,offset),self.interval_source(owner,interval),cut.certified(),
            interval.end.journal()==cut.joint_spec().journal_spec(),interval.end.events()==cut.joint_spec().events(),
            trajectory::linked(interval.events,self.completion(),self.return_values(),self.obligations(owner.baseline(),id,offset)),
            completion::settled(interval.events,self.obligations(owner.baseline(),id,offset),self.return_values().dom()),
            coverage::complete(interval.events,self.completion(),interval.end,self.return_values().dom()),
        ensures self.recovered_values_at_cut(interval.events,cut)==self.begin_values(),
    {
        hide(joint::valid);hide(joint::step);hide(trajectory::linked);hide(completion::settled);hide(Interval::wf);
        owner.facts();interval.ordered();self.settled_recovers_begin(owner.baseline(),id,offset,interval.events);
        coverage::tails_from_census(interval.events,self.completion(),interval.end,self.return_values().dom());
        self.source_bounds();managed::episode::endpoint::final_observation(self.result->Ok_0.steps@,self.completion());
        managed::episode::endpoint::landed_domain(self.result->Ok_0.steps@,managed::recovery::word::initial(self.result->Ok_0.steps@));
        assert(self.return_values().dom() =~= managed::episode::endpoint::keys(self.result->Ok_0.steps@));
        endpoint::observe_matches(self.result->Ok_0.steps@,interval.events,self.completion(),interval.end,self.return_values());
        assert(self.recovered_values_at_cut(interval.events,cut) =~= endpoint::observe(self.result->Ok_0.steps@,interval.events,interval.end));
    }
    /// Total proof query at the actual common native cut. Foreign closure is
    /// read from complete producer histories, not a list of observed successes.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    pub proof fn unload_census<C,G,A,R,M,X,V>(&self,tracked owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,
        tracked end:&Unload,ledger:&Ledger,cut:&Snapshot<V>,interval:Interval<A,R,T,M,X>)->(out:FinalCensus<A,R,T,M,X>)
        requires self.unload_input(owner,id,offset,end),self.interval_source(owner,interval),
            ledger.cut_source(cut),cut.key()==end.native(),cut.joint_spec().covers(&end.checkpoint()),
            interval.end.journal()==cut.joint_spec().journal_spec(),interval.end.events()==cut.joint_spec().events(),
        ensures out.interval==interval,
            out.issue.is_none()==(interval.clear(self.obligations(owner.baseline(),id,offset))
                && completion::foreign_settled(interval.events,interval.producers.dom()) && owner.native_children_resolved(ledger)),
            out.issue.is_some() ==> out.diagnosed(owner,self.obligations(owner.baseline(),id,offset),ledger),
            out.issue.is_none() ==> self.recovered_values_at_cut(interval.events,cut)==self.begin_values()
                && owner.native_children_terminal(ledger,cut) && self.writes_registered_at_cut(&cut.joint_spec())
                && self.start().recorded(cut.joint_spec().events()) && end.recorded(cut.joint_spec().events()),
    {
        hide(joint::valid);hide(joint::step);hide(Interval::wf);hide(trajectory::linked);
        hide(trajectory::obligations::recover);hide(trajectory::outstanding);hide(trajectory::values);
        hide(coverage::complete);hide(trajectory::sources::origins::admitted);
        owner.facts();cut.valid_history();
        assert(interval.end.covers(&self.completion())) by {reveal(Interval::wf);}
        let boundary=self.recorded_census(owner,id,offset,interval);
        if let Some(issue)=boundary {return FinalCensus {interval,issue:Some(Obstruction::Boundary(issue))};}
        self.local_census_settled(owner,id,offset,end,interval);
        if exists|i:int|0<=i<interval.events.len() && (#[trigger] interval.events[i]).forward()
            && !completion::later(interval.events,interval.events[i].inverse(),(i+1) as nat) {
            let index=choose|i:int|0<=i<interval.events.len() && (#[trigger] interval.events[i]).forward()
                && !completion::later(interval.events,interval.events[i].inverse(),(i+1) as nat);
            assert(interval.producers.dom().contains(interval.events[index].inverse().address)) by {reveal(Interval::wf);}
            return FinalCensus {interval,issue:Some(Obstruction::Foreign {index})};
        }
        assert(completion::settled(interval.events,self.obligations(owner.baseline(),id,offset),self.return_values().dom()));
        self.settled_census_values(owner,id,offset,cut,interval);
        if exists|group:usize,token:int|(#[trigger] owner.native_child_source(group,token)).is_some()
            && !(exists|resolution:Resolution|owner.native_child_completion(ledger,group,token,resolution)) {
            let (group,token)=choose|group:usize,token:int|(#[trigger] owner.native_child_source(group,token)).is_some()
                && !(exists|resolution:Resolution|owner.native_child_completion(ledger,group,token,resolution));
            return FinalCensus {interval,issue:Some(Obstruction::Child {group,token})};
        }
        assert(owner.native_children_resolved(ledger));owner.native_children_at_cut(ledger,cut);
        self.registered_pending_at_cut(end.cleanup_link(),id,&cut.joint_spec());
        self.start().facts();end.facts();
        interval.end.cover_through(&self.completion(),&self.start().checkpoint());self.start().extend(&interval.end);
        assert(cut.joint_spec().events()[end.at() as int]==end.checkpoint().events()[end.at() as int]);
        assert(joint::state_at(cut.joint_spec().events(),end.at())==joint::state_at(end.checkpoint().events(),end.at()));
        FinalCensus {interval,issue:None}
    }
}
}
