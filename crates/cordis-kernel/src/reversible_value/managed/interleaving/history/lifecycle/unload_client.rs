//! Nonempty common-cut proof client: two actual registered invocations, one
//! assigned native Child and both real Unloads. The finite ownership profile
//! names creating operations, not restore successes or expected endpoint values.
#[cfg(verus_keep_ghost)]
use super::{
    unload_census::{FinalCensus, Obstruction},
    RecordedExecution,
};
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::{
    lifecycle_state::native::runtime::{
        child_history::{completion::Resolution, Ledger},
        episode::Unload,
        history::Snapshot,
    },
    reversible_value::{
        history::sources::Sources,
        joint,
        managed::{
            self,
            interleaving::{self as trajectory, completion, release, sources::interval::Interval},
            Step,
        },
        payload,
    },
};
use vstd::prelude::*;

verus! {
/// All writes in the interval belong to this actual registered report. Matching
/// includes the source address, creating position and complete semantic inverse.
pub open spec fn owns_forwards<E:ScalarEffect,A,R,T:?Sized,M,X>(report:&RegisteredReport<E,T>,interval:Interval<A,R,T,M,X>)->bool {
    report.result.is_ok() && forall|i:int|0<=i<interval.events.len() && (#[trigger] interval.events[i]).forward() ==>
        exists|k:int|0<=k<report.result->Ok_0.steps.len() && (#[trigger] report.result->Ok_0.steps@[k]).forward_inverse().inverse()==interval.events[i].inverse()
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    /// Complete producer projection replaces the old dispatch-observer coverage
    /// premise. The foreign queue's actual Unload forces its matching restore.
    #[verifier::spinoff_prover]
    pub proof fn foreign_census_from_unload<C,G,A,R,M,X>(&self,tracked owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,
        tracked end:&Unload,interval:Interval<A,R,T,M,X>,sources:Sources<payload::State<T>>)
        requires self.unload_input(owner,id,offset,end),interval.wf(),owns_forwards(self,interval),
            self.completion().covers(&interval.start),interval.end.covers(&end.checkpoint()),
            sources.wf(),sources.extends(owner.value_sources()),
            forall|key:crate::reversible_value::service_composition::Address|#[trigger] interval.producers.contains_key(key) ==> interval.producers[key].carrier().covered(sources),
        ensures completion::foreign_settled(interval.events,interval.producers.dom()),
    {
        hide(joint::valid);hide(joint::step);hide(Interval::wf);hide(Step::recorded_values);
        hide(trajectory::Forward::inverse);hide(trajectory::inverse_action);hide(completion::later);hide(release::emitted);
        owner.facts();self.source_bounds();end.facts();let tracked history=owner.history(id);
        self.emitted_from_history(owner.baseline(),id,offset,history,owner.terminal()[id],end);self.registered_sources(end,id);
        assert forall|i:int|0<=i<interval.events.len() && (#[trigger] interval.events[i]).forward() && interval.producers.dom().contains(interval.events[i].inverse().address) implies
            completion::later(interval.events,interval.events[i].inverse(),(i+1) as nat) by {
            let forward=interval.events[i];let k=choose|k:int|0<=k<self.result->Ok_0.steps.len() && (#[trigger] self.result->Ok_0.steps@[k]).forward_inverse().inverse()==forward.inverse();
            let step=self.result->Ok_0.steps@[k];let registration=step.insertion().unwrap();
            step.source_inverse(owner.baseline().cleanup_state().queues()[id].slots()[offset+k]);step.forward_inverse().facts();
            assert(step.forward_inverse().inverse().address==step.address()) by {reveal(Step::recorded_values);}
            assert(release::covered(history.events(),end,registration,id,step.token(),step.forward_inverse().inverse())) by {reveal(release::covered);}
            let h=release::restoration_before_unload(history.events(),end,registration,id,step.token(),step.forward_inverse().inverse());
            let event=history.events()[h];event.actual_attempt();event.attempt().mutation_record();interval.end.cover_through(&end.checkpoint(),&event.checkpoint());
            let j=interval.includes_restore(event,sources);
            reveal(Interval::wf);let p=forward->Produced_0.producer;p.mutation(forward->Produced_0.index);
            let created=interval.origin(j);p.ordered();
            assert(forward.inverse().origin==forward.checkpoint().at());
            assert(interval.events[j].inverse().origin<interval.events[j].checkpoint().at());
            assert(i<j);assert(completion::restores(interval.events[j],forward.inverse()));reveal(completion::later);
        }
    }
    /// A nonempty value/Child/foreign composition over actual host objects.
    /// The source profile allows failed attempts and retries; only authentic
    /// terminal groups force success. Destructive/cross-Begin barriers stay visible.
    #[verifier::spinoff_prover]
    pub proof fn nonempty_unload_client<C,G,C2,G2,E2:ScalarEffect,A,R,M,X,V>(&self,
        tracked owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,tracked end:&Unload,
        foreign:&RegisteredReport<E2,T>,tracked writer:&RecordedExecution<C2,G2,A,R,T,M,X>,writer_id:usize,writer_offset:nat,tracked writer_end:&Unload,
        ledger:&Ledger,cut:&Snapshot<V>,interval:Interval<A,R,T,M,X>,child_group:usize,child_token:int,resolution:Resolution)->(out:FinalCensus<A,R,T,M,X>)
        requires self.unload_input(owner,id,offset,end),self.interval_source(owner,interval),self.result->Ok_0.steps.len()>0,
            foreign.unload_input(writer,writer_id,writer_offset,writer_end),foreign.result->Ok_0.steps.len()>0,
            foreign.completion().covers(&interval.start),interval.end.covers(&writer_end.checkpoint()),owns_forwards(foreign,interval),
            exists|i:int|0<=i<interval.events.len() && (#[trigger] interval.events[i]).forward(),
            ledger.cut_source(cut),cut.key()==end.native(),cut.joint_spec().covers(&end.checkpoint()),
            interval.end.journal()==cut.joint_spec().journal_spec(),interval.end.events()==cut.joint_spec().events(),
            owner.native_child_source(child_group,child_token).is_some(),resolution.birth.is_some(),resolution.unload.is_some(),
            ledger.records(&owner.native_child_source(child_group,child_token).unwrap(),resolution),
            owner.owned_child_retirement(child_group,child_token,&ledger.retirements()[resolution.retirement]),
            ledger.births()[resolution.birth.unwrap()].parent().origin==owner.baseline().origin().unwrap(),
            ledger.births()[resolution.birth.unwrap()].parent().work_domain==owner.baseline().work_state().domain_id(),
            forall|group:usize,token:int|(#[trigger] owner.native_child_source(group,token)).is_some() ==> group==child_group && token==child_token,
        ensures out.interval==interval,out.issue.is_none()==interval.clear(self.obligations(owner.baseline(),id,offset)),
            out.issue.is_some() ==> out.issue.unwrap() is Boundary && out.diagnosed(owner,self.obligations(owner.baseline(),id,offset),ledger),
            out.issue.is_none() ==> self.recovered_values_at_cut(interval.events,cut)==self.begin_values()
                && owner.native_children_terminal(ledger,cut) && self.writes_registered_at_cut(&cut.joint_spec())
                && self.start().recorded(cut.joint_spec().events()) && end.recorded(cut.joint_spec().events()),
    {
        hide(joint::valid);hide(joint::step);hide(Interval::wf);owner.facts();writer.facts();
        let tracked mut sources=Sources::<payload::State<T>>::new();
        sources.merge(owner.sources_witness());sources.merge(writer.sources_witness());
        assert forall|key:crate::reversible_value::service_composition::Address|#[trigger] interval.producers.contains_key(key) implies interval.producers[key].carrier().covered(sources) by {}
        foreign.foreign_census_from_unload(writer,writer_id,writer_offset,writer_end,interval,sources);
        assert(owner.native_child_completion(ledger,child_group,child_token,resolution));
        assert forall|group:usize,token:int|(#[trigger] owner.native_child_source(group,token)).is_some() implies
            exists|r:Resolution|owner.native_child_completion(ledger,group,token,r) by {assert(owner.native_child_completion(ledger,group,token,resolution));}
        let out=self.unload_census(owner,id,offset,end,ledger,cut,interval);
        match out.issue {
            Some(Obstruction::Foreign {index})=>{
                assert(interval.producers.dom().contains(interval.events[index].inverse().address)) by {reveal(Interval::wf);}
                assert(false);
            },
            Some(Obstruction::Child {group,token})=>{assert(owner.native_child_completion(ledger,group,token,resolution));assert(false);},
            _=>{},
        }
        out
    }
}
}
