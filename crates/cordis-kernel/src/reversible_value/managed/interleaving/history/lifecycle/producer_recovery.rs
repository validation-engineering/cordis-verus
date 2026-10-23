//! Root and Child reports consume an automatically assembled producer interval.
//! Coverage and inverse origins are outputs; crossing the invocation boundary
//! returns an actual obstruction instead of assuming that boundary away.
#[cfg(verus_keep_ghost)]
use super::RecordedExecution;
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    joint,
    managed::{
        self,
        episode::endpoint,
        interleaving::{
            self as trajectory, obligations,
            sources::{
                coverage,
                interval::{Interval, Issue},
                link, origins,
            },
        },
        recovery::word,
    },
};
use vstd::prelude::*;

verus! {
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    /// The same registered invocation contract covers roots and native Child
    /// invocations. No event census, origin admission or quiet-tail input.
    pub proof fn recorded_census<C,G,A,R,M,X>(&self,owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,interval:Interval<A,R,T,M,X>)->(issue:Option<Issue<T>>)
        requires owner.wf(),owner.histories().contains_key(id),owner.baseline().cleanup_state().live(id),
            interval.wf(),interval.start==self.completion(),interval.producers.dom()==self.return_values().dom(),
            forall|key:crate::reversible_value::service_composition::Address|#[trigger] interval.producers.contains_key(key) ==> interval.producers[key].carrier().covered(owner.value_sources()),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner.baseline(),id,offset),managed::retained(self.result->Ok_0.steps@,owner.baseline(),id,offset),
            forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> (#[trigger] self.result->Ok_0.steps@[i]).carrier().covered(owner.value_sources()),
        ensures issue.is_none()==interval.clear(self.obligations(owner.baseline(),id,offset)),
            issue.is_some() ==> interval.diagnosed(issue.unwrap(),self.obligations(owner.baseline(),id,offset)),
            issue.is_none() ==> coverage::complete(interval.events,self.completion(),interval.end,self.return_values().dom())
                && origins::admitted(interval.events,self.obligations(owner.baseline(),id,offset),self.return_values().dom())
                && trajectory::linked(interval.events,self.completion(),self.return_values(),self.obligations(owner.baseline(),id,offset))
                && obligations::recover(trajectory::outstanding(interval.events,self.obligations(owner.baseline(),id,offset),self.return_values().dom(),interval.events.len()),
                    trajectory::endpoint::observe(self.result->Ok_0.steps@,interval.events,interval.end))==Some(self.begin_values()),
    {
        hide(joint::valid);hide(joint::step);hide(obligations::recover);hide(trajectory::outstanding);hide(trajectory::values);
        let issue=interval.check(self.obligations(owner.baseline(),id,offset));
        if issue.is_none() {
            owner.facts();self.source_bounds();interval.ordered();
            let steps=self.result->Ok_0.steps@;let events=interval.events;let keys=self.return_values().dom();
            endpoint::final_observation(steps,self.completion());endpoint::landed_domain(steps,word::initial(steps));
            assert(keys==endpoint::keys(steps));
            assert forall|i:int|0<=i<events.len() implies (#[trigger] events[i]).carrier().covered(owner.value_sources()) by {
                let e=events[i];assert(e is Produced);assert(e->Produced_0.producer==interval.producers[e.inverse().address]);
            }
            assert(link::covered(steps,events,owner.value_sources()));
            coverage::gaps_from_census(events,self.completion(),interval.end,keys);
            origins::available(events,self.obligations(owner.baseline(),id,offset),keys);
            link::linked_from_sources(steps,events,self.completion(),self.return_values(),self.obligations(owner.baseline(),id,offset),owner.value_sources());
            self.interleaved_progress(owner.baseline(),id,offset,events);
            coverage::tails_from_census(events,self.completion(),interval.end,keys);
            trajectory::endpoint::observe_matches(steps,events,self.completion(),interval.end,self.return_values());
        }
        issue
    }
}
}
