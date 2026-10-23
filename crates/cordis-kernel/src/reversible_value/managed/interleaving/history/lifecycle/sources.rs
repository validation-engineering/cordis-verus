//! Ownership of the actual typed source evidence used by recorded recovery.
use super::RecordedExecution;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::{
    episode::endpoint,
    interleaving::{
        self as trajectory, obligations,
        sources::{coverage, link, origins},
    },
    recovery::word,
};
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{history::sources::Sources, managed::Report, payload};
use vstd::prelude::*;

verus! {
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    pub open spec fn sources_for_history(&self,id:usize)->bool {
        forall|i:int|0<=i<self.histories()[id].events().len() ==> (#[trigger] self.histories()[id].events()[i]).carrier().covered(self.value_sources())
    }
    /// Observe the result of the real raw payload restoration API. The actual
    /// Attempt resource supplies both its typed history and common read/write
    /// checkpoint, so a caller cannot invent an external payload value.
    pub proof fn observe_payload_restore(tracked &mut self,tracked attempt:&payload::restoration::attempt::Attempt<T>)
        requires old(self).wf(),attempt.wf(),
        ensures final(self).wf(),final(self).value_sources().extends(old(self).value_sources()),
            trajectory::Event::<A,R,T,M,X>::Restore(trajectory::Attempt::Payload(*attempt)).carrier().covered(final(self).value_sources()),
            final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|id:usize|#[trigger] old(self).histories().contains_key(id) ==> {
                &&& final(self).histories()[id].initial()==old(self).histories()[id].initial()
                &&& final(self).histories()[id].current()==old(self).histories()[id].current()
                &&& final(self).histories()[id].events()==old(self).histories()[id].events().push(trajectory::Event::Restore(trajectory::Attempt::Payload(*attempt)))
            },
            old(self).recovery_boundary().is_some() ==> final(self).recovery_boundary().is_some() && final(self).recovery_boundary().unwrap().covers(&old(self).recovery_boundary().unwrap()),
            old(self).core().execution_journal()==Some(attempt.endpoint().journal()) ==>
                final(self).recovery_boundary().is_some() && final(self).recovery_boundary().unwrap().covers(&attempt.endpoint()),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        self.facts();attempt.boundaries();
        let tracked witness=attempt.history_witness();
        if let Some(witness)=witness {self.value_sources.borrow_mut().retain(witness);}
        reveal(RecordedExecution::wf);
        self.observe_foreign(trajectory::Event::Restore(trajectory::Attempt::Payload(*attempt)));
        let tracked boundary=Some(attempt.completion_cause());self.join_boundary(&boundary);
    }
    pub(crate) proof fn capture_report(tracked &mut self,tracked report:&Report<T>)
        requires old(self).wf(),report.witnessed(),
        ensures final(self).wf(),final(self).value_sources().extends(old(self).value_sources()),
            final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).histories()==old(self).histories(),final(self).terminal()==old(self).terminal(),final(self).recovery_boundary()==old(self).recovery_boundary(),
            forall|i:int|0<=i<report.steps.len() ==> (#[trigger] report.steps@[i]).carrier().covered(final(self).value_sources()),
    {
        self.facts();self.value_sources.borrow_mut().retain_report(report);
        reveal(RecordedExecution::wf);
    }
    pub(crate) proof fn merge_sources(tracked &mut self,tracked incoming:&Sources<payload::State<T>>)
        requires old(self).wf(),incoming.wf(),
        ensures final(self).wf(),final(self).value_sources().extends(old(self).value_sources()),final(self).value_sources().extends(*incoming),
            final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).histories()==old(self).histories(),final(self).terminal()==old(self).terminal(),final(self).recovery_boundary()==old(self).recovery_boundary(),
    {
        self.facts();self.value_sources.borrow_mut().merge(incoming);
        reveal(RecordedExecution::wf);
    }
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    /// Census the full shared Journal up to this real checkpoint. Only actual
    /// changing frames require a producer; unrelated lifecycle activity and
    /// genuine no-op failures may remain outside the projected value sequence.
    pub open spec fn observer_census<C,G,A,R,M,X>(&self,owner:RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,end:crate::reversible_value::joint::Receipt)->bool {
        let events=owner.histories()[id].events();let keys=self.return_values().dom();
        &&& forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> (#[trigger] self.result->Ok_0.steps@[i]).carrier().covered(owner.value_sources())
        &&& owner.source_order(id,self.completion())
        &&& coverage::complete(events,self.completion(),end,keys)
        &&& origins::admitted(events,self.obligations(owner.baseline(),id,offset),keys)
    }
    pub proof fn source_from_observer_census<C,G,A,R,M,X>(&self,owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,end:crate::reversible_value::joint::Receipt)
        requires self.observer_census(*owner,id,offset,end),
        ensures self.recorded_source(*owner,id,offset),
    {coverage::gaps_from_census(owner.histories()[id].events(),self.completion(),end,self.return_values().dom());}
    /// At a covered actual endpoint the remaining inverse word recovers Begin.
    /// The endpoint value is decoded from the Journal, not from an expected heap.
    pub proof fn recover_observer_censused_prefix<C,G,A,R,M,X>(&self,owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,end:crate::reversible_value::joint::Receipt)
        requires owner.wf(),owner.histories().contains_key(id),owner.baseline().cleanup_state().live(id),
            self.observer_census(*owner,id,offset,end),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner.baseline(),id,offset),crate::reversible_value::managed::retained(self.result->Ok_0.steps@,owner.baseline(),id,offset),
        ensures {
            let events=owner.histories()[id].events();let initial=self.return_values();
            obligations::recover(trajectory::outstanding(events,self.obligations(owner.baseline(),id,offset),initial.dom(),events.len()),
                trajectory::endpoint::observe(self.result->Ok_0.steps@,events,end))==Some(self.begin_values())
        },
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        hide(trajectory::outstanding);hide(trajectory::values);hide(obligations::recover);
        self.source_from_observer_census(owner,id,offset,end);self.recover_recorded_prefix(owner,id,offset);
        self.source_bounds();let steps=self.result->Ok_0.steps@;let events=owner.histories()[id].events();
        endpoint::final_observation(steps,self.completion());endpoint::landed_domain(steps,word::initial(steps));
        assert(self.return_values().dom()==endpoint::keys(steps));
        coverage::tails_from_census(events,self.completion(),end,self.return_values().dom());
        trajectory::endpoint::observe_matches(steps,events,self.completion(),end,self.return_values());
    }
    /// Successful native Unload is connected to the same census. Neither
    /// per-read quiet gaps nor a separately supplied quiet tail is required.
    pub proof fn unload_from_observer_census<C,G,A,R,M,X>(&self,owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,end:&crate::lifecycle_state::native::runtime::episode::Unload)
        requires self.observer_census(*owner,id,offset,end.checkpoint()),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            end.wf(),end.owner()==self.start().owner(),end.native()==self.start().native(),
        ensures self.recorded_source(*owner,id,offset),self.unload_source(owner.histories()[id].events(),end),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        self.source_from_observer_census(owner,id,offset,end.checkpoint());self.source_bounds();
        let steps=self.result->Ok_0.steps@;
        endpoint::final_observation(steps,self.completion());endpoint::landed_domain(steps,word::initial(steps));
        assert(self.return_values().dom()==endpoint::keys(steps));
        coverage::tails_from_census(owner.histories()[id].events(),self.completion(),end.checkpoint(),self.return_values().dom());
    }

    /// Source-only guards over the real owned histories. Inverse availability
    /// excludes restorations whose creating write was outside this interval.
    pub open spec fn recorded_source<C,G,A,R,M,X>(&self,owner:RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat)->bool {
        let events=owner.histories()[id].events();let initial=self.return_values();
        &&& forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> (#[trigger] self.result->Ok_0.steps@[i]).carrier().covered(owner.value_sources())
        &&& link::ordered(events,self.completion()) && link::gaps(events,self.completion(),initial.dom())
        &&& origins::admitted(events,self.obligations(owner.baseline(),id,offset),initial.dom())
    }
    pub proof fn link_recorded_source<C,G,A,R,M,X>(&self,owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat)
        requires owner.wf(),owner.histories().contains_key(id),self.recorded_source(*owner,id,offset),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
        ensures trajectory::linked(owner.histories()[id].events(),self.completion(),self.return_values(),self.obligations(owner.baseline(),id,offset)),
    {
        owner.facts();self.source_bounds();let steps=self.result->Ok_0.steps@;
        endpoint::final_observation(steps,self.completion());endpoint::landed_domain(steps,word::initial(steps));
        assert(self.return_values().dom()==endpoint::keys(steps));
        assert(link::covered(steps,owner.histories()[id].events(),owner.value_sources()));
        origins::available(owner.histories()[id].events(),self.obligations(owner.baseline(),id,offset),self.return_values().dom());
        link::linked_from_sources(steps,owner.histories()[id].events(),self.completion(),self.return_values(),self.obligations(owner.baseline(),id,offset),owner.value_sources());
    }
    /// Equation (55)'s strict managed specialization at any recorded prefix:
    /// the real remaining inverse word is defined and recovers the Begin values.
    /// It allows foreign writes and failed attempts, without requiring drain.
    pub proof fn recover_recorded_prefix<C,G,A,R,M,X>(&self,owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat)
        requires owner.wf(),owner.histories().contains_key(id),owner.baseline().cleanup_state().live(id),self.recorded_source(*owner,id,offset),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner.baseline(),id,offset),crate::reversible_value::managed::retained(self.result->Ok_0.steps@,owner.baseline(),id,offset),
        ensures {
            let events=owner.histories()[id].events();let initial=self.return_values();
            obligations::recover(trajectory::outstanding(events,self.obligations(owner.baseline(),id,offset),initial.dom(),events.len()),trajectory::values(events,initial,events.len()))==Some(self.begin_values())
        },
    {
        owner.facts();self.link_recorded_source(owner,id,offset);
        self.interleaved_progress(owner.baseline(),id,offset,owner.histories()[id].events());
    }
}
}
