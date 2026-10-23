//! Specialized production checkpoints join actual managed slots to the same
//! publication, work and cleanup history without changing generic payload APIs.
use super::{history, NativeRuntime};
use crate::execution::Execution;
use crate::reversible_value::slot::{Evidence, ServiceSlot};
use vstd::prelude::*;

verus! {
impl<R,H,T,M> NativeRuntime<R,H,ServiceSlot<T,M>> {
    /// Includes retained publications even when they are no longer visible.
    pub fn service_snapshot(&self)->(out:history::Snapshot<ServiceSlot<T,M>>)
        requires self.wf(),
        ensures out.certified(),out.history()==self.execution_history(),out.positions()==self.history_positions(),out.key()==self.joint_key(),
            out.joint_spec().journal_spec()==self.journal_spec(),
            self.publications().slots_observed(self.journal_spec(),out.joint_spec().last()),
            self.publications().observations_complete(&out.joint_spec()),
    {
        let mut evidence=Evidence::new();self.services.collect_slots(&mut evidence);
        let journal=self.execution_journal();let view=journal.read();
        self.joint.certify(&view);evidence.certify(&view);
        proof {self.services.slots_certified(evidence,view.journal_spec(),view.state());}
        let joint=view.finish();
        proof {self.services.project_observations(&joint);self.execution_history().extend_indexed(self.history_positions(),self.joint.events(),joint.events(),self.joint_key());}
        history::Snapshot::new(joint,Ghost(self.execution_history()),Ghost(self.history_positions()),Ghost(self.joint_key()))
    }
    /// Collect the actual owner imports and provisions as well as published
    /// services, then certify them with work/cleanup in one held read epoch.
    pub fn service_episode_snapshot<C,G,I>(&self,id:usize,execution:&Execution<ServiceSlot<T,M>,C,G,I>)->(out:Option<history::Snapshot<ServiceSlot<T,M>>>)
        requires self.wf(),execution.wf(),execution.execution_journal()==Some(self.journal_spec()),
        ensures out.is_some()==self.owns_execution(id,execution),
            out.is_some() ==> out.unwrap().certified() && out.unwrap().history()==self.execution_history()
                && out.unwrap().positions()==self.history_positions() && out.unwrap().key()==self.joint_key()
                && execution.observed(&out.unwrap().joint_spec()) && execution.context_observed(&out.unwrap().joint_spec())
                && self.publications().slots_observed(self.journal_spec(),out.unwrap().joint_spec().last())
                && self.publications().observations_complete(&out.unwrap().joint_spec())
                && execution.value_state().is_some()
                && execution.value_state().unwrap().slots_observed(self.journal_spec(),out.unwrap().joint_spec().last())
                && execution.value_state().unwrap().observations_complete(&out.unwrap().joint_spec())
                && self.episode_owners()[id].owns(execution),
    {
        if !self.matches_execution(id,execution) {return None;}
        let mut evidence=Evidence::new();self.services.collect_slots(&mut evidence);
        let ghost prior=evidence;let values=execution.native().unwrap();values.collect_slots(&mut evidence);
        proof {self.services.slots_coverage_extends(prior,evidence);}
        let journal=self.execution_journal();let view=journal.read();
        self.joint.certify(&view);execution.certify(&view);evidence.certify(&view);
        proof {self.services.slots_certified(evidence,view.journal_spec(),view.state());values.slots_certified(evidence,view.journal_spec(),view.state());}
        let joint=view.finish();
        proof {self.services.project_observations(&joint);values.project_observations(&joint);execution.context_correspondence(&joint);self.execution_history().extend_indexed(self.history_positions(),self.joint.events(),joint.events(),self.joint_key());}
        Some(history::Snapshot::new(joint,Ghost(self.execution_history()),Ghost(self.history_positions()),Ghost(self.joint_key())))
    }
    /// The actual adapter's root/effect scope must select a live queue in the
    /// same checkpoint. This reuses one read epoch, adding no Journal lock.
    pub fn scoped_service_episode_snapshot<C,G,I,E>(&self,id:usize,execution:&Execution<ServiceSlot<T,M>,C,G,I>,control:&crate::poll_control::PollControl<E>,scope:&crate::setup_context::SetupScope)->(out:Option<history::Snapshot<ServiceSlot<T,M>>>)
        requires self.wf(),control.wf(),control.bound(self),execution.wf(),execution.execution_journal()==Some(self.journal_spec()),
        ensures out.is_some()==(scope.matches(execution) && self.owns_execution(id,execution) && control.matches(execution) && control.state().owner==id),
            out.is_some() ==> out.unwrap().certified() && out.unwrap().history()==self.execution_history()
                && out.unwrap().positions()==self.history_positions() && out.unwrap().key()==self.joint_key()
                && scope.observed_in(execution,&out.unwrap().joint_spec())
                && execution.context_observed(&out.unwrap().joint_spec()) && control.observed(&out.unwrap().joint_spec())
                && self.publications().slots_observed(self.journal_spec(),out.unwrap().joint_spec().last())
                && self.publications().observations_complete(&out.unwrap().joint_spec())
                && execution.value_state().is_some()
                && execution.value_state().unwrap().slots_observed(self.journal_spec(),out.unwrap().joint_spec().last())
                && execution.value_state().unwrap().observations_complete(&out.unwrap().joint_spec()),
    {
        if !scope.belongs(execution) {return None;}
        let snapshot=self.controlled_service_episode_snapshot(id,execution,control)?;
        proof {scope.observed(execution,&snapshot.joint_spec());}
        Some(snapshot)
    }
    /// The actual poll owner, committed slots and shared Episode at one epoch.
    pub fn controlled_service_episode_snapshot<C,G,I,E>(&self,id:usize,execution:&Execution<ServiceSlot<T,M>,C,G,I>,control:&crate::poll_control::PollControl<E>)->(out:Option<history::Snapshot<ServiceSlot<T,M>>>)
        requires self.wf(),control.wf(),control.bound(self),execution.wf(),execution.execution_journal()==Some(self.journal_spec()),
        ensures out.is_some()==(self.owns_execution(id,execution) && control.matches(execution) && control.state().owner==id),
            out.is_some() ==> out.unwrap().certified() && out.unwrap().history()==self.execution_history()
                && out.unwrap().positions()==self.history_positions() && out.unwrap().key()==self.joint_key()
                && execution.observed(&out.unwrap().joint_spec()) && execution.context_observed(&out.unwrap().joint_spec()) && control.observed(&out.unwrap().joint_spec())
                && self.publications().slots_observed(self.journal_spec(),out.unwrap().joint_spec().last())
                && self.publications().observations_complete(&out.unwrap().joint_spec())
                && execution.value_state().is_some()
                && execution.value_state().unwrap().slots_observed(self.journal_spec(),out.unwrap().joint_spec().last())
                && execution.value_state().unwrap().observations_complete(&out.unwrap().joint_spec())
                && self.episode_owners()[id].owns(execution),
    {
        if id!=control.owner() || !control.matches_execution(execution) || !self.matches_execution(id,execution) {return None;}
        let mut evidence=Evidence::new();self.services.collect_slots(&mut evidence);
        let ghost prior=evidence;let values=execution.native().unwrap();values.collect_slots(&mut evidence);
        proof {self.services.slots_coverage_extends(prior,evidence);}
        let journal=self.execution_journal();let view=journal.read();
        self.joint.certify(&view);execution.certify(&view);evidence.certify(&view);control.certify(&view);
        proof {self.services.slots_certified(evidence,view.journal_spec(),view.state());values.slots_certified(evidence,view.journal_spec(),view.state());}
        let joint=view.finish();
        proof {self.services.project_observations(&joint);values.project_observations(&joint);execution.context_correspondence(&joint);self.execution_history().extend_indexed(self.history_positions(),self.joint.events(),joint.events(),self.joint_key());}
        Some(history::Snapshot::new(joint,Ghost(self.execution_history()),Ghost(self.history_positions()),Ghost(self.joint_key())))
    }
}
}
