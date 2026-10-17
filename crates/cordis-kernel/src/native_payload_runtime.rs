//! Combined checkpoints for the production typed payload carrier.
use super::{history, NativeRuntime};
use crate::execution::Execution;
use crate::reversible_value::payload::{Evidence as PayloadEvidence, SharedPayload};
use crate::reversible_value::slot::{Evidence, ServiceSlot};
use vstd::prelude::*;
verus! {
impl<R,H,T:?Sized,M> NativeRuntime<R,H,ServiceSlot<SharedPayload<T>,M>> {
    /// Includes retained publications even when they are no longer visible.
    pub fn payload_service_snapshot(&self)->(out:history::Snapshot<ServiceSlot<SharedPayload<T>,M>>)
        requires self.wf(),
        ensures out.certified(),out.history()==self.execution_history(),out.positions()==self.history_positions(),out.key()==self.joint_key(),
            out.joint_spec().journal_spec()==self.journal_spec(),
            self.publications().slots_observed(self.journal_spec(),out.joint_spec().last()),
            self.publications().payloads_observed(self.journal_spec(),out.joint_spec().last()),
            self.publications().observations_complete(&out.joint_spec()),self.publications().payload_projections_complete(&out.joint_spec()),
    {
        let mut payloads=PayloadEvidence::new();self.services.collect_payloads(&mut payloads);
        let mut evidence=Evidence::new();self.services.collect_slots(&mut evidence);
        let journal=self.execution_journal();let view=journal.read();
        self.joint.certify(&view);evidence.certify(&view);payloads.certify(&view);
        proof {self.services.payloads_certified(payloads,view.journal_spec(),view.state());self.services.slots_certified(evidence,view.journal_spec(),view.state());}
        let joint=view.finish();
        proof {self.services.project_observations(&joint);self.services.project_payloads(&joint);self.execution_history().extend_indexed(self.history_positions(),self.joint.events(),joint.events(),self.joint_key());}
        history::Snapshot::new(joint,Ghost(self.execution_history()),Ghost(self.history_positions()),Ghost(self.joint_key()))
    }
    /// The actual poll owner, committed slots and shared Episode at one epoch.
    pub fn scoped_payload_service_episode_snapshot<C,G,I,E>(&self,id:usize,execution:&Execution<ServiceSlot<SharedPayload<T>,M>,C,G,I>,control:&crate::poll_control::PollControl<E>,scope:&crate::setup_context::SetupScope)->(out:Option<history::Snapshot<ServiceSlot<SharedPayload<T>,M>>>)
        requires self.wf(),control.wf(),control.bound(self),execution.wf(),execution.execution_journal()==Some(self.journal_spec()),
        ensures out.is_some()==(scope.matches(execution) && self.owns_execution(id,execution) && control.matches(execution) && control.state().owner==id),
            out.is_some() ==> out.unwrap().certified() && out.unwrap().history()==self.execution_history()
                && out.unwrap().positions()==self.history_positions() && out.unwrap().key()==self.joint_key()
                && scope.observed_in(execution,&out.unwrap().joint_spec()) && execution.observed(&out.unwrap().joint_spec()) && execution.context_observed(&out.unwrap().joint_spec()) && control.observed(&out.unwrap().joint_spec())
                && self.publications().payloads_observed(self.journal_spec(),out.unwrap().joint_spec().last())
                && self.publications().slots_observed(self.journal_spec(),out.unwrap().joint_spec().last())
                && self.publications().observations_complete(&out.unwrap().joint_spec()) && self.publications().payload_projections_complete(&out.unwrap().joint_spec())
                && execution.value_state().is_some()
                && execution.value_state().unwrap().payloads_observed(self.journal_spec(),out.unwrap().joint_spec().last())
                && execution.value_state().unwrap().slots_observed(self.journal_spec(),out.unwrap().joint_spec().last())
                && execution.value_state().unwrap().observations_complete(&out.unwrap().joint_spec()) && execution.value_state().unwrap().payload_projections_complete(&out.unwrap().joint_spec())
                && self.episode_owners()[id].owns(execution),
    {
        if !scope.belongs(execution) {return None;}
        if id!=control.owner() || !control.matches_execution(execution) || !self.matches_execution(id,execution) {return None;}
        let mut payloads=PayloadEvidence::new();self.services.collect_payloads(&mut payloads);
        let mut evidence=Evidence::new();self.services.collect_slots(&mut evidence);
        let ghost prior=evidence;let values=execution.native().unwrap();values.collect_slots(&mut evidence);
        proof {self.services.slots_coverage_extends(prior,evidence);}
        let ghost prior_payloads=payloads;values.collect_payloads(&mut payloads);
        proof {self.services.payloads_coverage_extends(prior_payloads,payloads);}
        let journal=self.execution_journal();let view=journal.read();
        self.joint.certify(&view);execution.certify(&view);evidence.certify(&view);payloads.certify(&view);control.certify(&view);
        proof {self.services.payloads_certified(payloads,view.journal_spec(),view.state());self.services.slots_certified(evidence,view.journal_spec(),view.state());values.slots_certified(evidence,view.journal_spec(),view.state());values.payloads_certified(payloads,view.journal_spec(),view.state());}
        let joint=view.finish();
        proof {self.services.project_observations(&joint);self.services.project_payloads(&joint);values.project_observations(&joint);values.project_payloads(&joint);execution.context_correspondence(&joint);scope.observed(execution,&joint);self.execution_history().extend_indexed(self.history_positions(),self.joint.events(),joint.events(),self.joint_key());}
        Some(history::Snapshot::new(joint,Ghost(self.execution_history()),Ghost(self.history_positions()),Ghost(self.joint_key())))
    }
}
}
