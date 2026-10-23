//! Actual native snapshot and producer reads for the final recovery query.
//! The result retains no runtime history or payload references; proof evidence
//! is erased. This call observes completed work and does not schedule cleanup.
#[cfg(verus_keep_ghost)]
use super::producer_capture::{payload_addresses, scalar_addresses};
use super::{unload_census::FinalCensus, RecordedExecution};
use crate::lifecycle_state::native::runtime::{
    control_source, episode::Unload, history::Snapshot, NativeRuntime,
};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::interleaving::completion;
use crate::reversible_value::{
    self as scalar,
    effect::ScalarEffect,
    managed::{root::RegisteredReport, Slot},
    payload,
};
use vstd::prelude::*;

verus! {
pub struct RecoveryCapture<A,R,T:?Sized,M,X> {
    pub cut:Snapshot<Slot<T,M>>,
    pub control:Result<control_source::Source<Slot<T,M>>,control_source::Error>,
    pub evidence:Ghost<FinalCensus<A,R,T,M,X>>,
    pub observations:Ghost<crate::lifecycle_state::native::runtime::history::recovery::Interval<Slot<T,M>>>,
    pub observation_issue:Ghost<Option<crate::lifecycle_state::native::runtime::history::recovery::Issue>>,
}
impl<A,R,T:?Sized,M,X> RecoveryCapture<A,R,T,M,X> {
    pub open spec fn source_bound(&self)->bool {
        self.control.is_ok() ==> self.control->Ok_0.certified() && self.control->Ok_0.cut()==self.cut
    }
}
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    /// Convenience entry for the actual result of RecordedExecution::release.
    /// Callers pass that result directly, without constructing a proof token.
    #[allow(clippy::too_many_arguments)] // Four inputs are used only in invocation/release proofs.
    pub fn capture_release_census<P,H,E:ScalarEffect>(&mut self,runtime:&NativeRuntime<P,H,Slot<T,M>>,
        _report:&RegisteredReport<E,T>,_id:usize,_offset:usize,_release:&super::native::ReleaseOutcome<A,R,T,M,X>,
        scalars:&[scalar::ReversibleValue],payloads:&[payload::SharedPayload<T>])->(out:RecoveryCapture<A,R,T,M,X>)
        requires crate::lifecycle_state::native::runtime::released(*_release),runtime.wf(),_report.unload_input(old(self),_id,_offset as nat,&_release.1@.unwrap()),
            _release.1@.unwrap().native()==runtime.joint_key(),_release.1@.unwrap().checkpoint().journal()==runtime.journal_spec(),
            exists|i:int|0<=i<runtime.child_records().unloads().len() && (#[trigger] runtime.child_records().unloads()[i]).same_source(&_release.1@.unwrap()),
            scalar_addresses(scalars@).union(payload_addresses(payloads@))==_report.return_values().dom(),
            forall|i:int|0<=i<scalars.len() ==> (#[trigger] scalars@[i]).journal_spec()==runtime.journal_spec(),
            forall|i:int|0<=i<payloads.len() ==> (#[trigger] payloads@[i]).journal_spec()==runtime.journal_spec(),
        ensures out.source_bound(),out.control.is_ok()==(runtime.recording_status()==control_source::Status::Recording),
            final(self).wf(),final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),
            final(self).histories()==old(self).histories(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),final(self).value_sources().extends(old(self).value_sources()),
            out.cut.certified(),runtime.child_records().cut_source(&out.cut),out.cut.key()==runtime.joint_key(),
            out.observations@.wf(),out.observations@.source==out.cut,out.observations@.start==_report.start().at(),out.observations@.normalized(),
            out.observation_issue@.is_none()==out.observations@.balanced(out.observations@.scope()),
            out.observation_issue@.is_none() ==> out.observations@.recovered_all(),
            out.observation_issue@.is_some() ==> out.observations@.diagnosed(out.observations@.scope(),out.observation_issue@.unwrap()),
            _report.interval_source(final(self),out.evidence@.interval),
            out.evidence@.interval.end.journal()==out.cut.joint_spec().journal_spec(),out.evidence@.interval.end.events()==out.cut.joint_spec().events(),
            out.evidence@.issue.is_none()==(out.evidence@.interval.clear(_report.obligations(final(self).baseline(),_id,_offset as nat))
                && completion::foreign_settled(out.evidence@.interval.events,out.evidence@.interval.producers.dom())
                && final(self).native_children_resolved(&runtime.child_records())),
            out.evidence@.issue.is_some() ==> out.evidence@.diagnosed(final(self),_report.obligations(final(self).baseline(),_id,_offset as nat),&runtime.child_records()),
            out.evidence@.issue.is_none() ==> _report.recovered_values_at_cut(out.evidence@.interval.events,&out.cut)==_report.begin_values()
                && final(self).native_children_terminal(&runtime.child_records(),&out.cut)
                && _report.writes_registered_at_cut(&out.cut.joint_spec())
                && _report.start().recorded(out.cut.joint_spec().events()) && _release.1@.unwrap().recorded(out.cut.joint_spec().events()),
    {
        let tracked end=match _release.1.borrow() {Some(end)=>end,None=>{assert(false);proof_from_false()}};
        self.capture_unload_census(runtime,_report,_id,_offset,Tracked(end),scalars,payloads)
    }
    #[allow(clippy::too_many_arguments)] // Four inputs are used only in invocation/release proofs.
    pub fn capture_unload_census<P,H,E:ScalarEffect>(&mut self,runtime:&NativeRuntime<P,H,Slot<T,M>>,
        _report:&RegisteredReport<E,T>,_id:usize,_offset:usize,Tracked(end):Tracked<&Unload>,
        scalars:&[scalar::ReversibleValue],payloads:&[payload::SharedPayload<T>])->(out:RecoveryCapture<A,R,T,M,X>)
        requires runtime.wf(),_report.unload_input(old(self),_id,_offset as nat,end),
            end.native()==runtime.joint_key(),end.checkpoint().journal()==runtime.journal_spec(),
            exists|i:int|0<=i<runtime.child_records().unloads().len() && (#[trigger] runtime.child_records().unloads()[i]).same_source(end),
            scalar_addresses(scalars@).union(payload_addresses(payloads@))==_report.return_values().dom(),
            forall|i:int|0<=i<scalars.len() ==> (#[trigger] scalars@[i]).journal_spec()==runtime.journal_spec(),
            forall|i:int|0<=i<payloads.len() ==> (#[trigger] payloads@[i]).journal_spec()==runtime.journal_spec(),
        ensures out.source_bound(),out.control.is_ok()==(runtime.recording_status()==control_source::Status::Recording),
            final(self).wf(),final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),
            final(self).histories()==old(self).histories(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),final(self).value_sources().extends(old(self).value_sources()),
            out.cut.certified(),runtime.child_records().cut_source(&out.cut),out.cut.key()==runtime.joint_key(),
            out.observations@.wf(),out.observations@.source==out.cut,out.observations@.start==_report.start().at(),out.observations@.normalized(),
            out.observation_issue@.is_none()==out.observations@.balanced(out.observations@.scope()),
            out.observation_issue@.is_none() ==> out.observations@.recovered_all(),
            out.observation_issue@.is_some() ==> out.observations@.diagnosed(out.observations@.scope(),out.observation_issue@.unwrap()),
            _report.interval_source(final(self),out.evidence@.interval),
            out.evidence@.interval.end.journal()==out.cut.joint_spec().journal_spec(),out.evidence@.interval.end.events()==out.cut.joint_spec().events(),
            out.evidence@.issue.is_none()==(out.evidence@.interval.clear(_report.obligations(final(self).baseline(),_id,_offset as nat))
                && completion::foreign_settled(out.evidence@.interval.events,out.evidence@.interval.producers.dom())
                && final(self).native_children_resolved(&runtime.child_records())),
            out.evidence@.issue.is_some() ==> out.evidence@.diagnosed(final(self),_report.obligations(final(self).baseline(),_id,_offset as nat),&runtime.child_records()),
            out.evidence@.issue.is_none() ==> _report.recovered_values_at_cut(out.evidence@.interval.events,&out.cut)==_report.begin_values()
                && final(self).native_children_terminal(&runtime.child_records(),&out.cut)
                && _report.writes_registered_at_cut(&out.cut.joint_spec())
                && _report.start().recorded(out.cut.joint_spec().events()) && end.recorded(out.cut.joint_spec().events()),
    {
        let cut=runtime.publication_snapshot();
        proof {
            let ledger=runtime.child_records();
            let i=choose|i:int|0<=i<ledger.unloads().len() && (#[trigger] ledger.unloads()[i]).same_source(end);
            assert(ledger.unloads()[i].checkpoint().events()==end.checkpoint().events());
            assert(cut.joint_spec().covers(&end.checkpoint()));
            assert(cut.joint_spec().events().take(_report.completion().events().len() as int) =~= _report.completion().events());
        }
        let tracked start=_report.completion_witness();
        let _endpoint=cut.joint().checkpoint_receipt();
        let journal=runtime.execution_journal();
        let _interval=self.capture_recovery_interval(&journal,scalars,payloads,Tracked(start),Tracked(_endpoint.borrow()));
        proof {
            assert forall|i:int|0<=i<_report.result->Ok_0.steps.len() implies (#[trigger] _report.result->Ok_0.steps@[i]).carrier().covered(self.value_sources()) by {}
        }
        let ghost evidence=_report.unload_census(self,_id,_offset as nat,end,&runtime.child_records(),&cut,_interval@);
        proof {
            _report.source_bounds();_report.start().facts();
            assert(cut.joint_spec().events().take(_report.start().checkpoint().events().len() as int) =~= _report.start().checkpoint().events());
        }
        let ghost observations=cut.recovery_since_begin(&_report.start());
        let ghost observation_issue=observations.check_all();
        let control=runtime.bind_control_source(&cut);
        RecoveryCapture {cut,control,evidence:Ghost(evidence),observations:Ghost(observations),observation_issue:Ghost(observation_issue)}
    }
}
}
