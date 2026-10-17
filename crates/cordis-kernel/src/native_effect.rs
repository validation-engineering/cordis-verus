//! Two-phase native effects: checked declaration/owner capture, unlocked user
//! calculation, then checked landing of the exact retained object and inverse.
//! Slot replacement cannot retarget a computation already prepared.
use super::cursor::{Owner, StartError};
use super::effect::{EffectError, Prepared, ScalarEffect};
use super::slot::{ServiceBinding, ServiceSlot};
use super::{access, Branch};
#[cfg(verus_keep_ghost)]
use super::{alias, effect, joint, Applied};
use crate::execution::Execution;
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
use crate::lifecycle_state::services::NativeEpisode;
use crate::Port;
use vstd::prelude::*;

verus! {
#[allow(dead_code)] // The actual admission context is erased, not cloned.
pub struct Capture<T,M> {binding:ServiceBinding,owner:Owner,episode:Ghost<NativeEpisode<ServiceSlot<T,M>>>}
impl<T,M> Capture<T,M> {
    pub closed spec fn binding(&self)->ServiceBinding {self.binding}
    pub closed spec fn owner(&self)->Owner {self.owner}
    pub closed spec fn episode(&self)->NativeEpisode<ServiceSlot<T,M>> {self.episode@}
    pub closed spec fn wf(&self)->bool {access::selected(self.episode(),self.binding())}
    /// Called after releasing the episode mutex; arbitrary compute never runs
    /// under the value lock either. The input is read from this retained capture.
    /// Join the prior instruction with this actual slot selection before
    /// observing the retained value. Foreign Journals keep separate orders.
    pub(crate) fn prepare_following<E:ScalarEffect>(self,effect:E,Tracked(previous):Tracked<&super::registration::ReceiptMap>)->(out:Computation<T,M>)
        requires self.wf(),super::registration::witnesses(*previous),
        ensures out.wf(),out.capture()==self,out.prepared().code()==effect.model(),
            forall|k:(int,bool)|previous.contains_key(k) && #[trigger] previous[k].journal()==out.prepared().cause().journal() ==> out.prepared().cause().covers(&previous[k]),
    {
        let snapshot0=self.binding.capture().observe_value();
        proof {assert(snapshot0.joint_spec().events().len()>0);}
        let Tracked(selection)=snapshot0.joint_execution().checkpoint_receipt();
        let (journal,Tracked(_object))=self.binding.value().reference();
        let Tracked(cause)=journal.join_receipts::<(int,bool)>(Tracked(previous),Tracked(Some(selection.duplicate())));
        let snapshot=self.binding.value().snapshot_following(Tracked(cause.tracked_borrow()));
        let prepared=self.binding.value().prepare_observed(effect,snapshot);
        proof {
            prepared.read_evidence();
            if selection.journal()==journal {
                prepared.cause().cover_through(&cause.unwrap(),&selection);
                if self.binding.capture_spec().commit().journal()==journal {prepared.cause().cover_through(&selection,&self.binding.capture_spec().commit());}
            }
            assert forall|k:(int,bool)|previous.contains_key(k) && #[trigger] previous[k].journal()==prepared.cause().journal() implies prepared.cause().covers(&previous[k]) by {
                prepared.cause().cover_through(&cause.unwrap(),&previous[k]);
            }
        }
        Computation {capture:self,prepared}
    }
    pub fn prepare<E:ScalarEffect>(self,effect:E)->(out:Computation<T,M>)
        requires self.wf(),
        ensures out.wf(),out.capture()==self,out.prepared().code()==effect.model(),
    {
        let snapshot=self.binding.capture().observe_value();
        let prepared=self.binding.value().prepare_observed(effect,snapshot);
        proof {
            prepared.read_evidence();
            assert(prepared.observation()==snapshot);
            assert(prepared.cause().events()==snapshot.joint_spec().events());
            if self.binding.capture_spec().commit().journal()==prepared.cause().journal() {
                assert(self.binding.capture_spec().commit().journal()==snapshot.journal_spec());
                assert(prepared.cause().covers(&self.binding.capture_spec().commit()));
            }
        }
        Computation {capture:self,prepared}
    }
}
pub struct Computation<T,M> {capture:Capture<T,M>,prepared:Prepared}
impl<T,M> Computation<T,M> {
    pub proof fn provenance(&self)
        requires self.wf(),
        ensures access::selected(self.capture().episode(),self.capture().binding()),
            self.prepared().target()==*self.capture().binding().capture_spec().value_spec(),
    {}
    pub closed spec fn capture(&self)->Capture<T,M> {self.capture}
    pub closed spec fn prepared(&self)->Prepared {self.prepared}
    pub closed spec fn wf(&self)->bool {
        self.capture().wf() && self.prepared().wf()
            && self.prepared().target()==*self.capture().binding().capture_spec().value_spec()
            && (self.capture().binding().capture_spec().commit().journal()==self.prepared().cause().journal() ==>
                self.prepared().cause().covers(&self.capture().binding().capture_spec().commit()))
    }
}
impl access::Write {
    pub open spec fn computed(&self,code:effect::Code,branch:Branch)->bool {
        let event=self.admission.registration().write().event().change;
        &&& self.certified() && event is Value && event->Value_event is Computed
        &&& event->Value_event->Computed_code==code && event->Value_event->Computed_branch==branch
        &&& event->Value_event->Computed_outcome==self.admission.outcome && event->Value_event->Computed_next==self.admission.next
        &&& self.admission.next==branch.selected(self.admission.outcome)
    }
    /// Actual production input/output, continuation, strict inverse and alias
    /// frame for the context that admitted this native root/Child/group call.
    pub proof fn effect_semantics<T,M>(&self,episode:NativeEpisode<ServiceSlot<T,M>>,code:effect::Code,branch:Branch)
        requires self.computed(code,branch),access::selected(episode,self.binding),
        ensures {
            let receipt=self.admission.registration().write();let before=joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
            let run=crate::dependent_grammar::run(alias::library(),alias::node(receipt.event().key,code,branch),access::objects(before));
            &&& run.is_some() && run.unwrap().state==access::objects(after) && run.unwrap().next==self.admission.next
            &&& forall|state:Map<nat,super::ValueState>| #[trigger] (run.unwrap().undo)(state)==
                if state.contains_key(receipt.event().key) && state[receipt.event().key]==receipt.event().change->Value_event.after()
                    {Some(state.insert(receipt.event().key,receipt.event().change->Value_event.before()))} else {None}
            &&& crate::lifecycle_state::services::slots::value_frame(episode.owned(),receipt.journal(),before,after,receipt.event().key)
            &&& crate::lifecycle_state::services::slots::value_frame(episode.imports(),receipt.journal(),before,after,receipt.event().key)
            &&& alias::targets(episode.owned(),receipt.journal(),after)==alias::targets(episode.owned(),receipt.journal(),before)
            &&& alias::targets(episode.imports(),receipt.journal(),after)==alias::targets(episode.imports(),receipt.journal(),before)
        },
    {
        let receipt=self.admission.registration().write();let before=joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
        alias::computed(before,after,receipt.event());self.service_frame(episode);
        alias::production_value(episode.owned(),receipt.journal(),before,after,receipt.event());
        alias::production_value(episode.imports(),receipt.journal(),before,after,receipt.event());
    }
    /// A checkable condition on the real write checkpoint recovers the paper's
    /// literal single-key update. It is not asserted for retained old targets
    /// or for two current service names aliasing this object.
    pub proof fn single_key_effect<K,T,M>(&self,values:Map<K,std::sync::Arc<ServiceSlot<T,M>>>,key:K,code:effect::Code,branch:Branch)
        requires self.computed(code,branch),
            alias::single_binding(alias::targets(values,self.admission.registration().write().journal(),
                joint::state_at(self.admission.registration().write().events(),self.admission.registration().write().at())),key,self.admission.registration().write().event().key),
        ensures {
            let receipt=self.admission.registration().write();let before=joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
            let targets=alias::targets(values,receipt.journal(),before);
            let paper=crate::dependent_grammar::run(alias::library(),alias::node(key,code,branch),alias::view(targets,access::objects(before)));
            &&& paper.is_some() && paper.unwrap().state==alias::view(alias::targets(values,receipt.journal(),after),access::objects(after))
            &&& paper.unwrap().next==self.admission.next
        },
    {
        let receipt=self.admission.registration().write();let before=joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
        alias::production_targets(values,receipt.journal(),before);alias::computed(before,after,receipt.event());
        alias::production_value(values,receipt.journal(),before,after,receipt.event());
        alias::single_key_refinement(alias::targets(values,receipt.journal(),before),access::objects(before),key,receipt.event().key,code,branch);
    }
}
impl<T,M,C,G,Cb,X> Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>> {
    /// Small executable admission boundary, reused by the actual landing path.
    fn admits_native_effect(&self,id:usize,owner:&Owner)->(out:bool)
        requires self.wf(),
        ensures out==(self.work_state().accepts() && self.cleanup_state().acquisition_open(id) && owner.matches(self,id)),
    {
        if !self.accepts_acquisition(id) {return false;}
        owner.check(self,id)
    }
    pub fn capture_native_effect(&self,id:usize,port:Port)->(out:Result<Capture<T,M>,StartError>)
        requires self.wf(),
        ensures out.is_err() ==> match out->Err_0 {
                StartError::Closed=>!self.work_state().accepts() || !self.cleanup_state().acquisition_open(id),
                StartError::NoNativeOwner=>self.value_state().is_none(),
                StartError::Read(error)=>self.value_state().is_some() && self.value_state().unwrap().reversible_read_failed(port,error),
            },
            out.is_ok() ==> out->Ok_0.wf() && self.value_state().is_some()
            && out->Ok_0.episode()==self.value_state().unwrap() && out->Ok_0.binding().port_spec()==port
            && out->Ok_0.owner().matches(self,id),
            (out.is_err() && out->Err_0 is Closed)==!(self.work_state().accepts() && self.cleanup_state().acquisition_open(id)),
    {
        if !self.accepts_acquisition(id) {return Err(StartError::Closed);}
        let native=match self.native() {Some(native)=>native,None=>return Err(StartError::NoNativeOwner)};
        let binding=match native.read_reversible(port) {Ok(binding)=>binding,Err(error)=>return Err(StartError::Read(error))};
        proof {access::selection_declared(*native,binding);}
        let owner=Owner::capture(self,id);
        Ok(Capture {binding,owner,episode:Ghost(*native)})
    }
    /// The owner ticket/work/queue identity and current acquisition state are
    /// checked again after calculation. Host instance identity is still the
    /// ordinary adapter's responsibility, as for resumable program cursors.
    #[verifier::rlimit(30)]
    pub fn apply_native_effect(&mut self,id:usize,computation:Computation<T,M>,branch:Branch)->(out:Result<access::Write,EffectError>)
        requires old(self).wf(),computation.wf(),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).capture()==old(self).capture(),final(self).value_state()==old(self).value_state(),
            final(self).work_state()==old(self).work_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> final(self).same_runtime(old(self)),
            (out==Err(EffectError::Closed))==!(old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)
                && computation.capture().owner().matches(old(self),id)),
            out==Err(EffectError::Closed) ==> *final(self)==*old(self),
            out!=Err(EffectError::Closed) ==> final(self).value_attempts().appended(&old(self).value_attempts(),&computation.prepared().target())
                && final(self).value_attempts().events().last().follows(&computation.prepared().cause()),
            out.is_err() && out!=Err(EffectError::Closed) ==> super::attempt::effect_rejection(final(self).value_attempts().event(),computation.prepared().code(),computation.prepared().expected(),out->Err_0)
                && joint::state_at(final(self).value_attempts().events().last().events(),final(self).value_attempts().events().last().at())==final(self).value_attempts().events().last().events().last().state
                && joint::pending_at(final(self).value_attempts().events().last().events(),final(self).value_attempts().events().last().at())==final(self).value_attempts().events().last().events().last().pending,
            out.is_ok() ==> {
                let report=out->Ok_0;
                &&& report.binding==computation.capture().binding() && report.computed(computation.prepared().code(),branch)
                &&& report.admission.registration().write().follows(&computation.prepared().cause())
                &&& final(self).cleanup_state().acquisition_open(id)==old(self).cleanup_state().acquisition_open(id)
                &&& report.recorded(*final(self),id) && access::selected(computation.capture().episode(),report.binding)
                &&& report.admission.token==old(self).cleanup_state().queues()[id].slots().len()
                &&& final(self).cleanup_state().queues()[id].slots().len()==old(self).cleanup_state().queues()[id].slots().len()+1
                &&& final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(report.admission.token)
                &&& final(self).cleanup_state().queues()[id].slots().take(report.admission.token as int)==old(self).cleanup_state().queues()[id].slots()
                &&& (Applied {outcome:report.admission.outcome,next:report.admission.next,pending:Tracked(None),
                    inverse:final(self).cleanup_state().queues()[id].slots()[report.admission.token as int].unwrap()->Value_0})
                    .effect_corresponds(&computation.prepared().target(),computation.prepared().code(),branch)
            },
            final(self).status_links()==old(self).status_links(),
    {
        if !self.admits_native_effect(id,&computation.capture.owner) {return Err(EffectError::Closed);}
        let ghost code=computation.prepared.code();let ghost cause=computation.prepared.cause();
        let ghost episode=computation.capture.episode();
        let binding=computation.capture.binding;
        let admission=match self.apply_prepared_effect(id,computation.prepared,branch) {
            Ok(admission)=>admission,
            Err(error)=>{proof {self.value_attempts().rejection_step();}return Err(error);},
        };
        proof {
            if binding.capture_spec().commit().journal()==cause.journal() {
                admission.registration().write().after_cover(&cause,&binding.capture_spec().commit());
            }
        }
        let report=access::Write {binding,admission};
        proof {report.effect_semantics(episode,code,branch);report.general_semantics();}
        Ok(report)
    }
}
}
