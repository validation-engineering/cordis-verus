//! Atomic scalar execution for data-only managed instructions. The shared
//! commit routine also implements prepared callback landing; inverse admission
//! always goes through the original execution owner and cleanup queue.
#[cfg(verus_keep_ghost)]
use super::Applied;
use super::{
    effect::{EffectError, Instruction},
    joint, Branch, ReversibleValue,
};
use crate::execution::{Execution, ValueAdmission};
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
use vstd::prelude::*;
verus! {
impl<V,C,G,Cb,X> Execution<V,C,G,ChildCleanup<Cb,X>> {
    pub fn apply_controlled_effect(&mut self,id:usize,target:&ReversibleValue,instruction:Instruction,branch:Branch,Tracked(cause):Tracked<joint::Receipt>)->(out:Result<ValueAdmission,EffectError>)
        requires old(self).wf(),cause.wf(),cause.journal()==target.journal_spec(),
        ensures out!=Err(EffectError::Interference),
            out!=Err(EffectError::Closed) ==> (out.is_ok()==super::effect::operation(instruction.model())(final(self).value_attempts().event().before()).is_some()),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            old(self).cleanup_state().live(id) ==> {
                let before=old(self).cleanup_state().queues()[id];let after=final(self).cleanup_state().queues()[id];
                &&& after.link()==before.link() && after.protocol().domain_id()==before.protocol().domain_id()
                &&& after.slots().len()>=before.slots().len() && after.slots().take(before.slots().len() as int)==before.slots()
                &&& after.issued()==before.issued() && after.protocol().selected()==before.protocol().selected()
            },
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            old(self).cleanup_state().live(id) ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                && final(self).cleanup_state().queues()[id].issued()==old(self).cleanup_state().queues()[id].issued()
                && final(self).cleanup_state().queues()[id].protocol().selected()==old(self).cleanup_state().queues()[id].protocol().selected(),
            final(self).execution_journal()==old(self).execution_journal(),
            out!=Err(EffectError::Closed) ==> final(self).value_attempts().events().last().follows(&cause),
            final(self).wf(),final(self).capture()==old(self).capture(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            final(self).effect_state()==old(self).effect_state(),final(self).checked_out()==old(self).checked_out(),
            final(self).initialized()==old(self).initialized(),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            final(self).cleanup_state().drained_failure()==old(self).cleanup_state().drained_failure(),
            (out==Err(EffectError::Closed))==!(old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)),
            out.is_err() ==> final(self).same_runtime(old(self)),
            out==Err(EffectError::Closed) ==> *final(self)==*old(self),
            out!=Err(EffectError::Closed) ==> final(self).value_attempts().appended(&old(self).value_attempts(),target),
            out.is_err() && out!=Err(EffectError::Closed) ==>
                super::attempt::effect_rejection(final(self).value_attempts().event(),instruction.model(),final(self).value_attempts().event().before(),out->Err_0),
            out.is_ok() ==> final(self).value_attempts().events().last().same(&out->Ok_0.registration().write()),
            out.is_ok() ==> super::joint::groups::registration(out->Ok_0.registration().insertion(),final(self).cleanup_state().link(),id),
            out.is_ok() ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link(),
            out.is_ok() ==> final(self).cleanup_state().acquisition_open(id)==old(self).cleanup_state().acquisition_open(id) && final(self).cleanup_state().live(id) && old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)
                && out->Ok_0.next==branch.selected(out->Ok_0.outcome)
                && out->Ok_0.token==old(self).cleanup_state().queues()[id].slots().len()
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(out->Ok_0.token)
                && final(self).cleanup_state().queues()[id].slots()==old(self).cleanup_state().queues()[id].slots().push(
                    final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int])
                && final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].is_some()
                && final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap() is Value
                && {
                    let inverse=final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap()->Value_0;
                    &&& out->Ok_0.registration().records(inverse,final(self).cleanup_state().queues()[id].link(),
                        final(self).cleanup_state().queues()[id].protocol().domain_id(),out->Ok_0.token)
                    &&& inverse.state().before==final(self).value_attempts().event().before()
                    &&& inverse.state().after==final(self).value_attempts().event().after()
                    &&& (Applied {outcome:out->Ok_0.outcome,next:out->Ok_0.next,pending:Tracked(None),inverse}).effect_corresponds(target,instruction.model(),branch)
                },
            final(self).status_links()==old(self).status_links(),
    {
        let mut access=None;
        self.apply_controlled_in(id,target,instruction,branch,Tracked(cause),&mut access)
    }

    #[allow(clippy::too_many_arguments)] // Optional access owns the same real cell.
    pub(crate) fn apply_controlled_in(&mut self,id:usize,target:&ReversibleValue,instruction:Instruction,branch:Branch,Tracked(cause):Tracked<joint::Receipt>,access:&mut Option<super::protected::Exclusive<'_>> )->(out:Result<ValueAdmission,EffectError>)
        requires old(access).is_some() ==> old(access)->Some_0.wf() && old(access)->Some_0.target()==*target,
            old(self).wf(),cause.wf(),cause.journal()==target.journal_spec(),
        ensures final(access).is_some()==old(access).is_some(),
            final(access).is_some() ==> final(access)->Some_0.wf() && final(access)->Some_0.target()==old(access)->Some_0.target()
                && (out.is_err() ==> final(access)->Some_0.state()==old(access)->Some_0.state())
                && (out!=Err(EffectError::Closed) ==> final(self).value_attempts().event().before()==old(access)->Some_0.state()
                    && final(self).value_attempts().event().after()==final(access)->Some_0.state()),
            out!=Err(EffectError::Interference),
            out!=Err(EffectError::Closed) ==> (out.is_ok()==super::effect::operation(instruction.model())(final(self).value_attempts().event().before()).is_some()),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            old(self).cleanup_state().live(id) ==> {
                let before=old(self).cleanup_state().queues()[id];let after=final(self).cleanup_state().queues()[id];
                &&& after.link()==before.link() && after.protocol().domain_id()==before.protocol().domain_id()
                &&& after.slots().len()>=before.slots().len() && after.slots().take(before.slots().len() as int)==before.slots()
                &&& after.issued()==before.issued() && after.protocol().selected()==before.protocol().selected()
            },
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            old(self).cleanup_state().live(id) ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                && final(self).cleanup_state().queues()[id].issued()==old(self).cleanup_state().queues()[id].issued()
                && final(self).cleanup_state().queues()[id].protocol().selected()==old(self).cleanup_state().queues()[id].protocol().selected(),
            final(self).execution_journal()==old(self).execution_journal(),
            out!=Err(EffectError::Closed) ==> final(self).value_attempts().events().last().follows(&cause),
            final(self).wf(),final(self).capture()==old(self).capture(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            final(self).effect_state()==old(self).effect_state(),final(self).checked_out()==old(self).checked_out(),
            final(self).initialized()==old(self).initialized(),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            final(self).cleanup_state().drained_failure()==old(self).cleanup_state().drained_failure(),
            (out==Err(EffectError::Closed))==!(old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)),
            out.is_err() ==> final(self).same_runtime(old(self)),
            out==Err(EffectError::Closed) ==> *final(self)==*old(self),
            out!=Err(EffectError::Closed) ==> final(self).value_attempts().appended(&old(self).value_attempts(),target),
            out.is_err() && out!=Err(EffectError::Closed) ==>
                super::attempt::effect_rejection(final(self).value_attempts().event(),instruction.model(),final(self).value_attempts().event().before(),out->Err_0),
            out.is_ok() ==> final(self).value_attempts().events().last().same(&out->Ok_0.registration().write()),
            out.is_ok() ==> super::joint::groups::registration(out->Ok_0.registration().insertion(),final(self).cleanup_state().link(),id),
            out.is_ok() ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link(),
            out.is_ok() ==> final(self).cleanup_state().acquisition_open(id)==old(self).cleanup_state().acquisition_open(id) && final(self).cleanup_state().live(id) && old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)
                && out->Ok_0.next==branch.selected(out->Ok_0.outcome)
                && out->Ok_0.token==old(self).cleanup_state().queues()[id].slots().len()
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(out->Ok_0.token)
                && final(self).cleanup_state().queues()[id].slots()==old(self).cleanup_state().queues()[id].slots().push(
                    final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int])
                && final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].is_some()
                && final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap() is Value
                && {
                    let inverse=final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap()->Value_0;
                    &&& out->Ok_0.registration().records(inverse,final(self).cleanup_state().queues()[id].link(),
                        final(self).cleanup_state().queues()[id].protocol().domain_id(),out->Ok_0.token)
                    &&& inverse.state().before==final(self).value_attempts().event().before()
                    &&& inverse.state().after==final(self).value_attempts().event().after()
                    &&& (Applied {outcome:out->Ok_0.outcome,next:out->Ok_0.next,pending:Tracked(None),inverse}).effect_corresponds(target,instruction.model(),branch)
                },
            final(self).status_links()==old(self).status_links(),
    {
        if !self.accepts_acquisition(id) {return Err(EffectError::Closed);}
        proof {self.representation();}
        let result=match access {
            Some(locked)=>locked.apply(instruction,branch,
                Ghost(joint::local(self.cleanup_state().queues()[id].link(),target.journal_spec())),Tracked(cause),Tracked(self.attempts.borrow_mut())),
            None=>super::effect::commit_calculation(target,super::effect::Calculation::Kernel(instruction),Ghost(instruction.model()),branch,
                Ghost(joint::local(self.cleanup_state().queues()[id].link(),target.journal_spec())),Tracked(cause),Tracked(self.attempts.borrow_mut())),
        };
        proof {self.representation();}
        let applied=result?;
        let outcome=applied.outcome;let next=applied.next;
        let registered=self.register_inverse(id,applied);
        Ok(ValueAdmission {outcome,next,token:registered.token,evidence:registered.evidence})
    }
}
}
