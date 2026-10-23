//! Borrowed exclusive access to the real scalar cell. No shadow storage is
//! allocated. Both ordinary and protected execution call the same locked core.
use super::{
    attempt, effect, joint, Applied, Branch, Cell, Predicate, ReversibleValue, Snapshot, ValueState,
};
use vstd::prelude::*;
use vstd::rwlock::WriteHandle;

verus! {
pub(crate) struct Exclusive<'a> {
    target:&'a ReversibleValue,
    cell:Cell,
    guard:WriteHandle<'a,Cell,Predicate>,
}
impl ReversibleValue {
    pub(crate) fn acquire_exclusive(&self)->(out:Exclusive<'_>)
        ensures out.wf(),out.target()==*self,
    {
        let (cell,guard)=self.inner.acquire_write();
        Exclusive {target:self,cell,guard}
    }
}
impl<'a> Exclusive<'a> {
    pub(crate) closed spec fn target(&self)->ReversibleValue {*self.target}
    pub(crate) closed spec fn state(&self)->ValueState {self.cell.state}
    pub(crate) closed spec fn wf(&self)->bool {
        self.guard.rwlock()==*self.target.inner && self.target.inner.inv(self.cell)
    }
    pub(crate) fn snapshot_following(&self,Tracked(cause):Tracked<&joint::Receipt>)->(out:Snapshot)
        requires self.wf(),cause.wf(),
        ensures out.certified(),out.state()==self.state(),out.source()==self.target().source(),
            out.object()==self.target().object(),out.journal_spec()==self.target().journal_spec(),
            cause.journal()==self.target().journal_spec() ==> cause.events().len()<=out.joint_spec().events().len()
                && out.joint_spec().events().take(cause.events().len() as int)==cause.events(),
    {self.cell.snapshot_following(Tracked(cause))}
    pub(crate) fn journal(&self)->(out:joint::Journal)
        requires self.wf(),ensures out==self.target().journal_spec(),
    {self.cell.joint.domain()}
    pub(crate) fn state_value(&self)->(out:ValueState)
        requires self.wf(),ensures out==self.state(),
    {self.cell.state}
    /// A closed instruction holds the same cell throughout the read and write.
    /// Between successive mutable borrows its state cannot be changed by an alias.
    pub(crate) fn apply(&mut self,instruction:effect::Instruction,branch:Branch,
        Ghost(managed):Ghost<bool>,Tracked(cause):Tracked<joint::Receipt>,Tracked(attempts):Tracked<&mut attempt::Ledger>)
        ->(out:Result<Applied,effect::EffectError>)
        requires old(self).wf(),cause.wf(),cause.journal()==old(self).target().journal_spec(),old(attempts).wf(),
        ensures final(self).wf(),final(self).target()==old(self).target(),
            out.is_ok()==effect::operation(instruction.model())(old(self).state()).is_some(),
            out.is_err() ==> out==Err(effect::EffectError::Capacity) || out==Err(effect::EffectError::Rejected),
            out.is_err() ==> final(self).state()==old(self).state(),
            out.is_ok() ==> out->Ok_0.effect_corresponds(&old(self).target(),instruction.model(),branch)
                && out->Ok_0.inverse.state().before==old(self).state() && out->Ok_0.inverse.state().after==final(self).state()
                && out->Ok_0.pending_for(managed),
            final(attempts).appended(old(attempts),&old(self).target()),
            final(attempts).events().last().follows(&cause),
            final(attempts).event().before()==old(self).state(),final(attempts).event().after()==final(self).state(),
            out.is_err() ==> attempt::effect_rejection(final(attempts).event(),instruction.model(),old(self).state(),out->Err_0),
            out.is_ok() ==> final(attempts).records(out->Ok_0.inverse),
    {
        effect::commit_calculation_in(self.target,&mut self.cell,effect::Calculation::Kernel(instruction),
            Ghost(instruction.model()),branch,Ghost(managed),Tracked(cause),Tracked(attempts))
    }
    /// Explicit release is kept inside the owning execution scope. The vstd
    /// write handle alone has no automatic unlock on Drop.
    pub(crate) fn release(self)
        requires self.wf(),
    {self.guard.release_write(self.cell)}
}
}
