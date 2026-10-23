//! A successful managed insertion settles its actual forward obligation.
//! Later shared-Journal activity cannot recreate that write's pending entry.
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, managed::Step};
use vstd::prelude::*;

verus! {
pub proof fn registration_settled_at_cut<T:?Sized>(step:Step<T>,groups:Option<(joint::Journal,nat)>,id:usize,cut:&joint::Snapshot)
    requires step.registered(groups,id),step.insertion().is_some(),groups.is_some(),groups.unwrap().0==step.write().journal(),
        cut.certified(),cut.covers(&step.insertion().unwrap()),
    ensures !cut.pending().contains_key(step.write().at()),
{
    hide(joint::valid);hide(joint::step);reveal(Step::registered);reveal(joint::groups::registration);
    let receipt=step.insertion().unwrap();receipt.transition();cut.valid_history();
    assert(receipt.event().settled==Some(step.write().at()));
    assert(!receipt.event().pending);
    assert(!joint::pending_at(receipt.events(),receipt.events().len()).contains_key(step.write().at()));
    assert(joint::pending_at(cut.events(),receipt.events().len())==joint::pending_at(receipt.events(),receipt.events().len()));
    joint::pending_absent_later(cut.events(),step.write().at(),receipt.events().len(),cut.events().len());
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    pub open spec fn writes_registered_at_cut(&self,cut:&joint::Snapshot)->bool {
        self.result.is_ok() && forall|i:int|0<=i<self.result->Ok_0.steps.len() ==>
            !cut.pending().contains_key((#[trigger] self.result->Ok_0.steps@[i]).write().at())
    }
    pub proof fn registered_pending_at_cut(&self,groups:Option<(joint::Journal,nat)>,id:usize,cut:&joint::Snapshot)
        requires self.result.is_ok(),self.result->Ok_0.registered(groups,id),groups.is_some(),groups.unwrap().0==self.completion().journal(),
            self.completed(),self.effects_before_return(),self.result->Ok_0.witnessed(),
            cut.certified(),cut.covers(&self.completion()),
            forall|i:int|0<=i<self.result->Ok_0.steps.len() ==>
                (#[trigger] self.result->Ok_0.steps@[i]).write().journal()==self.completion().journal(),
        ensures self.writes_registered_at_cut(cut),
    {
        hide(joint::valid);hide(joint::step);reveal(Step::registered);reveal(joint::groups::registration);self.execution_interval();
        assert forall|i:int|0<=i<self.result->Ok_0.steps.len() implies
            !cut.pending().contains_key((#[trigger] self.result->Ok_0.steps@[i]).write().at()) by {
            let step=self.result->Ok_0.steps@[i];assert(step.registered(groups,id));let receipt=step.insertion().unwrap();
            assert(cut.events().take(receipt.events().len() as int) =~= self.completion().events().take(receipt.events().len() as int));
            registration_settled_at_cut(step,groups,id,cut);
        }
    }
}
}
