//! Recovery between this registered invocation's authentic Begin and return.
//! Source conditions concern real Journal frames, never a desired result heap.
use super::RegisteredReport;
use crate::reversible_value::effect::ScalarEffect;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    joint,
    managed::{
        episode::{self, endpoint},
        recovery::word,
        semantics::{self as s, Value},
        trace, Owner, Report,
    },
    service_composition::Address,
};
use vstd::prelude::*;

verus! {
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    /// This sufficient condition is checked in the authentic trace. Other
    /// Journals keep their own cuts; interfering writes are not silently erased.
    pub open spec fn endpoint_source(&self)->bool {
        self.result.is_ok() && {
            let steps=self.result->Ok_0.steps@;let end=self.completion();
            &&& forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).write().journal()==end.journal()
            &&& word::admissible(steps)
            &&& endpoint::quiet_start(steps,end.events(),self.start().at()+1)
            &&& endpoint::quiet_end(steps,end.events())
        }
    }
    /// Values are decoded at the actual native Begin in its retained prefix.
    pub open spec fn begin_values(&self)->Map<Address,Value<T>> {
        endpoint::observe(self.result->Ok_0.steps@,self.start().checkpoint().events(),
            self.start().at()+1,self.start().checkpoint().journal(),false)
    }
    pub open spec fn return_values(&self)->Map<Address,Value<T>> {
        let end=self.completion();
        endpoint::observe(self.result->Ok_0.steps@,end.events(),end.events().len(),end.journal(),true)
    }
    pub proof fn source_bounds(&self)
        requires self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
        ensures endpoint::bounded(self.result->Ok_0.steps@,self.completion()),
            forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> self.start().at()<(#[trigger] self.result->Ok_0.steps@[i]).write().at(),
            self.begin_values()==endpoint::observe(self.result->Ok_0.steps@,self.completion().events(),
                self.start().at()+1,self.completion().journal(),false),
    {
        hide(joint::valid);hide(joint::step);
        self.execution_interval();self.start().facts();
        reveal(Report::recovery_history);reveal(Report::after);reveal(episode::writes_after);
        let steps=self.result->Ok_0.steps@;let end=self.completion();let start=self.start();
        assert forall|i:int|0<=i<steps.len() implies start.at()<(#[trigger] steps[i]).write().at() by {
            assert(steps[i].write().follows(&start.checkpoint()));
        }
        assert(joint::state_at(start.checkpoint().events(),start.at()+1)==joint::state_at(end.events(),start.at()+1));
        assert(self.begin_values() =~= endpoint::observe(steps,end.events(),start.at()+1,end.journal(),false));
    }
    #[verifier::opaque]
    pub open spec fn endpoint_recovery(&self)->bool {
        self.endpoint_source() ==> {
            &&& s::replay(self.result->Ok_0.steps@,self.begin_values())==Some(self.return_values())
            &&& s::undo(self.result->Ok_0.steps@,self.return_values())==Some(self.begin_values())
        }
    }
    /// Called by the real dispatcher for successful and failed-prefix returns.
    pub proof fn establish_endpoint_recovery(&self)
        requires self.completed(),self.effects_before_return(),self.episode_interval(),
            self.result.is_ok() ==> self.result->Ok_0.witnessed() && self.result->Ok_0.recovery_history(),
        ensures self.endpoint_recovery(),
    {
        reveal(RegisteredReport::endpoint_recovery);
        if self.endpoint_source() {
            self.source_bounds();
            self.result->Ok_0.recover_observed(self.completion(),self.start().at()+1);
        }
    }
    #[verifier::opaque]
    pub open spec fn retained_recovery<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat)->bool {
        self.endpoint_source() ==> trace::queued_undo(
            owner.cleanup_state().queues()[id].slots().subrange(offset as int,owner.cleanup_state().queues()[id].slots().len() as int),
            self.return_values())==Some(self.begin_values())
    }
    /// The inverse is exactly the retained mixed suffix in the actual owner.
    pub proof fn establish_retained_recovery<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat)
        requires self.endpoint_recovery(),self.result.is_ok() ==> self.result->Ok_0.queue_semantics(owner,id,offset),
        ensures self.retained_recovery(owner,id,offset),
    {reveal(RegisteredReport::endpoint_recovery);reveal(RegisteredReport::retained_recovery);}
    pub proof fn recover_begin<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat)
        requires self.endpoint_source(),self.retained_recovery(owner,id,offset),
        ensures trace::queued_undo(
            owner.cleanup_state().queues()[id].slots().subrange(offset as int,owner.cleanup_state().queues()[id].slots().len() as int),
            self.return_values())==Some(self.begin_values()),
    {reveal(RegisteredReport::retained_recovery);}
}
}
