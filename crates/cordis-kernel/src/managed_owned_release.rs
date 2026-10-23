//! Recovery consumes the history and actual terminal queue retained by the
//! executable lifecycle owner, including a queue removed before final Unload.
#[path = "managed_recovery_cut.rs"]
pub mod cut;
#[cfg(verus_keep_ghost)]
use super::RecordedExecution;
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::{
    lifecycle_state::native::runtime::episode::Unload,
    reversible_value::managed::{self, interleaving as trajectory},
};
use vstd::prelude::*;

verus! {
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    /// Neither a separately carried collector nor a caller-created drained
    /// snapshot is an input. Interference/quiet-tail hypotheses remain explicit.
    pub proof fn unload_recovers_from_owner<C,G,A,R,M,X>(&self,tracked owner:&RecordedExecution<C,G,A,R,T,M,X>,id:usize,offset:nat,tracked end:&Unload)
        requires owner.wf(),owner.baseline().cleanup_state().live(id),owner.histories().contains_key(id),owner.terminal().contains_key(id),
            self.start().owner().owns(&owner.baseline()),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner.baseline(),id,offset),managed::retained(self.result->Ok_0.steps@,owner.baseline(),id,offset),
            trajectory::linked(owner.histories()[id].events(),self.completion(),self.return_values(),self.obligations(owner.baseline(),id,offset)),
            self.unload_source(owner.histories()[id].events(),end),
            self.result->Ok_0.registered(owner.baseline().cleanup_state().link(),id),end.cleanup_link()==owner.baseline().cleanup_state().link(),
            self.result->Ok_0.queued_sources(owner.baseline().cleanup_state().queues()[id].link()),
            end.cleanup_checkpoint().is_some(),end.cleanup_checkpoint().unwrap().journal()==end.checkpoint().journal(),
            trajectory::completion::foreign_settled(owner.histories()[id].events(),self.return_values().dom()),
        ensures self.unload_values(owner.histories()[id].events(),end)==self.begin_values(),
            self.start().recorded(end.checkpoint().events()),end.recorded(end.checkpoint().events()),self.start().at()<end.at(),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        hide(trajectory::linked);hide(trajectory::completion::foreign_settled);hide(RegisteredReport::unload_source);
        owner.facts();let tracked history=owner.history(id);
        assert(history.starts_with(owner.baseline().cleanup_state().queues()[id].slots()));
        self.unload_recovers_from_history(owner.baseline(),id,offset,history,owner.terminal()[id],end);
    }
}
}
