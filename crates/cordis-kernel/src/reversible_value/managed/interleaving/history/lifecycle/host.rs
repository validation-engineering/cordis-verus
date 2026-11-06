//! Ordinary host mutations retain the same recorded cleanup owner.
//! Read-only Deref is intentional; there is no mutable core escape.
use super::RecordedExecution;
use crate::lifecycle_state::services::NativeValueError;
use crate::reversible_value::{
    self as value,
    managed::{Owner, Slot},
    payload::SharedPayload,
};
use crate::setup_work::{WorkItem, WorkReceipt, WorkTicket};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub type FailureResult<E,A,R,T,M,X> = Result<crate::cleanup_queue::completion::CleanupReport<E,crate::reversible_value::managed::Action<A,R,T,M,X>>,(crate::cleanup_journal::RestoreTicket,E,Option<crate::reversible_value::managed::Action<A,R,T,M,X>>)>;
impl<C,G,A,R,T:?Sized,M,X> std::ops::Deref for RecordedExecution<C,G,A,R,T,M,X> {
    type Target=Owner<C,G,A,R,T,M,X>;
    fn deref(&self)->(out:&Self::Target) ensures *out==self.core(), {&self.core}
}
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    /// Extend only from an actual append-only queue transition. Managed
    /// consumption must go through dispatch and its authentic acknowledgement.
    proof fn appended(tracked &mut self,prior:Self,id:usize)
        requires prior.wf(),old(self).core().wf(),old(self).same_history(&prior),
            old(self).value_sources()==prior.value_sources(),
            old(self).core().execution_journal()==prior.core().execution_journal(),
            old(self).core().cleanup_state().frame(&prior.core().cleanup_state(),id),
            old(self).core().cleanup_state().queues().dom()==prior.core().cleanup_state().queues().dom(),
            old(self).core().cleanup_state().domain_ids()==prior.core().cleanup_state().domain_ids(),
            prior.core().cleanup_state().live(id) ==> {
                let before=prior.core().cleanup_state().queues()[id];let after=old(self).core().cleanup_state().queues()[id];
                &&& after.link()==before.link() && after.protocol().domain_id()==before.protocol().domain_id()
                &&& after.slots().len()>=before.slots().len() && after.slots().take(before.slots().len() as int)==before.slots()
                &&& after.issued()==before.issued() && after.protocol().selected()==before.protocol().selected()
            },
        ensures final(self).wf(),final(self).core()==old(self).core(),final(self).baseline()==prior.baseline(),
            final(self).origins()==prior.origins(),final(self).terminal()==prior.terminal(),
            final(self).value_sources()==prior.value_sources(),final(self).recovery_boundary()==prior.recovery_boundary(),
            final(self).histories().dom()==prior.histories().dom(),final(self).source_order_extends(&prior),
            forall|key:usize|#[trigger] prior.histories().contains_key(key) ==>
                final(self).histories()[key].starts_with(prior.histories()[key].initial())
                && final(self).histories()[key].events()==prior.histories()[key].events(),
    {
        prior.facts();
        if prior.core().cleanup_state().live(id) {
            let tracked mut history=self.histories.borrow_mut().tracked_remove(id);let ghost before=history;
            let queue=self.core().cleanup_state().queues()[id];
            history.extend(queue);
            assert(history.current()==queue.slots());
            history.prefix_transitive(before,self.origins()[id].slots());
            self.histories.borrow_mut().tracked_insert(id,history);
        }
        assert forall|key:usize|#[trigger] self.histories().contains_key(key) implies self.entry(key) by {};
        assert forall|key:usize|#[trigger] prior.histories().contains_key(key) implies
            self.histories()[key].starts_with(prior.histories()[key].initial()) && self.histories()[key].events()==prior.histories()[key].events() by {
            if key!=id || !prior.core().cleanup_state().live(id) {assert(prior.histories()[key].initial().take(prior.histories()[key].initial().len() as int) =~= prior.histories()[key].initial());}
        }
        reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);
    }
    pub fn withdraw_work(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_history(old(self)),final(self).value_sources()==old(self).value_sources(),
            final(self).source_order_extends(old(self)),final(self).core().cleanup_state()==old(self).core().cleanup_state(),
    {
        proof {self.facts();}self.core.withdraw();
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}
    }
    pub fn activate_external(&mut self)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_history(old(self)),final(self).value_sources()==old(self).value_sources(),
            final(self).source_order_extends(old(self)),final(self).core().cleanup_state()==old(self).core().cleanup_state(),
    {
        proof {self.facts();}let out=self.core.activate_external();
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}out
    }
    pub fn provide(&mut self,port:crate::Port,value:Arc<Slot<T,M>>)->(out:Result<(),(NativeValueError,Arc<Slot<T,M>>)>)
        requires old(self).wf(),
        ensures final(self).core().value_state().is_some()==old(self).core().value_state().is_some(),
            final(self).core().value_state().is_some() ==> old(self).core().value_state().unwrap().owned().submap_of(final(self).core().value_state().unwrap().owned()),
            out.is_ok() ==> final(self).core().value_state().is_some()
                && final(self).core().value_state().unwrap().owned().contains_pair((port.key,port.realm),value),
            final(self).wf(),final(self).same_history(old(self)),final(self).value_sources()==old(self).value_sources(),
            final(self).source_order_extends(old(self)),final(self).core().cleanup_state()==old(self).core().cleanup_state(),
    {
        proof {self.facts();}let out=self.core.provide(port,value);
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}out
    }
    pub fn issue_root<B>(&mut self,argument:B)->(out:Result<WorkItem<B>,B>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_history(old(self)),final(self).value_sources()==old(self).value_sources(),
            final(self).source_order_extends(old(self)),final(self).core().cleanup_state()==old(self).core().cleanup_state(),
    {
        proof {self.facts();}let out=self.core.issue_root(argument);
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}out
    }
    pub fn start_root(&mut self,ticket:WorkTicket)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_history(old(self)),final(self).value_sources()==old(self).value_sources(),
            final(self).source_order_extends(old(self)),final(self).core().cleanup_state()==old(self).core().cleanup_state(),
    {
        proof {self.facts();}let out=self.core.start_root(ticket);
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}out
    }
    pub fn cancel_queued_root(&mut self,ticket:WorkTicket)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_history(old(self)),final(self).value_sources()==old(self).value_sources(),
            final(self).source_order_extends(old(self)),final(self).core().cleanup_state()==old(self).core().cleanup_state(),
    {
        proof {self.facts();}let out=self.core.cancel_queued_root(ticket);
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}out
    }
    pub fn complete_root<E>(&mut self,receipt:WorkReceipt<Result<(),E>>)->(out:Result<Result<(),E>,WorkReceipt<Result<(),E>>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_history(old(self)),final(self).value_sources()==old(self).value_sources(),
            final(self).source_order_extends(old(self)),final(self).core().cleanup_state()==old(self).core().cleanup_state(),
    {
        proof {self.facts();}let out=self.core.complete_root(receipt);
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}out
    }
    pub fn fail_root<E>(&mut self,ticket:WorkTicket,error:E)->(out:Result<E,E>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_history(old(self)),final(self).value_sources()==old(self).value_sources(),
            final(self).source_order_extends(old(self)),final(self).core().cleanup_state()==old(self).core().cleanup_state(),
    {
        proof {self.facts();}let out=self.core.fail_root(ticket,error);
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}out
    }
    pub fn abandon_root(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_history(old(self)),final(self).value_sources()==old(self).value_sources(),
            final(self).source_order_extends(old(self)),final(self).core().cleanup_state()==old(self).core().cleanup_state(),
    {
        proof {self.facts();}self.core.abandon_root();
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}
    }
    pub fn apply_value(&mut self,id:usize,value:&value::ReversibleValue,operation:value::Operation,branch:value::Branch)->(out:Result<crate::execution::ValueAdmission,value::ValueError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).terminal()==old(self).terminal(),final(self).value_sources()==old(self).value_sources(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==>
                final(self).histories()[group].starts_with(old(self).histories()[group].initial())
                && final(self).histories()[group].events()==old(self).histories()[group].events(),
    {
        proof {self.facts();}let ghost prior=*self;
        let out=self.core.apply_value(id,value,operation,branch);
        proof {self.appended(prior,id);}out
    }
    pub fn apply_prepared_effect(&mut self,id:usize,prepared:value::effect::Prepared,branch:value::Branch)->(out:Result<crate::execution::ValueAdmission,value::effect::EffectError>)
        requires old(self).wf(),prepared.wf(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).terminal()==old(self).terminal(),final(self).value_sources()==old(self).value_sources(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==>
                final(self).histories()[group].starts_with(old(self).histories()[group].initial())
                && final(self).histories()[group].events()==old(self).histories()[group].events(),
    {
        proof {self.facts();}let ghost prior=*self;
        let out=self.core.apply_prepared_effect(id,prepared,branch);
        proof {self.appended(prior,id);}out
    }
    pub fn apply_native_value(&mut self,id:usize,port:crate::Port,operation:value::Operation,branch:value::Branch)->(out:Result<value::access::Write,value::access::Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).terminal()==old(self).terminal(),final(self).value_sources()==old(self).value_sources(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==>
                final(self).histories()[group].starts_with(old(self).histories()[group].initial())
                && final(self).histories()[group].events()==old(self).histories()[group].events(),
    {
        proof {self.facts();}let ghost prior=*self;
        let out=self.core.apply_native_value(id,port,operation,branch);
        proof {self.appended(prior,id);}out
    }
    pub fn apply_native_effect(&mut self,id:usize,computation:value::native_effect::Computation<SharedPayload<T>,M>,branch:value::Branch)->(out:Result<value::access::Write,value::effect::EffectError>)
        requires old(self).wf(),computation.wf(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).terminal()==old(self).terminal(),final(self).value_sources()==old(self).value_sources(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==>
                final(self).histories()[group].starts_with(old(self).histories()[group].initial())
                && final(self).histories()[group].events()==old(self).histories()[group].events(),
    {
        proof {self.facts();}let ghost prior=*self;
        let out=self.core.apply_native_effect(id,computation,branch);
        proof {self.appended(prior,id);}out
    }
    pub fn apply_native_payload(&mut self,id:usize,port:crate::Port,value:Arc<T>)->(out:Result<crate::cleanup_groups::payload::Admission<T>,(crate::cleanup_groups::payload::AccessError,Arc<T>)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).terminal()==old(self).terminal(),final(self).value_sources()==old(self).value_sources(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==>
                final(self).histories()[group].starts_with(old(self).histories()[group].initial())
                && final(self).histories()[group].events()==old(self).histories()[group].events(),
    {
        proof {self.facts();}let ghost prior=*self;
        let out=self.core.apply_native_payload(id,port,value);
        proof {self.appended(prior,id);}out
    }
    pub fn advance_value_program(&mut self,id:usize,cursor:&mut value::cursor::Cursor)->(out:Result<Option<value::Outcome>,value::ValueError>)
        requires old(self).wf(),old(cursor).wf(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).terminal()==old(self).terminal(),final(self).value_sources()==old(self).value_sources(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==>
                final(self).histories()[group].starts_with(old(self).histories()[group].initial())
                && final(self).histories()[group].events()==old(self).histories()[group].events(),
    {
        proof {self.facts();}let ghost prior=*self;
        let out=self.core.advance_value_program(id,cursor);
        proof {self.appended(prior,id);}out
    }
    #[verifier::spinoff_prover]
    pub fn run_value_program(&mut self,id:usize,value:&value::ReversibleValue,program:&value::program::Program)->(out:Result<value::program::ProgramReport,value::ValueError>)
        requires old(self).wf(),program.valid(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).terminal()==old(self).terminal(),final(self).value_sources()==old(self).value_sources(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==>
                final(self).histories()[group].starts_with(old(self).histories()[group].initial())
                && final(self).histories()[group].events()==old(self).histories()[group].events(),
    {
        proof {self.facts();}let ghost prior=*self;
        let out=self.core.run_value_program(id,value,program);
        proof {self.appended(prior,id);}out
    }
    #[verifier::spinoff_prover]
    pub fn run_native_value_program(&mut self,id:usize,port:crate::Port,program:&value::program::Program)->(out:Result<value::function::Report,value::function::Error>)
        requires old(self).wf(),program.valid(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).terminal()==old(self).terminal(),final(self).value_sources()==old(self).value_sources(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==>
                final(self).histories()[group].starts_with(old(self).histories()[group].initial())
                && final(self).histories()[group].events()==old(self).histories()[group].events(),
    {
        proof {self.facts();}let ghost prior=*self;
        let out=self.core.run_native_value_program(id,port,program);
        proof {self.appended(prior,id);}out
    }
    #[verifier::spinoff_prover]
    pub fn run_service_program(&mut self,id:usize,program:&value::services::Program)->(out:Result<value::services::Report,value::services::AdmissionError>)
        requires old(self).wf(),program.valid(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).terminal()==old(self).terminal(),final(self).value_sources()==old(self).value_sources(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==>
                final(self).histories()[group].starts_with(old(self).histories()[group].initial())
                && final(self).histories()[group].events()==old(self).histories()[group].events(),
    {
        proof {self.facts();}let ghost prior=*self;
        let out=self.core.run_service_program(id,program);
        proof {self.appended(prior,id);}out
    }
    pub fn complete_failure<E>(&mut self,id:usize,ticket:crate::cleanup_journal::RestoreTicket,error:E,retry:Option<super::callbacks::HostAction<A,R,X>>,policy:crate::cleanup_queue::completion::CleanupPolicy)->(out:FailureResult<E,A,R,T,M,X>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).source_order_extends(old(self)),
    {
        match self.complete_result(id,ticket,Err(error),retry,policy) {
            Ok(report)=>Ok(report),
            Err((ticket,result,retry))=>Err((ticket,result.unwrap_err(),retry)),
        }
    }
    pub fn seal_external(&mut self)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).histories()==old(self).histories(),
            final(self).source_order_extends(old(self)),
            out ==> final(self).terminal().dom()==final(self).histories().dom(),
    {
        proof {self.facts();}let ghost queues=self.core().cleanup_state().queues();
        let out=self.core.seal_external();
        proof {if out {self.terminal=Ghost(self.terminal@.union_prefer_right(queues));}
            reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}
        out
    }
    pub fn retire_observed_effect(&mut self,run:crate::effect_work::EffectRun<G>)->(out:Result<(G,crate::host_status::Observation),crate::effect_work::EffectRun<G>>)
        requires old(self).wf(),run.wf(),
        ensures final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).histories()==old(self).histories(),final(self).source_order_extends(old(self)),
            out.is_ok() ==> out->Ok_0.1.wf() && out->Ok_0.1.retirement_recorded(),
    {
        proof {self.facts();}let ghost id=run.identity().group_id();let ghost queue=self.core().cleanup_state().queues()[id];
        let out=self.core.retire_observed_effect(run);
        proof {if out.is_ok() {self.terminal=Ghost(self.terminal@.insert(id,queue));}
            reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}
        out
    }

    pub fn admit_root<P,H,B>(&mut self,runtime:&crate::lifecycle_state::native::runtime::NativeRuntime<P,H,Slot<T,M>>,id:usize,argument:B)->(out:Result<crate::lifecycle_state::registration::RegisteredInvocation<B>,B>)
        requires old(self).wf(),runtime.wf(),
        ensures final(self).wf(),final(self).same_history(old(self)),final(self).source_order_extends(old(self)),
            out.is_ok() ==> out->Ok_0.work().value()==argument && out->Ok_0.owner()==id
                && out->Ok_0.bound_to(runtime.control_address()),
    {
        proof {self.facts();}let out=runtime.admit_managed_root(id,&mut self.core,argument);
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}out
    }

    #[verifier::spinoff_prover]
    pub fn run_value_root<P,H,F>(&mut self,runtime:&mut crate::lifecycle_state::native::runtime::NativeRuntime<value::function::Body<P,F>,H,Slot<T,M>>,id:usize)
        ->(out:Result<value::function::RegisteredReport,value::function::AdmissionError>)
        requires old(self).wf(),old(runtime).wf(),
        ensures final(self).wf(),final(runtime).wf(),final(self).baseline()==old(self).baseline(),final(self).source_order_extends(old(self)),
    {
        proof {self.facts();}let ghost prior=*self;let out=runtime.run_value_root(id,&mut self.core);
        proof {self.appended(prior,0);}out
    }

    #[verifier::spinoff_prover]
    pub fn run_service_root<P,H,F>(&mut self,runtime:&mut crate::lifecycle_state::native::runtime::NativeRuntime<value::function::Body<P,F>,H,Slot<T,M>>,id:usize)
        ->(out:Result<value::service_function::RegisteredReport,value::service_function::AdmissionError>)
        requires old(self).wf(),old(runtime).wf(),
        ensures final(self).wf(),final(runtime).wf(),final(self).baseline()==old(self).baseline(),final(self).source_order_extends(old(self)),
    {
        proof {self.facts();}let ghost prior=*self;let out=runtime.run_service_root(id,&mut self.core);
        proof {self.appended(prior,0);}out
    }

    pub fn effect_status<E>(&mut self,id:usize)->(out:Option<crate::host_status::HostStatus<E>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_history(old(self)),final(self).source_order_extends(old(self)),
            out.is_some() ==> out.unwrap().wf() && out.unwrap().owned_by(&final(self).core(),id) && out.unwrap().bound(&final(self).core()),
    {
        proof {self.facts();}let out=self.core.effect_status(id);
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}out
    }

    pub open spec fn terminal_restores(&self)->bool {
        forall|id:usize,token:int|self.terminal().contains_key(id) && self.histories().contains_key(id)
            && 0<=token<self.histories()[id].initial().len()
            && (#[trigger] self.histories()[id].initial()[token]).is_some()
            && crate::cleanup_groups::payload::recovery::managed(self.histories()[id].initial()[token].unwrap()) ==>
                exists|at:int|super::super::consumed(self.histories()[id].events(),self.histories()[id].receipts(),self.histories()[id].link(),token,self.histories()[id].initial()[token].unwrap(),at)
    }
    /// Every managed inverse in a terminal queue has its own actual successful
    /// dispatch and (for a Journal-bound queue) matching acknowledgement.
    pub proof fn terminal_history(&self)
        requires self.wf(),ensures self.terminal_restores(),
    {
        self.facts();
        assert forall|id:usize,token:int|self.terminal().contains_key(id) && self.histories().contains_key(id)
            && 0<=token<self.histories()[id].initial().len()
            && (#[trigger] self.histories()[id].initial()[token]).is_some()
            && crate::cleanup_groups::payload::recovery::managed(self.histories()[id].initial()[token].unwrap()) implies
                exists|at:int|super::super::consumed(self.histories()[id].events(),self.histories()[id].receipts(),self.histories()[id].link(),token,self.histories()[id].initial()[token].unwrap(),at) by {
            assert(!self.core().cleanup_state().live(id));
            let queue=self.terminal()[id];queue.empty_payloads();
            let h=self.histories()[id];reveal(super::History::wf);
            assert(h.accounted(token));assert(h.current()[token].is_none());
        }
    }

}
}
