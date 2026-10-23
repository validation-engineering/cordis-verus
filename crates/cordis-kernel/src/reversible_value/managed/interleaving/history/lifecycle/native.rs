//! The recorded owner delegates native Finish, withdrawal and Unload to the
//! existing production runtime; terminal evidence comes from that same call.
use super::RecordedExecution;
use crate::lifecycle_state::native::runtime::{NativeRuntime, ReleaseObservation};
use crate::reversible_value::{
    effect::ScalarEffect,
    function::Body,
    managed::{
        root::{AdmissionError, RegisteredReport},
        Action, Function, Owner, Slot,
    },
};
use crate::Error;
use vstd::prelude::*;

verus! {
pub type ReleaseOutcome<A,R,T,M,X> = ReleaseObservation<Slot<T,M>,Action<A,R,T,M,X>>;
pub type RootOutcome<C,G,A,R,T,M,X,E> = (RecordedExecution<C,G,A,R,T,M,X>,Result<RegisteredReport<E,T>,AdmissionError>);
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    pub fn finish<P,H>(&mut self,runtime:&mut NativeRuntime<P,H,Slot<T,M>>,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),old(runtime).wf(),
        ensures final(self).core().value_state()==old(self).core().value_state(),
            old(runtime).publications().entries().submap_of(final(runtime).publications().entries()),
            final(runtime).journal_spec()==old(runtime).journal_spec(),final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(runtime).wf(),final(self).baseline()==old(self).baseline(),
            final(self).histories()==old(self).histories(),final(self).terminal()==old(self).terminal(),
            final(self).core().cleanup_state()==old(self).core().cleanup_state(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> final(runtime).publications().entries().contains_key(id) && old(runtime).owns_execution(id,&old(self).core())
                && final(runtime).publications().entries()[id].values()==final(self).core().value_state().unwrap().owned()
                && final(runtime).publications().entries()[id].origin()==final(self).core().origin().unwrap(),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}
        let out=runtime.finish_managed_execution(id,&mut self.core);
        proof {reveal(RecordedExecution::wf);}
        out
    }
    pub fn withdraw<P,H>(&mut self,runtime:&mut NativeRuntime<P,H,Slot<T,M>>,id:usize,retiring:bool)->(out:Result<(),Error>)
        requires old(self).wf(),old(runtime).wf(),
        ensures final(runtime).publications()==old(runtime).publications(),final(runtime).journal_spec()==old(runtime).journal_spec(),
            final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(runtime).wf(),final(self).baseline()==old(self).baseline(),
            final(self).histories()==old(self).histories(),final(self).terminal()==old(self).terminal(),
            final(self).core().cleanup_state()==old(self).core().cleanup_state(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> old(runtime).owns_execution(id,&old(self).core()) && !final(self).core().work_state().accepts(),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}
        let out=runtime.withdraw_managed_execution(id,&mut self.core,retiring);
        proof {reveal(RecordedExecution::wf);}
        out
    }
    /// Retry the actual failed native cleanup action and all failed local queues
    /// together. Both the lifecycle action and each retrying token get new tickets.
    pub fn retry_native<P,H>(&mut self,runtime:&mut NativeRuntime<P,H,Slot<T,M>>,id:usize)->(out:Result<crate::action_ledger::ActionTicket,Error>)
        requires old(self).wf(),old(runtime).wf(),
        ensures final(runtime).publications()==old(runtime).publications(),final(runtime).journal_spec()==old(runtime).journal_spec(),
            final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(runtime).wf(),final(self).baseline()==old(self).baseline(),
            final(self).histories()==old(self).histories(),final(self).terminal()==old(self).terminal(),
            final(self).core().cleanup_state().same_slots(&old(self).core().cleanup_state()),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> final(self).core().cleanup_state().retried_failed(&old(self).core().cleanup_state())
                && !final(self).core().cleanup_state().any_failed()
                && out->Ok_0.id==id && out->Ok_0.generation==old(self).core().origin().unwrap().generation
                && out->Ok_0.action==old(runtime).state().protocol().next_id()
                && final(runtime).state().protocol().cleanup_reply_enabled(out->Ok_0),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}
        let out=runtime.retry_managed_execution(id,&mut self.core);
        proof {reveal(RecordedExecution::wf);}
        out
    }
    pub fn release<P,H>(&mut self,runtime:&mut NativeRuntime<P,H,Slot<T,M>>,id:usize)->(out:ReleaseOutcome<A,R,T,M,X>)
        requires old(self).wf(),old(runtime).wf(),
        ensures out.0.is_err() ==> final(runtime).publications()==old(runtime).publications(),
            out.0.is_ok() ==> final(runtime).publications().entries()==old(runtime).publications().entries().remove(id),
            final(runtime).child_records().extends(&old(runtime).child_records()),
            final(runtime).journal_spec()==old(runtime).journal_spec(),final(runtime).joint_key()==old(runtime).joint_key(),
            out.0.is_ok() ==> final(runtime).child_records().unloads().len()==old(runtime).child_records().unloads().len()+1
                && final(runtime).child_records().unloads().last().same_source(&out.1@.unwrap()),
            final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(runtime).wf(),final(self).baseline()==old(self).baseline(),
            final(self).histories()==old(self).histories(),
            out.0.is_err() ==> *final(self)==*old(self) && out.1@.is_none() && out.2@.is_none(),
            out.0.is_ok() ==> crate::lifecycle_state::native::runtime::released(out)
                && out.1@.unwrap().cleanup_link()==final(self).baseline().cleanup_state().link()
                && out.2@==Some(old(self).core().cleanup_state())
                && final(self).core().cleanup_state().queues()==Map::empty()
                && final(self).terminal()==old(self).terminal().union_prefer_right(old(self).core().cleanup_state().queues())
                && final(self).terminal().dom()==final(self).histories().dom(),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}
        let out=runtime.release_managed_execution_observed(id,&mut self.core);
        proof {
            if out.0.is_ok() {self.terminal=Ghost(self.terminal@.union_prefer_right(out.2@.unwrap().queues()));}
            reveal(RecordedExecution::wf);
        }
        out
    }
    pub fn retry_controlled<P,H,E>(&mut self,runtime:&mut NativeRuntime<P,H,Slot<T,M>>,id:usize,control:&mut crate::poll_control::PollControl<E>)
        ->(out:Result<(crate::action_ledger::ActionTicket,Option<E>),Error>)
        requires old(self).wf(),old(runtime).wf(),old(control).wf(),old(control).bound(old(runtime)),
        ensures final(self).wf(),final(runtime).wf(),final(control).wf(),final(control).bound(final(runtime)),
            final(self).same_history(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).source_order_extends(old(self)),
            out.is_ok() ==> final(control).cleanup_error().is_none() && out->Ok_0.1==old(control).cleanup_error()
                && final(runtime).state().protocol().cleanup_reply_enabled(out->Ok_0.0),
    {
        proof {self.facts();}let out=runtime.retry_controlled_execution(id,&mut self.core,control);
        proof {reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);}out
    }
    pub fn release_controlled<P,H,E>(&mut self,runtime:&mut NativeRuntime<P,H,Slot<T,M>>,id:usize,control:&mut crate::poll_control::PollControl<E>)
        ->(out:ReleaseOutcome<A,R,T,M,X>)
        requires old(self).wf(),old(runtime).wf(),old(control).wf(),old(control).bound(old(runtime)),
        ensures final(self).wf(),final(runtime).wf(),final(control).wf(),final(control).bound(final(runtime)),
            final(self).baseline()==old(self).baseline(),final(self).histories()==old(self).histories(),final(self).source_order_extends(old(self)),
            out.0.is_err() ==> *final(self)==*old(self) && out.1@.is_none() && out.2@.is_none(),
            out.0.is_ok() ==> final(self).terminal_restores() && crate::lifecycle_state::native::runtime::released(out)
                && final(self).terminal().dom()==final(self).histories().dom()
                && final(control).state().episode.is_none() && !final(control).state().restart
                && out.2@==Some(old(self).core().cleanup_state())
                && final(self).terminal()==old(self).terminal().union_prefer_right(old(self).core().cleanup_state().queues()),
    {
        proof {self.facts();}let out=runtime.release_controlled_execution_observed(id,&mut self.core,control);
        proof {if out.0.is_ok() {self.terminal=Ghost(self.terminal@.union_prefer_right(out.2@.unwrap().queues()));
                assert(self.terminal().dom()==self.histories().dom());}
            reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);self.terminal_history();}out
    }

}
impl<P,H,E:ScalarEffect+Copy,T:?Sized,M> NativeRuntime<Body<P,Function<E,T>>,H,Slot<T,M>> {
    /// Run the stored root/Child recipe and immediately take ownership of its
    /// actual retained queues. Callers cannot replace the return-time baseline.
    pub fn run_recorded_root<C,G,A,R,X>(&mut self,id:usize,execution:Owner<C,G,A,R,T,M,X>)->(out:RootOutcome<C,G,A,R,T,M,X,E>)
        requires old(self).wf(),execution.wf(),
        ensures out.1.is_ok() ==> out.1->Ok_0.completion().event().key==final(self).recipe_key()
                && out.1->Ok_0.completion().event().after is Recipes
                && out.1->Ok_0.completion().event().after->Recipes_state.revision==final(self).recipe_history().events.len(),
            out.1.is_ok() ==> out.1->Ok_0.completion().event().after->Recipes_state.entries==crate::lifecycle_state::native::runtime::recipes::project(crate::lifecycle_state::native::runtime::recipes::entries(final(self).registry().entries())),
            old(self).managed_invocation_ready(id,&execution) ==> out.1.is_ok(),
            final(self).wf(),out.0.wf(),out.0.baseline()==out.0.core(),
            final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
            final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.0.core().execution_journal()==execution.execution_journal(),out.0.baseline().value_state()==execution.value_state(),
            out.1.is_ok() && execution.execution_journal()==Some(old(self).journal_spec()) ==>
                out.0.recovery_boundary().is_some() && out.0.recovery_boundary().unwrap().same(&out.1->Ok_0.completion())
                && (forall|group:usize|#[trigger] out.0.histories().contains_key(group) ==> out.0.source_order(group,out.1->Ok_0.completion()))
                && (out.1->Ok_0.result.is_ok() ==> out.1->Ok_0.result->Ok_0.covered_by(out.0.recovery_boundary().unwrap())),
            out.1.is_ok() ==> {
                let report=out.1->Ok_0;let owner=out.0.baseline();
                &&& report.completed() && report.episode_interval() && report.effects_before_return()
                &&& report.completion().journal()==old(self).journal_spec()
                &&& report.endpoint_recovery() && report.retained_recovery(owner,0,execution.cleanup_state().queues()[0].slots().len())
                &&& old(self).owns_execution(id,&owner) && report.start().owner().owns(&owner)
                &&& old(self).registry().entries().contains_key(id) && old(self).registry().entries()[id].recipe().payload() is Managed
                &&& report.function@==old(self).registry().entries()[id].recipe().payload()->Managed_0
                &&& report.function@.valid() && report.function@.bound(report.ports@,old(self).registry().entries()[id].recipe())
                &&& report.revision==old(self).registry().entries()[id].recipe().version()
                &&& report.origin.id==id && report.origin.domain==old(self).state().protocol().domain_id()
                &&& report.work.domain_id()==owner.work_state().domain_id() && report.work.domain_id()==execution.work_state().domain_id()
                &&& report.result.is_ok() ==> owner.value_state().is_some()
                    && report.result->Ok_0.certified(report.function@.code(),report.ports@,owner.value_state().unwrap())
                    && report.result->Ok_0.interpreted(report.function@.code())
                &&& report.result.is_ok() ==> report.result->Ok_0.recovery_history() && report.result->Ok_0.witnessed()
                    && report.result->Ok_0.queued_sources(owner.cleanup_state().queues()[0].link())
                    && report.result->Ok_0.registered(owner.cleanup_state().link(),0)
                    && (forall|i:int|0<=i<report.result->Ok_0.steps.len() ==> (#[trigger] report.result->Ok_0.steps@[i]).carrier().covered(out.0.value_sources()))
                    && crate::reversible_value::managed::retained(report.result->Ok_0.steps@,owner,0,execution.cleanup_state().queues()[0].slots().len())
            },
    {let mut mode=None;self.run_recorded_root_with(id,execution,&mut mode,Ghost(None))}

    pub(crate) fn run_recorded_root_with<C,G,A,R,X>(&mut self,id:usize,execution:Owner<C,G,A,R,T,M,X>,mode:&mut Option<crate::reversible_value::managed::protected::Context<'_>>,Ghost(expected):Ghost<Option<Seq<crate::reversible_value::managed::Step<T>>>>)->(out:RootOutcome<C,G,A,R,T,M,X,E>)
        requires expected.is_some() ==> old(mode).is_some()
                && crate::reversible_value::managed::protected::plan(old(self).registry().entries()[id].recipe().payload()->Managed_0.code(),expected.unwrap())
                && crate::reversible_value::managed::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap()),
            old(mode).is_some() ==> old(self).protection_ready(id,&execution,&old(mode)->Some_0),
            old(self).wf(),execution.wf(),
        ensures expected.is_some() && out.1.is_ok() && out.1->Ok_0.result.is_ok() ==>
                out.1->Ok_0.result->Ok_0.failure.is_none() && crate::reversible_value::managed::protected::same(out.1->Ok_0.result->Ok_0.steps@,expected.unwrap()),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.shape(&old(mode)->Some_0)
                && (out.1.is_err() || out.1->Ok_0.result.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states())
                && (out.1.is_ok() && out.1->Ok_0.result.is_ok() ==> crate::reversible_value::managed::protected::addressed(old(mode)->Some_0.targets(),old(mode)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && crate::reversible_value::managed::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && final(mode)->Some_0.states()==crate::reversible_value::managed::protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)),
            out.1.is_ok() ==> out.1->Ok_0.completion().event().key==final(self).recipe_key()
                && out.1->Ok_0.completion().event().after is Recipes
                && out.1->Ok_0.completion().event().after->Recipes_state.revision==final(self).recipe_history().events.len(),
            out.1.is_ok() ==> out.1->Ok_0.completion().event().after->Recipes_state.entries==crate::lifecycle_state::native::runtime::recipes::project(crate::lifecycle_state::native::runtime::recipes::entries(final(self).registry().entries())),
            old(self).managed_invocation_ready(id,&execution) ==> out.1.is_ok(),
            final(self).wf(),out.0.wf(),out.0.baseline()==out.0.core(),
            final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
            final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.0.core().execution_journal()==execution.execution_journal(),out.0.baseline().value_state()==execution.value_state(),
            out.1.is_ok() && execution.execution_journal()==Some(old(self).journal_spec()) ==>
                out.0.recovery_boundary().is_some() && out.0.recovery_boundary().unwrap().same(&out.1->Ok_0.completion())
                && (forall|group:usize|#[trigger] out.0.histories().contains_key(group) ==> out.0.source_order(group,out.1->Ok_0.completion()))
                && (out.1->Ok_0.result.is_ok() ==> out.1->Ok_0.result->Ok_0.covered_by(out.0.recovery_boundary().unwrap())),
            out.1.is_ok() ==> {
                let report=out.1->Ok_0;let owner=out.0.baseline();
                &&& report.completed() && report.episode_interval() && report.effects_before_return()
                &&& report.completion().journal()==old(self).journal_spec()
                &&& report.endpoint_recovery() && report.retained_recovery(owner,0,execution.cleanup_state().queues()[0].slots().len())
                &&& old(self).owns_execution(id,&owner) && report.start().owner().owns(&owner)
                &&& old(self).registry().entries().contains_key(id) && old(self).registry().entries()[id].recipe().payload() is Managed
                &&& report.function@==old(self).registry().entries()[id].recipe().payload()->Managed_0
                &&& report.function@.valid() && report.function@.bound(report.ports@,old(self).registry().entries()[id].recipe())
                &&& report.revision==old(self).registry().entries()[id].recipe().version()
                &&& report.origin.id==id && report.origin.domain==old(self).state().protocol().domain_id()
                &&& report.work.domain_id()==owner.work_state().domain_id() && report.work.domain_id()==execution.work_state().domain_id()
                &&& report.result.is_ok() ==> owner.value_state().is_some()
                    && report.result->Ok_0.certified(report.function@.code(),report.ports@,owner.value_state().unwrap())
                    && report.result->Ok_0.interpreted(report.function@.code())
                &&& report.result.is_ok() ==> report.result->Ok_0.recovery_history() && report.result->Ok_0.witnessed()
                    && report.result->Ok_0.queued_sources(owner.cleanup_state().queues()[0].link())
                    && report.result->Ok_0.registered(owner.cleanup_state().link(),0)
                    && (forall|i:int|0<=i<report.result->Ok_0.steps.len() ==> (#[trigger] report.result->Ok_0.steps@[i]).carrier().covered(out.0.value_sources()))
                    && crate::reversible_value::managed::retained(report.result->Ok_0.steps@,owner,0,execution.cleanup_state().queues()[0].slots().len())
            },
    {
        let mut typed=None;
        self.run_recorded_root_in(id,execution,mode,Ghost(expected),&mut typed)
    }
    pub(crate) fn run_recorded_root_in<C,G,A,R,X>(&mut self,id:usize,execution:Owner<C,G,A,R,T,M,X>,mode:&mut Option<crate::reversible_value::managed::protected::Context<'_>>,Ghost(expected):Ghost<Option<Seq<crate::reversible_value::managed::Step<T>>>>,typed:&mut Option<crate::reversible_value::managed::protected_typed::Context<'_,T,M>>)->(out:RootOutcome<C,G,A,R,T,M,X,E>)
        requires old(typed).is_some() ==> old(mode).is_none() && old(self).typed_protection_ready(id,&execution,&old(typed)->Some_0),
            expected.is_some() ==> old(mode).is_some()
                && crate::reversible_value::managed::protected::plan(old(self).registry().entries()[id].recipe().payload()->Managed_0.code(),expected.unwrap())
                && crate::reversible_value::managed::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap()),
            old(mode).is_some() ==> old(self).protection_ready(id,&execution,&old(mode)->Some_0),
            old(self).wf(),execution.wf(),
        ensures final(typed).is_some()==old(typed).is_some(),
            final(typed).is_some() ==> final(typed)->Some_0.wf() && final(typed)->Some_0.shape(&old(typed)->Some_0)
                && (out.1.is_err() || out.1->Ok_0.result.is_err() ==> final(typed)->Some_0.states()==old(typed)->Some_0.states() && final(typed)->Some_0.revisions()==old(typed)->Some_0.revisions())
                && (out.1.is_ok() && out.1->Ok_0.result.is_ok() ==> out.1->Ok_0.result->Ok_0.failure.is_none()
                    && crate::reversible_value::managed::protected_typed::addressed(old(typed)->Some_0.targets(),old(typed)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && crate::reversible_value::managed::protected_typed::execution(old(typed)->Some_0.states(),old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.states()==crate::reversible_value::managed::protected_typed::after(old(typed)->Some_0.states(),old(typed)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.revisions()==crate::reversible_value::managed::protected_typed::clocks(old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)),
            expected.is_some() && out.1.is_ok() && out.1->Ok_0.result.is_ok() ==>
                out.1->Ok_0.result->Ok_0.failure.is_none() && crate::reversible_value::managed::protected::same(out.1->Ok_0.result->Ok_0.steps@,expected.unwrap()),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.shape(&old(mode)->Some_0)
                && (out.1.is_err() || out.1->Ok_0.result.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states())
                && (out.1.is_ok() && out.1->Ok_0.result.is_ok() ==> crate::reversible_value::managed::protected::addressed(old(mode)->Some_0.targets(),old(mode)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && crate::reversible_value::managed::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && final(mode)->Some_0.states()==crate::reversible_value::managed::protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)),
            out.1.is_ok() ==> out.1->Ok_0.completion().event().key==final(self).recipe_key()
                && out.1->Ok_0.completion().event().after is Recipes
                && out.1->Ok_0.completion().event().after->Recipes_state.revision==final(self).recipe_history().events.len(),
            out.1.is_ok() ==> out.1->Ok_0.completion().event().after->Recipes_state.entries==crate::lifecycle_state::native::runtime::recipes::project(crate::lifecycle_state::native::runtime::recipes::entries(final(self).registry().entries())),
            old(self).managed_invocation_ready(id,&execution) ==> out.1.is_ok(),
            final(self).wf(),out.0.wf(),out.0.baseline()==out.0.core(),
            final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
            final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.0.core().execution_journal()==execution.execution_journal(),out.0.baseline().value_state()==execution.value_state(),
            out.1.is_ok() && execution.execution_journal()==Some(old(self).journal_spec()) ==>
                out.0.recovery_boundary().is_some() && out.0.recovery_boundary().unwrap().same(&out.1->Ok_0.completion())
                && (forall|group:usize|#[trigger] out.0.histories().contains_key(group) ==> out.0.source_order(group,out.1->Ok_0.completion()))
                && (out.1->Ok_0.result.is_ok() ==> out.1->Ok_0.result->Ok_0.covered_by(out.0.recovery_boundary().unwrap())),
            out.1.is_ok() ==> {
                let report=out.1->Ok_0;let owner=out.0.baseline();
                &&& report.completed() && report.episode_interval() && report.effects_before_return()
                &&& report.completion().journal()==old(self).journal_spec()
                &&& report.endpoint_recovery() && report.retained_recovery(owner,0,execution.cleanup_state().queues()[0].slots().len())
                &&& old(self).owns_execution(id,&owner) && report.start().owner().owns(&owner)
                &&& old(self).registry().entries().contains_key(id) && old(self).registry().entries()[id].recipe().payload() is Managed
                &&& report.function@==old(self).registry().entries()[id].recipe().payload()->Managed_0
                &&& report.function@.valid() && report.function@.bound(report.ports@,old(self).registry().entries()[id].recipe())
                &&& report.revision==old(self).registry().entries()[id].recipe().version()
                &&& report.origin.id==id && report.origin.domain==old(self).state().protocol().domain_id()
                &&& report.work.domain_id()==owner.work_state().domain_id() && report.work.domain_id()==execution.work_state().domain_id()
                &&& report.result.is_ok() ==> owner.value_state().is_some()
                    && report.result->Ok_0.certified(report.function@.code(),report.ports@,owner.value_state().unwrap())
                    && report.result->Ok_0.interpreted(report.function@.code())
                &&& report.result.is_ok() ==> report.result->Ok_0.recovery_history() && report.result->Ok_0.witnessed()
                    && report.result->Ok_0.queued_sources(owner.cleanup_state().queues()[0].link())
                    && report.result->Ok_0.registered(owner.cleanup_state().link(),0)
                    && (forall|i:int|0<=i<report.result->Ok_0.steps.len() ==> (#[trigger] report.result->Ok_0.steps@[i]).carrier().covered(out.0.value_sources()))
                    && crate::reversible_value::managed::retained(report.result->Ok_0.steps@,owner,0,execution.cleanup_state().queues()[0].slots().len())
            },
    {
        let mut mixed=None;
        self.run_recorded_root_guarded(id,execution,mode,Ghost(expected),typed,&mut mixed,Ghost(None))
    }
    #[allow(clippy::too_many_arguments)] // Includes erased plans and borrowed guards.
    pub(crate) fn run_recorded_root_guarded<C,G,A,R,X>(&mut self,id:usize,mut execution:Owner<C,G,A,R,T,M,X>,mode:&mut Option<crate::reversible_value::managed::protected::Context<'_>>,Ghost(expected):Ghost<Option<Seq<crate::reversible_value::managed::Step<T>>>>,typed:&mut Option<crate::reversible_value::managed::protected_typed::Context<'_,T,M>>,mixed:&mut Option<crate::reversible_value::managed::protected_mixed::Context<'_,T,M>>,Ghost(mixed_expected):Ghost<Option<Seq<crate::reversible_value::managed::Step<T>>>>)->(out:RootOutcome<C,G,A,R,T,M,X,E>)
        requires old(mixed).is_some()==mixed_expected.is_some(),
            old(mixed).is_some() ==> old(mode).is_none() && old(typed).is_none() && expected.is_none()
                && old(self).mixed_protection_ready(id,&execution,&old(mixed)->Some_0,mixed_expected.unwrap())
                && crate::reversible_value::managed::protected_mixed::plan(old(self).registry().entries()[id].recipe().payload()->Managed_0.code(),mixed_expected.unwrap())
                && crate::reversible_value::managed::protected::execution(old(mixed)->Some_0.scalar->Some_0.states(),old(mixed)->Some_0.scalar->Some_0.routes(),crate::reversible_value::managed::protected_mixed::scalars(mixed_expected.unwrap())),
            old(typed).is_some() ==> old(mode).is_none() && old(self).typed_protection_ready(id,&execution,&old(typed)->Some_0),
            expected.is_some() ==> old(mode).is_some()
                && crate::reversible_value::managed::protected::plan(old(self).registry().entries()[id].recipe().payload()->Managed_0.code(),expected.unwrap())
                && crate::reversible_value::managed::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap()),
            old(mode).is_some() ==> old(self).protection_ready(id,&execution,&old(mode)->Some_0),
            old(self).wf(),execution.wf(),
        ensures final(mixed).is_some()==old(mixed).is_some(),
            final(mixed).is_some() ==> final(mixed)->Some_0.wf() && final(mixed)->Some_0.shape(&old(mixed)->Some_0)
                && (out.1.is_err() || out.1->Ok_0.result.is_err() ==> *final(mixed)==*old(mixed))
                && (out.1.is_ok() && out.1->Ok_0.result.is_ok() ==> out.1->Ok_0.result->Ok_0.failure.is_none()
                    && crate::reversible_value::managed::protected_mixed::same(out.1->Ok_0.result->Ok_0.steps@,mixed_expected.unwrap())
                    && final(mixed)->Some_0.trace(&old(mixed)->Some_0,out.1->Ok_0.result->Ok_0.steps@)),
            final(typed).is_some()==old(typed).is_some(),
            final(typed).is_some() ==> final(typed)->Some_0.wf() && final(typed)->Some_0.shape(&old(typed)->Some_0)
                && (out.1.is_err() || out.1->Ok_0.result.is_err() ==> final(typed)->Some_0.states()==old(typed)->Some_0.states() && final(typed)->Some_0.revisions()==old(typed)->Some_0.revisions())
                && (out.1.is_ok() && out.1->Ok_0.result.is_ok() ==> out.1->Ok_0.result->Ok_0.failure.is_none()
                    && crate::reversible_value::managed::protected_typed::addressed(old(typed)->Some_0.targets(),old(typed)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && crate::reversible_value::managed::protected_typed::execution(old(typed)->Some_0.states(),old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.states()==crate::reversible_value::managed::protected_typed::after(old(typed)->Some_0.states(),old(typed)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.revisions()==crate::reversible_value::managed::protected_typed::clocks(old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)),
            expected.is_some() && out.1.is_ok() && out.1->Ok_0.result.is_ok() ==>
                out.1->Ok_0.result->Ok_0.failure.is_none() && crate::reversible_value::managed::protected::same(out.1->Ok_0.result->Ok_0.steps@,expected.unwrap()),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.shape(&old(mode)->Some_0)
                && (out.1.is_err() || out.1->Ok_0.result.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states())
                && (out.1.is_ok() && out.1->Ok_0.result.is_ok() ==> crate::reversible_value::managed::protected::addressed(old(mode)->Some_0.targets(),old(mode)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && crate::reversible_value::managed::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)
                    && final(mode)->Some_0.states()==crate::reversible_value::managed::protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out.1->Ok_0.result->Ok_0.steps@)),
            out.1.is_ok() ==> out.1->Ok_0.completion().event().key==final(self).recipe_key()
                && out.1->Ok_0.completion().event().after is Recipes
                && out.1->Ok_0.completion().event().after->Recipes_state.revision==final(self).recipe_history().events.len(),
            out.1.is_ok() ==> out.1->Ok_0.completion().event().after->Recipes_state.entries==crate::lifecycle_state::native::runtime::recipes::project(crate::lifecycle_state::native::runtime::recipes::entries(final(self).registry().entries())),
            old(self).managed_invocation_ready(id,&execution) ==> out.1.is_ok(),
            final(self).wf(),out.0.wf(),out.0.baseline()==out.0.core(),
            final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
            final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.0.core().execution_journal()==execution.execution_journal(),out.0.baseline().value_state()==execution.value_state(),
            out.1.is_ok() && execution.execution_journal()==Some(old(self).journal_spec()) ==>
                out.0.recovery_boundary().is_some() && out.0.recovery_boundary().unwrap().same(&out.1->Ok_0.completion())
                && (forall|group:usize|#[trigger] out.0.histories().contains_key(group) ==> out.0.source_order(group,out.1->Ok_0.completion()))
                && (out.1->Ok_0.result.is_ok() ==> out.1->Ok_0.result->Ok_0.covered_by(out.0.recovery_boundary().unwrap())),
            out.1.is_ok() ==> {
                let report=out.1->Ok_0;let owner=out.0.baseline();
                &&& report.completed() && report.episode_interval() && report.effects_before_return()
                &&& report.completion().journal()==old(self).journal_spec()
                &&& report.endpoint_recovery() && report.retained_recovery(owner,0,execution.cleanup_state().queues()[0].slots().len())
                &&& old(self).owns_execution(id,&owner) && report.start().owner().owns(&owner)
                &&& old(self).registry().entries().contains_key(id) && old(self).registry().entries()[id].recipe().payload() is Managed
                &&& report.function@==old(self).registry().entries()[id].recipe().payload()->Managed_0
                &&& report.function@.valid() && report.function@.bound(report.ports@,old(self).registry().entries()[id].recipe())
                &&& report.revision==old(self).registry().entries()[id].recipe().version()
                &&& report.origin.id==id && report.origin.domain==old(self).state().protocol().domain_id()
                &&& report.work.domain_id()==owner.work_state().domain_id() && report.work.domain_id()==execution.work_state().domain_id()
                &&& report.result.is_ok() ==> owner.value_state().is_some()
                    && report.result->Ok_0.certified(report.function@.code(),report.ports@,owner.value_state().unwrap())
                    && report.result->Ok_0.interpreted(report.function@.code())
                &&& report.result.is_ok() ==> report.result->Ok_0.recovery_history() && report.result->Ok_0.witnessed()
                    && report.result->Ok_0.queued_sources(owner.cleanup_state().queues()[0].link())
                    && report.result->Ok_0.registered(owner.cleanup_state().link(),0)
                    && (forall|i:int|0<=i<report.result->Ok_0.steps.len() ==> (#[trigger] report.result->Ok_0.steps@[i]).carrier().covered(out.0.value_sources()))
                    && crate::reversible_value::managed::retained(report.result->Ok_0.steps@,owner,0,execution.cleanup_state().queues()[0].slots().len())
            },
    {
        let report=self.run_managed_root_guarded(id,&mut execution,mode,Ghost(expected),typed,mixed,Ghost(mixed_expected));
        let tracked boundary=match report {
            Ok(ref result)=>if execution.execution_journal()==Some(result.completion().journal()) {Some(result.completion_witness().duplicate())} else {None},
            Err(_)=>None,
        };
        let mut owner=RecordedExecution::new(execution);
        proof {owner.facts();}
        owner.recovery_boundary=Tracked(boundary);
        proof {
            if let Ok(ref result)=report {if let Ok(ref inner)=result.result {
                owner.value_sources.borrow_mut().retain_report(inner);
                inner.cover_return(result.completion());
                if owner.recovery_boundary().is_some() {
                    assert(owner.recovery_boundary().unwrap().events().take(result.completion().events().len() as int) =~= result.completion().events());
                    inner.extend_boundary(result.completion(),owner.recovery_boundary().unwrap());
                }
            }}
            reveal(RecordedExecution::wf);
            if let Ok(ref result)=report {if owner.recovery_boundary().is_some() {
                let boundary=owner.recovery_boundary().unwrap();
                assert(boundary.events().take(result.completion().events().len() as int) =~= result.completion().events());
                assert forall|group:usize|#[trigger] owner.histories().contains_key(group) implies owner.source_order(group,result.completion()) by {
                    assert(owner.histories()[group].events().len()==0);
                }
            }}
        }
        (owner,report)
    }
}
}
