//! Subsequent actual managed calls append both inverse obligations and their
//! forward value observations to the original lifecycle owner's histories.
use super::RecordedExecution;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::{interleaving::Event, Step};
use crate::reversible_value::{
    effect::ScalarEffect,
    managed::{AdmissionError, Function, Report},
};
use crate::Port;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn forwards<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>)->Seq<Event<A,R,T,M,X>> {
    steps.map(|_:int,step:Step<T>|Event::Forward(step.forward_inverse()))
}
proof fn forward_source<A,R,T:?Sized,M,X>(step:Step<T>)
    requires step.recorded_values(),
    ensures Event::<A,R,T,M,X>::Forward(step.forward_inverse()).source(),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
}
impl<T:?Sized> Report<T> {
    #[verifier::opaque]
    pub open spec fn covered_by(&self,end:crate::reversible_value::joint::Receipt)->bool {
        end.wf() && forall|k:(int,bool)|self.receipts().contains_key(k)
            && (#[trigger] self.receipts()[k]).journal()==end.journal() ==> end.covers(&self.receipts()[k])
    }
    pub proof fn cover_return(&self,end:crate::reversible_value::joint::Receipt)
        requires end.wf(),crate::reversible_value::registration::before_return(self.receipts(),end),
        ensures self.covered_by(end),
    {reveal(Report::covered_by);}
    /// Later checkpoints extend earlier coverage without replacing the source
    /// report. This composes any finite sequence of actual owner calls.
    pub proof fn extend_boundary(&self,earlier:crate::reversible_value::joint::Receipt,later:crate::reversible_value::joint::Receipt)
        requires self.covered_by(earlier),later.wf(),later.covers(&earlier),
        ensures self.covered_by(later),
    {
        reveal(Report::covered_by);
        assert forall|k:(int,bool)|self.receipts().contains_key(k) && (#[trigger] self.receipts()[k]).journal()==later.journal()
            implies later.covers(&self.receipts()[k]) by {later.cover_through(&earlier,&self.receipts()[k]);}
    }
    /// A real cleanup read and acknowledgement follow every local receipt
    /// covered by the preceding return, including a failed invocation's prefix.
    pub proof fn before_cleanup<A,R,H,X>(&self,dispatch:&crate::cleanup_groups::payload::Dispatch<A,R,H,T,X>,boundary:crate::reversible_value::joint::Receipt)
        requires self.covered_by(boundary),dispatch.authentic(),dispatch.managed(),dispatch.follows_boundary(Some(boundary)),
            dispatch.queue_link().is_some(),dispatch.queue_link().unwrap().0==boundary.journal(),
        ensures dispatch.acknowledgement().is_some(),
            forall|k:(int,bool)|self.receipts().contains_key(k) && (#[trigger] self.receipts()[k]).journal()==boundary.journal() ==> {
                &&& dispatch.acknowledgement().unwrap().follows(&self.receipts()[k])
                &&& dispatch.checkpoint().journal()==boundary.journal() ==>
                    dispatch.checkpoint().covers(&self.receipts()[k]) && self.receipts()[k].events().len()<=dispatch.read_cut()
            },
    {
        reveal(Report::covered_by);
        assert forall|k:(int,bool)|self.receipts().contains_key(k) && (#[trigger] self.receipts()[k]).journal()==boundary.journal() implies {
            &&& dispatch.acknowledgement().unwrap().follows(&self.receipts()[k])
            &&& dispatch.checkpoint().journal()==boundary.journal() ==>
                dispatch.checkpoint().covers(&self.receipts()[k]) && self.receipts()[k].events().len()<=dispatch.read_cut()
        } by {
            dispatch.acknowledgement().unwrap().after_cover(&boundary,&self.receipts()[k]);
            if dispatch.checkpoint().journal()==boundary.journal() {dispatch.checkpoint().cover_through(&boundary,&self.receipts()[k]);}
        }
    }
    /// Includes failed-prefix receipts and registrations, not only successful
    /// writes. No successful completion or nonempty instruction list is assumed.
    pub proof fn after_call_receipts(&self,earlier:&Self,boundary:crate::reversible_value::joint::Receipt)
        requires self.after(Some(boundary)),earlier.covered_by(boundary),
        ensures forall|j:int,k:(int,bool)|#![trigger self.steps@[j],earlier.receipts()[k]]
            0<=j<self.steps.len() && earlier.receipts().contains_key(k)
                && self.steps@[j].write().journal()==boundary.journal() && earlier.receipts()[k].journal()==boundary.journal()
                ==> self.steps@[j].write().follows(&earlier.receipts()[k]),
    {
        reveal(Report::after);reveal(crate::reversible_value::managed::episode::writes_after);reveal(Report::covered_by);
        assert forall|j:int,k:(int,bool)|#![trigger self.steps@[j],earlier.receipts()[k]]
            0<=j<self.steps.len() && earlier.receipts().contains_key(k)
                && self.steps@[j].write().journal()==boundary.journal() && earlier.receipts()[k].journal()==boundary.journal()
                implies self.steps@[j].write().follows(&earlier.receipts()[k]) by {
            self.steps@[j].write().after_cover(&boundary,&earlier.receipts()[k]);
        }
    }
    /// Compose two actual invocation reports through their retained boundary.
    /// The same-Journal test is explicit: this is no global multi-Journal clock.
    pub proof fn after_call(&self,earlier:&Self,boundary:crate::reversible_value::joint::Receipt)
        requires self.after(Some(boundary)),earlier.witnessed(),earlier.covered_by(boundary),
        ensures forall|i:int,j:int|#![trigger earlier.steps@[i],self.steps@[j]]
            0<=i<earlier.steps.len() && 0<=j<self.steps.len() && self.steps@[j].write().journal()==boundary.journal() ==> {
                let first=earlier.steps@[i];let later=self.steps@[j];
                &&& first.write().journal()==boundary.journal() ==> later.write().follows(&first.write())
                &&& first.insertion().is_some() && first.insertion().unwrap().journal()==boundary.journal() ==> later.write().follows(&first.insertion().unwrap())
            },
            forall|j:int|0<=j<self.steps.len() && (#[trigger] self.steps@[j]).write().journal()==boundary.journal() ==>
                boundary.events().len()<=self.steps@[j].write().at(),
    {
        reveal(Report::after);reveal(crate::reversible_value::managed::episode::writes_after);reveal(Report::covered_by);
        assert forall|i:int,j:int|#![trigger earlier.steps@[i],self.steps@[j]]
            0<=i<earlier.steps.len() && 0<=j<self.steps.len() && self.steps@[j].write().journal()==boundary.journal() implies {
                let first=earlier.steps@[i];let later=self.steps@[j];
                &&& first.write().journal()==boundary.journal() ==> later.write().follows(&first.write())
                &&& first.insertion().is_some() && first.insertion().unwrap().journal()==boundary.journal() ==> later.write().follows(&first.insertion().unwrap())
            } by {
            let first=earlier.steps@[i];let later=self.steps@[j];
            assert(first.witnessed(earlier.receipts(),i));
            if first.write().journal()==boundary.journal() {later.write().after_cover(&boundary,&first.write());}
            if first.insertion().is_some() && first.insertion().unwrap().journal()==boundary.journal() {later.write().after_cover(&boundary,&first.insertion().unwrap());}
        }
    }
}
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    pub(super) proof fn record_call(tracked &mut self,steps:Seq<Step<T>>)
        requires old(self).wf(),forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).recorded_values(),
            forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).carrier().covered(old(self).value_sources()),
        ensures final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),
            final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|id:usize|#[trigger] old(self).histories().contains_key(id) ==> {
                let before=old(self).histories()[id];let after=final(self).histories()[id];
                &&& after.initial()==before.initial() && after.current()==before.current()
                &&& after.events()==before.events()+forwards(steps)
            },
        decreases steps.len(),
    {
        hide(Event::source);hide(Step::recorded_values);hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        if steps.len()>0 {
            let prefix=steps.drop_last();self.record_call(prefix);
            let event=Event::Forward(steps.last().forward_inverse());
            forward_source::<A,R,T,M,X>(steps.last());
            self.observe_foreign(event);
            assert(forwards::<A,R,T,M,X>(steps) =~= forwards::<A,R,T,M,X>(prefix).push(event));
        } else {assert(forwards::<A,R,T,M,X>(steps) =~= Seq::<Event<A,R,T,M,X>>::empty());}
    }
    /// Close a call under the actual Journal read lock. This records the owner
    /// state and includes local writes, registrations and failed-prefix receipts.
    fn close_call(&mut self,_report:&Report<T>)
        requires old(self).wf(),_report.witnessed(),_report.after(old(self).recovery_boundary()),
        ensures final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).core()==old(self).core(),
            final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).histories()==old(self).histories(),final(self).terminal()==old(self).terminal(),
            final(self).recovery_boundary().is_some()==old(self).core().execution_journal().is_some(),
            final(self).recovery_boundary().is_some() ==> _report.covered_by(final(self).recovery_boundary().unwrap())
                && final(self).core().observed_state(crate::reversible_value::joint::state_at(final(self).recovery_boundary().unwrap().events(),final(self).recovery_boundary().unwrap().events().len())),
            old(self).recovery_boundary().is_some() ==> final(self).recovery_boundary().is_some()
                && final(self).recovery_boundary().unwrap().covers(&old(self).recovery_boundary().unwrap()),
    {
        proof {self.facts();}
        let snapshot=self.core.observe_execution_following::<(int,bool)>(Tracked(_report.receipt_witnesses()));
        if let Some(snapshot)=snapshot {
            let Tracked(receipt)=snapshot.checkpoint_receipt();
            proof {
                reveal(Report::covered_by);reveal(Report::after);
                self.recovery_boundary=Tracked(Some(receipt));
            }
        }
        proof {reveal(RecordedExecution::wf);}
    }
    /// The same production interpreter supplies the successful prefix, actual
    /// failure and retained inverses. No caller-provided event list is accepted.
    /// Local writes follow the preceding authentic invocation or cleanup boundary;
    /// the return checkpoint includes this call's local receipts. External
    /// observation completeness and foreign restoration closure remain separate.
    pub fn run_function<E:ScalarEffect+Copy>(&mut self,id:usize,function:&Function<E,T>,ports:&[Port])->(out:Result<Report<T>,AdmissionError>)
        requires old(self).wf(),function.valid(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources().extends(old(self).value_sources()),
            out.is_ok() ==> (forall|i:int|0<=i<out->Ok_0.steps.len() ==> (#[trigger] out->Ok_0.steps@[i]).carrier().covered(final(self).value_sources())),
            out.is_ok() ==> (forall|i:int|0<=i<out->Ok_0.steps.len() ==> final(self).owns_forward(id,#[trigger] out->Ok_0.steps@[i])),
            final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            out.is_ok() ==> out->Ok_0.after(old(self).recovery_boundary())
                && final(self).recovery_boundary().is_some()==final(self).core().execution_journal().is_some(),
            out.is_ok() && final(self).recovery_boundary().is_some() ==> out->Ok_0.covered_by(final(self).recovery_boundary().unwrap())
                && final(self).core().observed_state(crate::reversible_value::joint::state_at(final(self).recovery_boundary().unwrap().events(),final(self).recovery_boundary().unwrap().events().len())),
            out.is_ok() && old(self).recovery_boundary().is_some() ==> final(self).recovery_boundary().is_some()
                && final(self).recovery_boundary().unwrap().covers(&old(self).recovery_boundary().unwrap()),
            out.is_err() ==> *final(self)==*old(self) && old(self).core().function_admission_failure(id,*function,ports@,out->Err_0),
            out.is_ok() ==> old(self).core().value_state().is_some()
                && out->Ok_0.certified(function.code(),ports@,old(self).core().value_state().unwrap())
                && out->Ok_0.ordered() && out->Ok_0.recovery_history()
                && out->Ok_0.queued_sources(final(self).core().cleanup_state().queues()[id].link())
                && out->Ok_0.registered(final(self).core().cleanup_state().link(),id)
                && crate::reversible_value::managed::retained(out->Ok_0.steps@,final(self).core(),id,old(self).histories()[id].initial().len())
                && final(self).histories()[id].starts_with(old(self).histories()[id].initial())
                && final(self).histories()[id].initial().len()==old(self).histories()[id].initial().len()+out->Ok_0.steps.len(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==> final(self).histories()[group].events()==
                if out.is_ok() {old(self).histories()[group].events()+forwards(out->Ok_0.steps@)} else {old(self).histories()[group].events()},
            forall|group:usize|group!=id && #[trigger] old(self).histories().contains_key(group) ==> final(self).histories()[group].initial()==old(self).histories()[group].initial(),
    {
        proof {self.facts();}let ghost before=*self;
        let tracked cause=match self.recovery_boundary.borrow() {Some(receipt)=>Some(receipt.duplicate()),None=>None};
        let ghost preceding=cause;
        let out=self.core.run_function_following(id,function,ports,Tracked(cause));
        proof {
            if let Ok(ref report)=out {
                let tracked mut history=self.histories.borrow_mut().tracked_remove(id);let ghost prior=history;
                assert(before.entry(id));assert(history.matches(before.core().cleanup_state().queues()[id]));
                let queue=self.core.cleanup_state().queues()[id];
                history.extend(queue);history.prefix_transitive(prior,self.origins()[id].slots());
                self.histories.borrow_mut().tracked_insert(id,history);
                reveal(RecordedExecution::wf);assert(self.wf());
                reveal(Report::recovery_history);
                assert forall|i:int|0<=i<report.steps.len() implies self.owns_forward(id,#[trigger] report.steps@[i]) by {
                    let step=report.steps@[i];let token=step.token() as int;
                    assert(token==before.histories()[id].initial().len()+i);
                    assert(self.histories()[id].initial()[token]==queue.slots()[token]);
                }
                self.capture_report(report);
                self.record_call(report.steps@);
                report.equivalent_cause(preceding,before.recovery_boundary());
            } else {reveal(RecordedExecution::wf);}
        }
        if let Ok(ref report)=out {self.close_call(report);}
        proof {
            self.facts();before.facts();
            let suffix=if out.is_ok() {forwards::<A,R,T,M,X>(out->Ok_0.steps@)} else {Seq::empty()};
            if before.recovery_boundary().is_some() && super::super::super::sources::order::local(suffix,before.recovery_boundary().unwrap().journal()) {
                if let Ok(ref report)=out {report.source_order::<A,R,M,X>(before.recovery_boundary().unwrap(),self.recovery_boundary().unwrap());}
            }
            self.extend_source_order(&before,suffix);
        }
        out
    }
}
}
