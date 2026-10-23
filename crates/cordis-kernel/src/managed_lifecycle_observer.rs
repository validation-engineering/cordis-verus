//! Cross-owner observations come from the actual interpreter and dispatcher.
//! The observer retains its own queues; only erased source evidence is added.
use super::RecordedExecution;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    joint,
    managed::interleaving::{sources::order, Event},
};
use crate::{
    cleanup_groups::payload::DispatchResult,
    reversible_value::{
        effect::ScalarEffect,
        managed::{AdmissionError, Function, Report, Slot},
    },
    Port,
};
use vstd::prelude::*;

verus! {
impl<T:?Sized> Report<T> {
    pub proof fn writes_after_covered(&self,preceding:joint::Receipt,earlier:joint::Receipt)
        requires self.after(Some(preceding)),preceding.wf(),earlier.wf(),preceding.covers(&earlier),
        ensures crate::reversible_value::managed::episode::writes_after(self.steps@,Some(earlier)),
    {
        reveal(Report::after);reveal(crate::reversible_value::managed::episode::writes_after);
        assert forall|i:int|0<=i<self.steps.len() && (#[trigger] self.steps@[i]).write().journal()==earlier.journal()
            implies self.steps@[i].write().follows(&earlier) by {self.steps@[i].write().after_cover(&preceding,&earlier);}
    }
}
/// Export cleanup order through a covering predecessor without pretending the
/// earlier observer receipt was the dispatch's exact supplied cause.
pub proof fn cleanup_after_covered<A,R,T:?Sized,M,X>(dispatch:&crate::reversible_value::managed::cleanup_path::Turn<A,R,T,M,X>,preceding:joint::Receipt,earlier:joint::Receipt)
    requires dispatch.follows_boundary(Some(preceding)),preceding.wf(),earlier.wf(),preceding.covers(&earlier),
    ensures dispatch.follows_boundary(Some(earlier)),
{
    if dispatch.queue_link().is_some() && dispatch.queue_link().unwrap().0==earlier.journal() {
        dispatch.acknowledgement().unwrap().after_cover(&preceding,&earlier);
        if dispatch.checkpoint().journal()==earlier.journal() {dispatch.checkpoint().cover_through(&preceding,&earlier);}
    }
}
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    /// Compare authentic receipt prefixes. This changes no runtime state and
    /// acquires no lock; independent Journals retain independent boundaries.
    pub(crate) proof fn join_boundary(tracked &mut self,tracked incoming:&Option<joint::Receipt>)
        requires old(self).wf(),incoming.is_some() ==> incoming.unwrap().wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),
            final(self).histories()==old(self).histories(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            old(self).recovery_boundary().is_some() ==> final(self).recovery_boundary().is_some()
                && final(self).recovery_boundary().unwrap().covers(&old(self).recovery_boundary().unwrap()),
            incoming.is_some() && old(self).core().execution_journal()==Some(incoming.unwrap().journal()) ==>
                final(self).recovery_boundary().is_some() && final(self).recovery_boundary().unwrap().covers(&incoming.unwrap()),
    {
        self.facts();let prior=*self;let original=self.recovery_boundary();
        if let Some(journal)=self.core().execution_journal() {
            let tracked boundary=crate::lifecycle_state::native::runtime::child_recovery::release_cause(self.recovery_boundary.borrow(),incoming,journal);
            self.recovery_boundary=Tracked(boundary);
        }
        if original.is_some() && self.recovery_boundary()==original {
            assert(original.unwrap().events().take(original.unwrap().events().len() as int) =~= original.unwrap().events());
        }
        reveal(RecordedExecution::wf);
        self.extend_source_order(&prior,Seq::empty());
    }

    /// Execute a foreign managed call and record its entire successful prefix
    /// in the observing owner, including a prefix followed by failure.
    #[verifier::spinoff_prover]
    pub fn run_function_observed<C2,G2,E:ScalarEffect+Copy>(&mut self,id:usize,function:&Function<E,T>,ports:&[Port],_observer:&mut RecordedExecution<C2,G2,A,R,T,M,X>)
        ->(out:Result<Report<T>,AdmissionError>)
        requires old(self).wf(),old(_observer).wf(),function.valid(),
        ensures old(self).core().execution_journal()==old(_observer).core().execution_journal() ==>
                final(self).source_order_extends(old(self)) && final(_observer).source_order_extends(old(_observer)),
            final(self).value_sources().extends(old(self).value_sources()),final(_observer).value_sources().extends(old(_observer).value_sources()),final(self).observations_extend(old(self),final(_observer),old(_observer)),
            final(self).wf(),final(_observer).wf(),
            final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            final(_observer).core()==old(_observer).core(),final(_observer).baseline()==old(_observer).baseline(),
            final(_observer).origins()==old(_observer).origins(),final(_observer).terminal()==old(_observer).terminal(),
            final(_observer).histories().dom()==old(_observer).histories().dom(),
            out.is_ok() ==> out->Ok_0.recovery_history() && out->Ok_0.ordered()
                && (forall|i:int|0<=i<out->Ok_0.steps.len() ==> (#[trigger] out->Ok_0.steps@[i]).carrier().covered(final(self).value_sources()) && out->Ok_0.steps@[i].carrier().covered(final(_observer).value_sources()))
                && (forall|i:int|0<=i<out->Ok_0.steps.len() ==> final(self).owns_forward(id,#[trigger] out->Ok_0.steps@[i])),
            out.is_ok() && old(_observer).recovery_boundary().is_some()
                && old(self).core().execution_journal()==Some(old(_observer).recovery_boundary().unwrap().journal()) ==>
                    crate::reversible_value::managed::episode::writes_after(out->Ok_0.steps@,old(_observer).recovery_boundary()),
            out.is_ok() && final(self).recovery_boundary().is_some()
                && old(_observer).core().execution_journal()==Some(final(self).recovery_boundary().unwrap().journal()) ==>
                    final(_observer).recovery_boundary().is_some() && out->Ok_0.covered_by(final(_observer).recovery_boundary().unwrap()),
            out.is_err() ==> final(self).core()==old(self).core() && final(self).histories()==old(self).histories(),
            forall|group:usize|#[trigger] old(_observer).histories().contains_key(group) ==> {
                let before=old(_observer).histories()[group];let after=final(_observer).histories()[group];
                &&& after.initial()==before.initial() && after.current()==before.current()
                &&& after.events()==if out.is_ok() {before.events()+super::function::forwards(out->Ok_0.steps@)} else {before.events()}
            },
    {
        hide(joint::valid);hide(joint::step);
        let ghost source=*self;let ghost original=*_observer;
        proof {_observer.facts();self.join_boundary(_observer.recovery_boundary_witness());}
        proof {self.facts();}
        let ghost preceding=self.recovery_boundary();
        let out=self.run_function(id,function,ports);
        proof {
            let suffix=if out.is_ok() {super::function::forwards(out->Ok_0.steps@)} else {Seq::<Event<A,R,T,M,X>>::empty()};
            if let Ok(ref report)=out {
                reveal(Report::recovery_history);
                self.facts();_observer.merge_sources(self.value_sources.borrow());
                _observer.record_call(report.steps@);
                if original.recovery_boundary().is_some() && source.core().execution_journal()==Some(original.recovery_boundary().unwrap().journal()) {
                    assert(preceding.is_some());assert(report.after(preceding));assert(preceding==Some(preceding.unwrap()));
                    report.writes_after_covered(preceding.unwrap(),original.recovery_boundary().unwrap());
                }
            }
            let ghost boundary=self.recovery_boundary();
            self.facts();_observer.join_boundary(self.recovery_boundary_witness());
            _observer.facts();
            if let Ok(ref report)=out {if boundary.is_some() && _observer.core().execution_journal()==Some(boundary.unwrap().journal()) {
                report.extend_boundary(boundary.unwrap(),_observer.recovery_boundary().unwrap());
            }}
            _observer.facts();self.facts();
            _observer.merge_sources(self.value_sources.borrow());
            self.shared_observations(&source,_observer,&original,suffix);
            source.facts();original.facts();self.facts();_observer.facts();
            if out.is_err() && preceding.is_some() {
                assert(self.recovery_boundary()==preceding);
                assert(preceding.unwrap().events().take(preceding.unwrap().events().len() as int) =~= preceding.unwrap().events());
            }
            if source.recovery_boundary().is_some() {
                self.recovery_boundary().unwrap().cover_through(&preceding.unwrap(),&source.recovery_boundary().unwrap());
            }
            if self.recovery_boundary().is_some() {
                let end=self.recovery_boundary().unwrap();assert(end.covers(&end)) by {assert(end.events().take(end.events().len() as int) =~= end.events());}
            }
            if source.core().execution_journal()==original.core().execution_journal() {
                if source.recovery_boundary().is_some() && order::local(suffix,source.recovery_boundary().unwrap().journal()) {
                    if let Ok(ref report)=out {
                        report.source_order::<A,R,M,X>(preceding.unwrap(),boundary.unwrap());
                        order::through(suffix,source.recovery_boundary().unwrap(),preceding.unwrap(),boundary.unwrap(),self.recovery_boundary().unwrap());
                    }
                }
                self.extend_source_order(&source,suffix);
                if original.recovery_boundary().is_some() && order::local(suffix,original.recovery_boundary().unwrap().journal()) {
                    if let Ok(ref report)=out {
                        report.source_order::<A,R,M,X>(preceding.unwrap(),boundary.unwrap());
                        order::through(suffix,original.recovery_boundary().unwrap(),preceding.unwrap(),boundary.unwrap(),_observer.recovery_boundary().unwrap());
                    }
                }
                _observer.extend_source_order(&original,suffix);
            }
        }
        out
    }

    /// Dispatch the real foreign queue, then copy its authentic observation to
    /// every retained observer history. Failure remains an observed failure.
    #[verifier::spinoff_prover]
    pub fn dispatch_observed<C2,G2>(&mut self,id:usize,_observer:&mut RecordedExecution<C2,G2,A,R,T,M,X>)
        ->(out:DispatchResult<A,R,std::sync::Arc<Slot<T,M>>,T,X>)
        requires old(self).wf(),old(_observer).wf(),old(self).core().cleanup_state().live(id),
        ensures old(self).core().execution_journal()==old(_observer).core().execution_journal() ==>
                final(self).source_order_extends(old(self)) && final(_observer).source_order_extends(old(_observer)),
            final(self).value_sources().extends(old(self).value_sources()),final(_observer).value_sources().extends(old(_observer).value_sources()),final(self).observations_extend(old(self),final(_observer),old(_observer)),
            final(self).wf(),final(_observer).wf(),
            final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            final(_observer).core()==old(_observer).core(),final(_observer).baseline()==old(_observer).baseline(),
            final(_observer).origins()==old(_observer).origins(),final(_observer).terminal()==old(_observer).terminal(),
            final(_observer).histories().dom()==old(_observer).histories().dom(),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed() ==>
                out->Ok_0.unwrap().authentic() && out->Ok_0.unwrap().carrier().covered(final(self).value_sources())
                    && out->Ok_0.unwrap().carrier().covered(final(_observer).value_sources()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed()
                && old(_observer).recovery_boundary().is_some()
                && old(self).core().execution_journal()==Some(old(_observer).recovery_boundary().unwrap().journal()) ==>
                    out->Ok_0.unwrap().follows_boundary(old(_observer).recovery_boundary()),
            final(self).recovery_boundary().is_some()
                && old(_observer).core().execution_journal()==Some(final(self).recovery_boundary().unwrap().journal()) ==>
                    final(_observer).recovery_boundary().is_some()
                        && final(_observer).recovery_boundary().unwrap().covers(&final(self).recovery_boundary().unwrap()),
            forall|group:usize|#[trigger] old(_observer).histories().contains_key(group) ==> {
                let before=old(_observer).histories()[group];let after=final(_observer).histories()[group];
                &&& after.initial()==before.initial() && after.current()==before.current()
                &&& after.events()==if out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed()
                    {before.events().push(Event::Managed(out->Ok_0.unwrap()))} else {before.events()}
            },
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==> {
                let before=old(self).histories()[group];let after=final(self).histories()[group];
                &&& after.initial()==before.initial()
                &&& after.events()==if out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed()
                    {before.events().push(Event::Managed(out->Ok_0.unwrap()))} else {before.events()}
            },
    {
        hide(joint::valid);hide(joint::step);
        let ghost source=*self;let ghost original=*_observer;
        proof {_observer.facts();self.join_boundary(_observer.recovery_boundary_witness());}
        proof {self.facts();}
        let ghost preceding=self.recovery_boundary();
        let out=self.dispatch(id);
        proof {
            if let Ok(Some(ref dispatch))=out {if dispatch.managed() {
                self.facts();_observer.merge_sources(self.value_sources.borrow());
                _observer.observe_foreign(Event::Managed(*dispatch));
                if original.recovery_boundary().is_some() && source.core().execution_journal()==Some(original.recovery_boundary().unwrap().journal()) {
                    assert(preceding.is_some());assert(dispatch.follows_boundary(Some(preceding.unwrap())));
                    cleanup_after_covered(dispatch,preceding.unwrap(),original.recovery_boundary().unwrap());
                }
            }}
            self.facts();_observer.join_boundary(self.recovery_boundary_witness());
            let suffix=if out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed()
                {seq![Event::Managed(out->Ok_0.unwrap())]} else {Seq::<Event<A,R,T,M,X>>::empty()};
            assert forall|group:usize|#[trigger] source.histories().contains_key(group) implies
                self.histories()[group].events()==source.histories()[group].events()+suffix by {
                assert(self.histories()[group].events() =~= source.histories()[group].events()+suffix);
            }
            assert forall|group:usize|#[trigger] original.histories().contains_key(group) implies
                _observer.histories()[group].events()==original.histories()[group].events()+suffix by {
                assert(_observer.histories()[group].events() =~= original.histories()[group].events()+suffix);
            }
            _observer.facts();self.facts();
            _observer.merge_sources(self.value_sources.borrow());
            self.shared_observations(&source,_observer,&original,suffix);
            source.facts();original.facts();self.facts();_observer.facts();
            if source.recovery_boundary().is_some() {
                self.recovery_boundary().unwrap().cover_through(&preceding.unwrap(),&source.recovery_boundary().unwrap());
            }
            if self.recovery_boundary().is_some() {
                let end=self.recovery_boundary().unwrap();assert(end.covers(&end)) by {assert(end.events().take(end.events().len() as int) =~= end.events());}
            }
            if source.core().execution_journal()==original.core().execution_journal() {
                if source.recovery_boundary().is_some() && order::local(suffix,source.recovery_boundary().unwrap().journal()) {
                    if let Ok(Some(ref dispatch))=out {if dispatch.managed() {
                        assert(suffix[0]==Event::Managed(*dispatch));
                        dispatch.source_order(preceding.unwrap(),self.recovery_boundary().unwrap());
                        let end=self.recovery_boundary().unwrap();assert(end.covers(&end)) by {assert(end.events().take(end.events().len() as int) =~= end.events());}
                        order::through(suffix,source.recovery_boundary().unwrap(),preceding.unwrap(),end,end);
                    }}
                }
                self.extend_source_order(&source,suffix);
                if original.recovery_boundary().is_some() && order::local(suffix,original.recovery_boundary().unwrap().journal()) {
                    if let Ok(Some(ref dispatch))=out {if dispatch.managed() {
                        assert(suffix[0]==Event::Managed(*dispatch));
                        dispatch.source_order(preceding.unwrap(),self.recovery_boundary().unwrap());
                        order::through(suffix,original.recovery_boundary().unwrap(),preceding.unwrap(),self.recovery_boundary().unwrap(),_observer.recovery_boundary().unwrap());
                    }}
                }
                _observer.extend_source_order(&original,suffix);
            }
        }
        out
    }
}
}
