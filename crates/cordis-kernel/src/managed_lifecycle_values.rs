//! Raw reversible operations execute through the recorded production owner.
//! The caller receives the real result/inverse; observation is automatic and
//! erased. Queue registration and ownership remain explicit, separate actions.
use super::RecordedExecution;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::interleaving::{Attempt, Event, Forward};
use crate::reversible_value::{self as scalar, joint, payload};
use crate::versioned_value::Rejected;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    /// Inspect the real scalar owner, including operations made through raw
    /// handles. The returned census covers the complete captured lifetime.
    pub fn scalar_source_snapshot(&self,value:&scalar::ReversibleValue)->(out:scalar::Snapshot)
        requires self.wf(),
        ensures out.certified(),out.object()==value.object(),out.journal_spec()==value.journal_spec(),
            super::super::super::sources::producer::Producer::<T>::Scalar(out).certified(),
            self.recovery_boundary().is_some() && value.journal_spec()==self.recovery_boundary().unwrap().journal() ==>
                self.recovery_boundary().unwrap().events().len()<=out.joint_spec().events().len()
                && out.joint_spec().events().take(self.recovery_boundary().unwrap().events().len() as int)==self.recovery_boundary().unwrap().events(),
    {
        proof {self.facts();}
        let tracked cause=match self.recovery_boundary.borrow() {Some(receipt)=>Some(receipt),None=>None};
        let out=value.snapshot_caused(Tracked(cause));
        proof {super::super::super::sources::producer::Producer::<T>::Scalar(out).certify();}
        out
    }
    /// Capture and retain the actual payload source, including after retirement.
    /// No user Arc is cloned and no executable audit history is allocated.
    pub fn payload_source_snapshot(&mut self,value:&payload::SharedPayload<T>)->(out:Tracked<payload::source::Source<T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),
            final(self).histories()==old(self).histories(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),
            final(self).value_sources().extends(old(self).value_sources()),out@.wf(),
            out@.observation().owner.source()==value.source(),out@.observation().owner.journal_spec()==value.journal_spec(),out@.observation().owner.key()==value.key(),
            final(self).value_sources().covers(value.source(),out@.observation().states),
            super::super::super::sources::producer::Producer::Payload(out@).certified(),
    {
        proof {self.facts();}
        let out=value.source_snapshot();
        proof {self.value_sources.borrow_mut().retain(out.borrow().witness());reveal(RecordedExecution::wf);reveal(RecordedExecution::source_order_extends);super::super::super::sources::producer::Producer::Payload(out@).certify();}
        out
    }

    /// Source capture never fabricates a queue slot or consumes another owner's
    /// inverse. It extends every retained history, including removed groups.
    pub open spec fn observed_only(&self,prior:&Self,suffix:Seq<Event<A,R,T,M,X>>)->bool {
        &&& self.wf() && self.core()==prior.core() && self.baseline()==prior.baseline()
        &&& self.origins()==prior.origins() && self.terminal()==prior.terminal()
        &&& self.value_sources().extends(prior.value_sources())
        &&& self.histories().dom()==prior.histories().dom()
        &&& forall|id:usize|#[trigger] prior.histories().contains_key(id) ==> {
            &&& self.histories()[id].initial()==prior.histories()[id].initial()
            &&& self.histories()[id].current()==prior.histories()[id].current()
            &&& self.histories()[id].events()==prior.histories()[id].events()+suffix
        }
        &&& prior.recovery_boundary().is_some() ==> self.recovery_boundary().is_some()
            && self.recovery_boundary().unwrap().covers(&prior.recovery_boundary().unwrap())
    }
    proof fn capture_value_event(tracked &mut self,event:Event<A,R,T,M,X>,tracked receipt:&joint::Receipt)
        requires old(self).wf(),event.source(),event.carrier().covered(old(self).value_sources()),
            receipt.wf(),receipt.same(&event.checkpoint()),
            old(self).recovery_boundary().is_some() && event.checkpoint().journal()==old(self).recovery_boundary().unwrap().journal() ==>
                event.checkpoint().covers(&old(self).recovery_boundary().unwrap()) && old(self).recovery_boundary().unwrap().events().len()<=event.read_cut(),
        ensures final(self).source_order_extends(old(self)),final(self).observed_only(old(self),seq![event]),
            old(self).core().execution_journal()==Some(receipt.journal()) ==>
                final(self).recovery_boundary().is_some() && final(self).recovery_boundary().unwrap().covers(receipt),
    {
        let ghost prior=*self;self.facts();
        self.observe_foreign(event);
        let tracked incoming=Some(receipt.duplicate());self.join_boundary(&incoming);
        assert forall|id:usize|#[trigger] old(self).histories().contains_key(id) implies
            self.histories()[id].events()==old(self).histories()[id].events()+seq![event] by {
            assert(self.histories()[id].events() =~= old(self).histories()[id].events()+seq![event]);
        }
        self.facts();event.facts();
        self.extend_source_order(&prior,seq![event]);
    }
    /// Successful forwards are observed at their actual write. Rejections have
    /// no inverse and make no value change; their real receipt still advances
    /// the causal boundary. A capacity/overflow error cannot hide a write.
    pub fn apply_scalar_observed(&mut self,value:&scalar::ReversibleValue,operation:scalar::Operation,branch:scalar::Branch)
        ->(out:Result<scalar::Applied,scalar::ValueError>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).observed_only(old(self),if out.is_ok() {seq![Event::Forward(Forward::Scalar(out->Ok_0.inverse))]} else {Seq::empty()}),
            out.is_ok() ==> out->Ok_0.corresponds(value,operation,branch) && out->Ok_0.pending_for(false),
            out.is_ok() && old(self).recovery_boundary().is_some() && value.journal_spec()==old(self).recovery_boundary().unwrap().journal() ==>
                out->Ok_0.inverse.origin().follows(&old(self).recovery_boundary().unwrap()),
            old(self).core().execution_journal()==Some(value.journal_spec()) ==> final(self).recovery_boundary().is_some(),
            out.is_ok() && old(self).core().execution_journal()==Some(value.journal_spec()) ==>
                final(self).recovery_boundary().unwrap().covers(&out->Ok_0.inverse.origin()),
            out.is_err() ==> out==Err(scalar::ValueError::Capacity) || out==Err(scalar::ValueError::Overflow),
    {
        let ghost prior=*self;
        proof {self.facts();}
        let tracked cause=match self.recovery_boundary.borrow() {Some(receipt)=>Some(receipt.duplicate()),None=>None};
        let tracked mut attempts=scalar::attempt::Ledger::new();
        let out=value.apply_pending_following(operation,branch,Ghost(false),Tracked(&mut attempts),Tracked(cause));
        proof {
            let tracked receipt=attempts.latest();
            if let Ok(ref applied)=out {
                self.capture_value_event(Event::Forward(Forward::Scalar(applied.inverse)),&receipt);
            } else {
                attempts.rejection_step();let tracked incoming=Some(receipt);self.join_boundary(&incoming);self.facts();
                self.extend_source_order(&prior,Seq::empty());
                assert forall|id:usize|#[trigger] old(self).histories().contains_key(id) implies
                    self.histories()[id].events()==old(self).histories()[id].events()+Seq::<Event<A,R,T,M,X>>::empty() by {};
            }
        }
        out
    }
    /// The real payload history is retained before returning the inverse. Equal
    /// keys/revisions do not substitute for persistent source agreement.
    pub fn apply_payload_observed(&mut self,value:&payload::SharedPayload<T>,replacement:Arc<T>)
        ->(out:Result<payload::restoration::Applied<T>,Rejected<Arc<T>>>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).observed_only(old(self),if out.is_ok() {seq![Event::Forward(Forward::Payload(out->Ok_0.inverse))]} else {Seq::empty()}),
            out.is_ok() ==> out->Ok_0.wf(false) && out->Ok_0.inverse.owner()==*value && out->Ok_0.inverse.after().value==replacement
                && Event::<A,R,T,M,X>::Forward(Forward::Payload(out->Ok_0.inverse)).carrier().covered(final(self).value_sources()),
            out.is_ok() && old(self).recovery_boundary().is_some() && value.journal_spec()==old(self).recovery_boundary().unwrap().journal() ==>
                out->Ok_0.inverse.after().commit.follows(&old(self).recovery_boundary().unwrap()),
            out.is_ok() && old(self).core().execution_journal()==Some(value.journal_spec()) ==>
                final(self).recovery_boundary().is_some() && final(self).recovery_boundary().unwrap().covers(&out->Ok_0.inverse.after().commit),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.value==replacement,
    {
        let ghost prior=*self;
        proof {self.facts();}
        let tracked mut causes=Map::<(int,bool),joint::Receipt>::tracked_empty();
        proof {if let Some(receipt)=self.recovery_boundary.borrow() {causes.tracked_insert((-1int,false),receipt.duplicate());}}
        let (out,_rejection)=value.apply_managed_following(replacement,Ghost(false),Tracked(&causes));
        proof {
            if let Ok(ref applied)=out {
                if old(self).recovery_boundary().is_some() && value.journal_spec()==old(self).recovery_boundary().unwrap().journal() {
                    assert(causes.contains_key((-1int,false)));
                    assert(applied.inverse.after().commit.follows(&causes[(-1int,false)]));
                }
                let tracked witness=applied.inverse.history_witness();
                self.value_sources.borrow_mut().retain(witness);reveal(RecordedExecution::wf);
                let tracked receipt=applied.inverse.receipt();
                let ghost middle=*self;
                self.capture_value_event(Event::Forward(Forward::Payload(applied.inverse)),&receipt);
                self.rebase_source_order(&prior,&middle);
            } else {
                assert forall|id:usize|#[trigger] old(self).histories().contains_key(id) implies
                    self.histories()[id].events()==old(self).histories()[id].events()+Seq::<Event<A,R,T,M,X>>::empty() by {};
                if self.recovery_boundary().is_some() {let r=self.recovery_boundary().unwrap();assert(r.events().take(r.events().len() as int) =~= r.events());}
                self.extend_source_order(&prior,Seq::empty());
            }
        }
        out
    }
    /// Consume the actual linear scalar inverse. A blocked attempt returns it
    /// unchanged and is still observed, allowing an authentic later retry.
    pub fn restore_scalar_observed(&mut self,inverse:scalar::Inverse)
        ->(out:(Result<scalar::Snapshot,scalar::Inverse>,Tracked<joint::Receipt>))
        requires old(self).wf(),inverse.recorded(),
        ensures final(self).source_order_extends(old(self)),scalar::restoration::attempted(&out.1@,inverse,out.0.is_ok()),
            final(self).observed_only(old(self),seq![Event::Restore(Attempt::Scalar {inverse,receipt:out.1@})]),
            out.0.is_err() ==> out.0->Err_0==inverse,
            out.0.is_ok() ==> out.0->Ok_0.certified() && out.0->Ok_0.state()==inverse.state().before,
            old(self).recovery_boundary().is_some() && inverse.target().journal_spec()==old(self).recovery_boundary().unwrap().journal() ==>
                out.1@.follows(&old(self).recovery_boundary().unwrap()),
            old(self).core().execution_journal()==Some(inverse.target().journal_spec()) ==>
                final(self).recovery_boundary().is_some() && final(self).recovery_boundary().unwrap().covers(&out.1@),
    {
        let ghost prior=*self;
        proof {self.facts();}
        let tracked cause=match self.recovery_boundary.borrow() {Some(receipt)=>Some(receipt.duplicate()),None=>None};
        let ghost original=inverse;
        let out=inverse.restore_following(Tracked(cause));
        proof {self.capture_value_event(Event::Restore(Attempt::Scalar {inverse:original,receipt:out.1@}),out.1.borrow());}
        out
    }
    /// The read, optional successful commit and typed history all come from
    /// the held payload lock. Failure and retirement do not invent a write.
    pub fn restore_payload_observed(&mut self,inverse:&payload::restoration::Inverse<T>)
        ->(out:(payload::restoration::RestoreResult<T>,Tracked<payload::restoration::attempt::Attempt<T>>))
        requires old(self).wf(),inverse.wf(),
        ensures final(self).source_order_extends(old(self)),out.1@.wf(),out.1@.recovered(),out.1@.inverse()==*inverse,out.1@.result()==out.0,
            out.1@.follows_cause(old(self).recovery_boundary()),
            final(self).observed_only(old(self),seq![Event::Restore(Attempt::Payload(out.1@))]),
            Event::<A,R,T,M,X>::Restore(Attempt::Payload(out.1@)).carrier().covered(final(self).value_sources()),
            old(self).core().execution_journal()==Some(inverse.owner().journal_spec()) ==>
                final(self).recovery_boundary().is_some() && final(self).recovery_boundary().unwrap().covers(&out.1@.endpoint()),
    {
        let ghost prior=*self;
        proof {self.facts();}
        let tracked cause=match self.recovery_boundary.borrow() {Some(receipt)=>Some(receipt.duplicate()),None=>None};
        let out=inverse.restore_following(Tracked(cause));
        proof {
            out.1@.boundaries();self.observe_payload_restore(out.1.borrow());
            if prior.recovery_boundary().is_some() && inverse.owner().journal_spec()==prior.recovery_boundary().unwrap().journal() {
                out.1@.endpoint().cover_through(&out.1@.read().checkpoint(),&prior.recovery_boundary().unwrap());
            }
            assert forall|id:usize|#[trigger] old(self).histories().contains_key(id) implies
                self.histories()[id].events()==old(self).histories()[id].events()+seq![Event::Restore(Attempt::Payload(out.1@))] by {
                assert(self.histories()[id].events() =~= old(self).histories()[id].events()+seq![Event::Restore(Attempt::Payload(out.1@))]);
            }
            self.facts();out.1@.facts();
            self.extend_source_order(&prior,seq![Event::Restore(Attempt::Payload(out.1@))]);
        }
        out
    }
}
}
