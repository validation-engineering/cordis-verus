//! Typed continuity derived from two real retained inverse histories.
//! Equality of an executable semantic head is useful only after authentic
//! allocation identity and persistent history agreement have been established.
use super::{Input, Operand};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, payload};
use vstd::prelude::*;

verus! {

impl<T:?Sized> Input<T> {
    /// Compare historical inputs through their authenticated allocation and
    /// history, without rereading the mutable source or invoking T::eq.
    pub fn same_payload_before(&self,other:&Self)->(out:Option<bool>)
        requires self.wf(),other.wf(),self.identity_spec().namespace()==other.identity_spec().namespace(),
        ensures out==Some(true) ==> self.source().address()==other.source().address() && self.source().before()==other.source().before(),
    {
        hide(joint::valid);hide(joint::step);
        let head=match self.operand() {Operand::Payload {head,..}=>*head,_=>return None};
        let other_head=match other.operand() {Operand::Payload {head,..}=>*head,_=>return None};
        if self.identity.same(&other.identity)!=Some(true) || head!=other_head {return Some(false);}
        proof {
            let a=self.source().result->Payload_0.inverse();let b=other.source().result->Payload_0.inverse();
            a.provenance();b.provenance();a.source_history();b.source_history();
            joint::payload::same_source_receipts(self.payload_receipt.borrow().tracked_borrow(),other.payload_receipt.borrow().tracked_borrow());
            let tracked ah=self.payload_history.borrow().tracked_borrow();let tracked bh=other.payload_history.borrow().tracked_borrow();
            if ah.events().len()>=bh.events().len() {ah.prefix(bh);} else {bh.prefix(ah);}
            assert(a.after().states[head as int]==a.before().state());
            assert(b.after().states[head as int]==b.before().state());
        }
        Some(true)
    }
    /// Some(true) derives full semantic value/depth continuity without T: Eq,
    /// pointer casts, live source rereads or a caller-supplied equality premise.
    /// None denotes an unavailable allocation name or non-payload input.
    pub fn continues_payload(&self,previous:&Self)->(out:Option<bool>)
        requires self.wf(),previous.wf(),self.identity_spec().namespace()==previous.identity_spec().namespace(),
        ensures out.is_some()==(self.source().result is Payload && previous.source().result is Payload
                && self.identity_spec().number_spec().is_some() && previous.identity_spec().number_spec().is_some()),
            out==Some(true) ==> self.source().address()==previous.source().address()
                && self.source().before()==previous.source().after(),
            out==Some(false) ==> self.source().address()!=previous.source().address()
                || self.source().before()!=previous.source().after(),
    {
        hide(joint::valid);hide(joint::step);
        let head=match self.operand() {Operand::Payload {head,..}=>*head,_=>return None};
        let prior=previous.payload_head?;
        let same=self.identity.same(&previous.identity)?;
        if !same {return Some(false);}
        if head!=prior {return Some(false);}
        proof {
            let a=self.source().result->Payload_0.inverse();let b=previous.source().result->Payload_0.inverse();
            a.provenance();b.provenance();a.source_history();b.source_history();
            joint::payload::same_source_receipts(self.payload_receipt.borrow().tracked_borrow(),previous.payload_receipt.borrow().tracked_borrow());
            let tracked ah=self.payload_history.borrow().tracked_borrow();let tracked bh=previous.payload_history.borrow().tracked_borrow();
            if ah.events().len()>=bh.events().len() {ah.prefix(bh);} else {bh.prefix(ah);}
            assert(a.before().state().head==b.after().state().head);
            assert(a.before().states[a.before().state().head as int]==a.before().state());
            assert(a.after().states[a.before().state().head as int]==a.before().state());
            assert(b.after().states[b.after().state().head as int]==b.after().state());
            assert(a.before().state()==b.after().state());
        }
        Some(true)
    }
}
}
