//! Authenticated read/write boundaries of a real typed restoration attempt.
//! A failed attempt is an actual read checkpoint, not a fabricated mutation.
use super::super::{Observation, SharedPayload, Storage};
use super::{Failure, Inverse, Restored};
use crate::reversible_value::joint;
use vstd::prelude::*;

verus! {
#[allow(dead_code)]
pub tracked struct Read<T:?Sized> {
    pub(super) checkpoint:joint::Receipt,pub(super) ghost owner:SharedPayload<T>,
    pub(super) ghost value:Option<Observation<T>>,
}
impl<T:?Sized> Read<T> {
    pub closed spec fn checkpoint(&self)->joint::Receipt {self.checkpoint}
    pub closed spec fn owner(&self)->SharedPayload<T> {self.owner}
    pub closed spec fn value(&self)->Option<Observation<T>> {self.value}
    pub open spec fn state(&self)->Map<nat,joint::Record> {self.checkpoint().events().last().state}
    pub open spec fn wf(&self)->bool {
        &&& self.checkpoint().wf() && self.checkpoint().journal()==self.owner().journal_spec()
        &&& self.state().contains_key(self.owner().key())
        &&& match self.value() {
            Some(value)=>value.wf() && value.owner==self.owner() && self.checkpoint().covers(&value.commit)
                && self.state()[self.owner().key()]==(joint::Record::Payload {source:self.owner().source(),revision:value.revision}),
            None=>self.state()[self.owner().key()] is RetiredPayload
                && self.state()[self.owner().key()]->RetiredPayload_source==self.owner().source(),
        }
    }
    pub(super) proof fn receipt(tracked &self)->(tracked out:joint::Receipt)
        requires self.wf(),ensures out.wf(),out.same(&self.checkpoint()),
    {self.checkpoint.duplicate()}
    pub proof fn recorded(&self)
        requires self.wf(),
        ensures joint::classification::history(self.checkpoint().events()),
            self.value().is_none() ==> self.state()[self.owner().key()] is RetiredPayload,
    {self.checkpoint().classify();}
}
#[allow(dead_code)]
pub tracked struct Attempt<T:?Sized> {
    pub(super) read:Read<T>,pub(super) write:Option<joint::Receipt>,
    pub(super) ghost inverse:Inverse<T>,pub(super) ghost result:Result<Restored<T>,Failure<T>>,
}
impl<T:?Sized> Attempt<T> {
    pub(super) proof fn representation(&self)
        ensures self.read()==self.read,self.write()==self.write,self.inverse()==self.inverse,self.result()==self.result,
    { }
    pub closed spec fn read(&self)->Read<T> {self.read}
    pub closed spec fn write(&self)->Option<joint::Receipt> {self.write}
    pub closed spec fn inverse(&self)->Inverse<T> {self.inverse}
    pub closed spec fn result(&self)->Result<Restored<T>,Failure<T>> {self.result}
    pub open spec fn endpoint(&self)->joint::Receipt {match self.write() {Some(write)=>write,None=>self.read().checkpoint()}}
    pub open spec fn details(&self)->bool {
        &&& self.inverse().wf() && self.read().wf() && self.read().owner()==self.inverse().owner()
        &&& self.read().checkpoint().covers(&self.inverse().after().commit)
        &&& self.write().is_some()==self.result().is_ok()
        &&& match self.result() {
            Ok(restored)=>restored.wf() && self.read().value()==Some(restored.before())
                && restored.before().state()==self.inverse().after().state()
                && restored.after().state()==self.inverse().before().state()
                && restored.before().revision>=self.inverse().after().revision
                && self.write().unwrap().wf() && self.write().unwrap().same(&restored.after().commit)
                && self.write().unwrap().follows(&self.read().checkpoint()),
            Err(failure)=>failure.wf(&self.inverse()) && failure.observation()==self.read().value(),
        }
    }
    #[verifier::opaque]
    pub open spec fn wf(&self)->bool {self.details()}
    pub(super) proof fn establish(&self)
        requires self.details(),ensures self.wf(),
    {reveal(Attempt::wf);}
    pub proof fn facts(&self)
        requires self.wf(),ensures self.details(),
    {reveal(Attempt::wf);}
    pub proof fn boundaries(&self)
        requires self.wf(),
        ensures self.read().wf(),self.read().owner()==self.inverse().owner(),
            self.read().checkpoint().covers(&self.inverse().after().commit),
            self.endpoint().wf(),self.endpoint().journal()==self.inverse().owner().journal_spec(),
            self.endpoint().covers(&self.read().checkpoint()),
    {
        assert(self.read().wf() && self.read().owner()==self.inverse().owner()
            && self.read().checkpoint().covers(&self.inverse().after().commit)) by {self.facts();}
        assert(self.write().is_some() ==> self.write().unwrap().wf()
            && self.write().unwrap().follows(&self.read().checkpoint())) by {self.facts();}
        if self.write().is_none() {
            assert(self.read().checkpoint().events().take(self.read().checkpoint().events().len() as int) =~= self.read().checkpoint().events());
        }
    }
    pub(crate) proof fn domain(&self)
        requires self.wf(),
        ensures self.read().checkpoint().journal()==self.inverse().owner().journal_spec(),
    {self.boundaries();}
    pub open spec fn follows_cause(&self,cause:Option<joint::Receipt>)->bool {
        cause.is_some() && cause.unwrap().journal()==self.inverse().owner().journal_spec() ==>
            self.read().checkpoint().covers(&cause.unwrap())
    }
    pub(crate) proof fn completion_cause(tracked &self)->(tracked out:joint::Receipt)
        requires self.wf(),
        ensures out.wf(),out.same(&self.endpoint()),out.journal()==self.inverse().owner().journal_spec(),
    {self.facts();match &self.write {Some(write)=>write.duplicate(),None=>self.read.checkpoint.duplicate()}}
    /// For success the complete recorded mutation is retained; failure names
    /// the actual read epoch. No intervening native commits are filtered away.
    pub proof fn classified(&self)
        requires self.wf(),
        ensures joint::classification::history(self.endpoint().events()),
            self.result().is_ok() ==> self.endpoint().event().change==joint::Change::PayloadRestore,
            self.result().is_err() ==> self.endpoint().same(&self.read().checkpoint()),
    {self.facts();self.endpoint().classify();}
}
impl<T:?Sized> Inverse<T> {
    /// Holds the real payload lock, then takes one common read epoch. The
    /// journal is retained in the inverse so retirement cannot erase access to
    /// this authoritative owner. No arbitrary T is cloned or dropped here.
    pub(super) fn observe_storage(&self,_storage:&Storage<T>,Tracked(cause):Tracked<&Option<joint::Receipt>>)->(out:Tracked<Read<T>>)
        requires self.wf(),cause.is_some() ==> cause.unwrap().wf(),
            match _storage.live {Some(cell)=>cell.belongs(self.owner()),None=>_storage.retired@.is_some()
                && self.owner().receipt_matches(_storage.retired@.unwrap()) && _storage.retired@.unwrap().event().after is RetiredPayload},
        ensures out@.wf(),out@.owner()==self.owner(),out@.checkpoint().covers(&self.after().commit),
            cause.is_some() && cause.unwrap().journal()==self.owner().journal_spec() ==> out@.checkpoint().covers(&cause.unwrap()),
            out@.value().is_some()==_storage.live.is_some(),
            _storage.live.is_some() ==> out@.value().unwrap().state()==_storage.live.unwrap().state()
                && out@.value().unwrap().history==_storage.live.unwrap().value.history()
                && out@.value().unwrap().states==_storage.live.unwrap().authority@.events()
                && out@.value().unwrap().revision==_storage.live.unwrap().value.revision_spec()
                && out@.value().unwrap().positions==_storage.live.unwrap().positions@
                && out@.value().unwrap().commit.events()==_storage.live.unwrap().member.events(),
    {
        let tracked mut receipts=Map::<u8,joint::Receipt>::tracked_empty();
        proof {
            receipts.tracked_insert(0,self.origin.borrow().duplicate());
            match cause {Some(receipt)=>receipts.tracked_insert(1,receipt.duplicate()),None=>{}}
        }
        let _value=match &_storage.live {Some(cell)=>{
            let _value=cell.evidence(&self.owner);proof {receipts.tracked_insert(2,cell.member.receipt());}Ghost(Some(_value@))
        },None=>{proof {receipts.tracked_insert(2,_storage.retired.borrow().tracked_borrow().duplicate());}Ghost(None)}};
        let view=self.journal.read();
        if let Some(cell)=&_storage.live {cell.member.certify(&view);}
        view.certify_receipts::<u8>(Tracked(&receipts));view.valid_history();
        proof {
            assert(receipts[0].journal()==view.journal_spec());
            assert(receipts[2].journal()==view.journal_spec());
            if let Some(ref cause)=*cause {
                if cause.journal()==view.journal_spec() {assert(receipts[1].same(cause));}
            }
            if _storage.live.is_none() {
                let retired=receipts[2];let frames=view.events();
                assert(frames[retired.at() as int]==retired.events()[retired.at() as int]);
                assert(joint::step(joint::state_at(frames,retired.at()),frames[retired.at() as int].state,retired.event()));
                joint::payload::retained(frames,retired.at()+1,frames.len(),self.owner().key());
            }
        }
        let snapshot=view.finish();let Tracked(checkpoint)=snapshot.checkpoint_receipt();
        Tracked(Read {checkpoint,owner:self.owner(),value:_value@})
    }
}
}

#[path = "payload_restoration.rs"]
pub mod protocol;
