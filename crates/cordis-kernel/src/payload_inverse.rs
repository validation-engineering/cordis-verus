//! Checked replacement and strict restoration of actual typed payloads.
//! A monotone read revision is distinct from the reversible semantic head.
//! Each managed forward reserves one future revision for its inverse.
use super::super::{history::Witness, joint};
#[cfg(verus_keep_ghost)]
use super::values;
use super::{Cell, Observation, Replacement, SharedPayload, State};
use crate::versioned_value::{Rejected, ReplaceError};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub type RestoreResult<T> = Result<Restored<T>,Failure<T>>;
pub(crate) type ApplyResult<T> = (Result<Applied<T>,Rejected<Arc<T>>>,Ghost<Option<ForwardRejection<T>>>);
pub(crate) type AttemptResult<T> = (RestoreResult<T>,Tracked<attempt::Attempt<T>>);
type LiveResult<T> = (RestoreResult<T>,Tracked<Option<joint::Receipt>>);
impl<T:?Sized> Cell<T> {
    fn advance(&mut self,_owner:&SharedPayload<T>,value:Arc<T>,head:u64,depth:u64,
        Ghost(mode):Ghost<(joint::Change,bool)>,Tracked(cause):Tracked<Option<joint::Receipt>>)
        ->(out:(Arc<T>,Tracked<Option<joint::Pending>>))
        requires old(self).belongs(*_owner),old(self).value.revision_spec()<u64::MAX,
            head<=old(self).value.revision_spec()+1,
            old(self).value.revision_spec() as int+1+depth as int<=u64::MAX,
            head<=old(self).value.revision_spec() ==> old(self).authority@.events()[head as int]==(State {value,head,depth}),
            joint::payload::mutation(mode.0),mode.1 ==> mode.0==joint::Change::PayloadApply,
            cause.is_some() ==> cause.unwrap().wf(),
        ensures final(self).belongs(*_owner),out.0==old(self).value.value(),
            final(self).state()==(State {value,head,depth}),
            final(self).value.revision_spec()==old(self).value.revision_spec()+1,
            final(self).value.history()==old(self).value.history().push(value),
            final(self).authority@.events()==old(self).authority@.events().push(State {value,head,depth}),
            old(self).member.events().len()<final(self).member.events().len(),
            final(self).member.events().take(old(self).member.events().len() as int)==old(self).member.events(),
            final(self).member.events().last().event.change==mode.0,
            cause.is_some() && cause.unwrap().journal()==_owner.journal_spec() ==> cause.unwrap().events().len()<final(self).member.events().len()
                && final(self).member.events().take(cause.unwrap().events().len() as int)==cause.unwrap().events(),
            joint::pending_matches(out.1@,_owner.journal_spec(),_owner.key(),(final(self).member.events().len()-1) as nat,mode.1),
    {
        let ghost before=*self;
        proof {self.value.representation();}
        let previous=match self.value.replace(value) {Ok(previous)=>previous,Err(_)=>{assert(false);panic!("reserved revision");}};
        self.head=head;self.depth=depth;
        proof {let state=self.state();self.authority.borrow_mut().append(state);
            assert(values(self.authority@.events()) =~= self.value.history());reveal(joint::changes);}
        let pending=self.member.update_following(Ghost(joint::Record::Payload {source:_owner.source(),revision:self.value.revision_spec()}),Ghost(mode.0),Tracked(cause),Ghost(mode.1),Tracked(None));
        proof {joint::payload::append_indexed(before.value.history().len(),before.positions@,before.member.events(),self.member.events(),_owner.key(),_owner.source());}
        self.positions=Ghost(before.positions@.push((self.member.events().len()-1) as nat));
        (previous,pending)
    }
}
#[allow(dead_code)]
pub struct Inverse<T:?Sized> {
    owner:SharedPayload<T>,journal:joint::Journal,previous:Arc<T>,head:u64,depth:u64,expected:u64,
    before:Ghost<Observation<T>>,after:Ghost<Observation<T>>,origin:Tracked<joint::Receipt>,witness:Tracked<Witness<State<T>>>,
}
impl<T:?Sized> Inverse<T> {
    #[verifier::type_invariant]
    closed spec fn invariant(&self)->bool {self.wf()}
    pub fn representation(&self) ensures self.wf(), {proof {use_type_invariant(self);}}
    pub closed spec fn owner(&self)->SharedPayload<T> {self.owner}
    pub closed spec fn before(&self)->Observation<T> {self.before@}
    pub closed spec fn after(&self)->Observation<T> {self.after@}
    pub closed spec fn wf(&self)->bool {
        self.journal==self.owner().journal_spec() && self.before().wf() && self.after().wf() && self.before().owner==self.owner() && self.after().owner==self.owner()
            && self.previous==self.before().value && self.head==self.before().state().head && self.depth==self.before().state().depth
            && self.expected==self.after().state().head && self.expected==self.after().revision
            && self.after().revision==self.before().revision+1 && self.after().state().depth==self.depth+1
            && self.after().states==self.before().states.push(self.after().state())
            && self.after().commit.follows(&self.before().commit) && self.after().commit.event().change==joint::Change::PayloadApply
            && self.origin@.wf() && self.origin@.same(&self.after().commit)
            && self.witness@.wf() && self.witness@.source()==self.owner().source() && self.witness@.events()==self.after().states
    }
    pub proof fn provenance(&self)
        requires self.wf(),
        ensures self.before().wf(),self.after().wf(),self.before().owner==self.owner(),self.after().owner==self.owner(),
            self.after().commit.wf(),self.after().commit.journal()==self.owner().journal_spec(),
            self.after().commit.event().key==self.owner().key(),self.after().commit.forward(),
    { }
    pub(crate) proof fn receipt(tracked &self)->(tracked out:joint::Receipt)
        requires self.wf(),ensures out.wf(),out.same(&self.after().commit),out.forward(),
            out.journal()==self.owner().journal_spec(),out.event().key==self.owner().key(),
    {self.origin.borrow().duplicate()}
    /// The strict inverse operates on the complete semantic state, for every
    /// input in that carrier. The anti-stale revision is a separate transition.
    pub open spec fn undo(&self,current:State<T>)->Option<State<T>> {
        if current==self.after().state() {Some(self.before().state())} else {None}
    }
    /// Rejection leaves the live cell unchanged. Success never needs an extra
    /// capacity assumption: the actual cell reserved its outstanding depth.
    pub fn restore(&self)->(out:Result<Restored<T>,Failure<T>>)
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.before().owner==self.owner()
            && out->Ok_0.before().state()==self.after().state() && out->Ok_0.after().state()==self.before().state()
            && out->Ok_0.before().revision>=self.after().revision,
            out.is_err() ==> out->Err_0.wf(self) && (out->Err_0.observation().is_some() == (out->Err_0.error_spec()==RestoreError::Interference)),
    {self.restore_following(Tracked(None)).0}
    pub(crate) fn restore_following(&self,Tracked(cause):Tracked<Option<joint::Receipt>>)
        ->(out:AttemptResult<T>)
        requires cause.is_some() ==> cause.unwrap().wf(),
        ensures out.1@.wf(),out.1@.inverse()==*self,out.1@.result()==out.0,out.1@.follows_cause(cause),
            out.0.is_ok() ==> out.0->Ok_0.wf() && out.0->Ok_0.before().owner==self.owner()
                && out.0->Ok_0.before().state()==self.after().state() && out.0->Ok_0.after().state()==self.before().state()
                && out.0->Ok_0.before().revision>=self.after().revision,
            out.0.is_err() ==> out.0->Err_0.wf(self) && (out.0->Err_0.observation().is_some()==(out.0->Err_0.error_spec()==RestoreError::Interference)),
    {
        proof {use_type_invariant(self);}
        let (mut storage,guard)=self.owner.inner.acquire_write();
        let Tracked(read)=self.observe_storage(&storage,Tracked(&cause));
        let Some(mut cell)=storage.live.take() else {
            guard.release_write(storage);
            let result=Err(Failure {error:RestoreError::Closed,current:Ghost(None)});
            let tracked trace=attempt::Attempt {read,write:None,inverse:*self,result};
            proof {trace.representation();trace.establish();}
            return (result,Tracked(trace));
        };
        let (result,Tracked(write))=self.restore_live(&mut cell,Tracked(&read));
        storage.live=Some(cell);guard.release_write(storage);
        let tracked trace=attempt::Attempt {read,write,inverse:*self,result};
        proof {trace.representation();trace.establish();}
        (result,Tracked(trace))
    }
    /// Restore the already observed live cell while its actual write guard is
    /// held. The outer method owns locking and attaches the read/issue evidence.
    fn restore_live(&self,cell:&mut Cell<T>,Tracked(read):Tracked<&attempt::Read<T>>)
        ->(out:LiveResult<T>)
        requires self.wf(),old(cell).belongs(self.owner()),read.wf(),read.owner()==self.owner(),
            read.value().is_some(),read.value().unwrap().state()==old(cell).state(),
            read.value().unwrap().history==old(cell).value.history(),
            read.value().unwrap().states==old(cell).authority@.events(),
            read.value().unwrap().revision==old(cell).value.revision_spec(),
            read.value().unwrap().commit.events()==old(cell).member.events(),
        ensures final(cell).belongs(self.owner()),out.1@.is_some()==out.0.is_ok(),
            out.0.is_ok() ==> out.0->Ok_0.wf() && out.0->Ok_0.before().owner==self.owner()
                && Some(out.0->Ok_0.before())==read.value()
                && out.0->Ok_0.before().state()==self.after().state() && out.0->Ok_0.after().state()==self.before().state()
                && out.0->Ok_0.before().revision>=self.after().revision
                && out.1@.unwrap().wf() && out.1@.unwrap().same(&out.0->Ok_0.after().commit)
                && out.1@.unwrap().follows(&read.checkpoint()),
            out.0.is_err() ==> out.0->Err_0.wf(self) && out.0->Err_0.error_spec()==RestoreError::Interference
                && out.0->Err_0.observation()==read.value() && *final(cell)==*old(cell),
    {
        proof {cell.authority.borrow().extends(self.witness.borrow());}
        let before=Ghost(read.value().unwrap());
        if cell.head!=self.expected {
            let result=Err(Failure {error:RestoreError::Interference,current:Ghost(Some(before@))});
            return (result,Tracked(None));
        }
        proof {
            assert(cell.authority@.events()[self.expected as int]==self.after().state());
            assert(cell.state()==self.after().state());
            assert(self.before().states[self.head as int]==self.before().state());
            assert(self.after().states[self.head as int]==self.before().state());
            assert(cell.authority@.events()[self.head as int]==self.after().states[self.head as int]);
            assert(cell.depth>0);
        }
        let tracked checkpoint=read.receipt();
        let (previous,_pending)=cell.advance(&self.owner,self.previous.clone(),self.head,self.depth,Ghost((joint::Change::PayloadRestore,false)),Tracked(Some(checkpoint)));
        let after=cell.evidence(&self.owner);let tracked write=cell.member.receipt();
        let result=Ok(Restored {replacement:Replacement {previous,before,after}});
        (result,Tracked(Some(write)))
    }


}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum RestoreError {Closed,Interference}
#[allow(dead_code)]
pub struct Failure<T:?Sized> {pub error:RestoreError,current:Ghost<Option<Observation<T>>>}
impl<T:?Sized> Failure<T> {
    pub closed spec fn error_spec(&self)->RestoreError {self.error}
    pub fn error(&self)->(out:RestoreError) ensures out==self.error_spec(), {self.error}
    pub closed spec fn observation(&self)->Option<Observation<T>> {self.current@}
    pub open spec fn wf(&self,inverse:&Inverse<T>)->bool {
        match self.observation() {None=>self.error_spec()==RestoreError::Closed,Some(current)=>
            self.error_spec()==RestoreError::Interference && current.wf() && current.owner==inverse.owner()
                && current.state()!=inverse.after().state() && current.revision>=inverse.after().revision}
    }
}
pub struct Restored<T:?Sized> {replacement:Replacement<T>}
impl<T:?Sized> Restored<T> {
    pub closed spec fn before(&self)->Observation<T> {self.replacement.before()}
    pub closed spec fn after(&self)->Observation<T> {self.replacement.after()}
    pub closed spec fn wf(&self)->bool {self.replacement.wf() && self.after().commit.event().change==joint::Change::PayloadRestore}
    pub fn into_displaced(self)->(out:Arc<T>) requires self.wf(),ensures out==self.before().value, {self.replacement.into_previous()}
}
pub struct Applied<T:?Sized> {pub inverse:Inverse<T>,pub pending:Tracked<Option<joint::Pending>>}
impl<T:?Sized> Applied<T> {
    pub open spec fn wf(&self,managed:bool)->bool {self.inverse.wf()
        && joint::pending_matches(self.pending@,self.inverse.owner().journal_spec(),self.inverse.owner().key(),self.inverse.after().commit.at(),managed)}
}
/// Rejection observations come from the same locked storage as the guard.
/// Capacity is an implementation reserve boundary; it is not a paper operation.
pub ghost enum ForwardRejection<T:?Sized> {
    Capacity {owner:SharedPayload<T>,observed:Observation<T>},
    Closed {owner:SharedPayload<T>,terminal:joint::Receipt},
}
impl<T:?Sized> ForwardRejection<T> {
    pub open spec fn owner(&self)->SharedPayload<T> {match self {Self::Capacity {owner,..}|Self::Closed {owner,..}=>*owner}}
    pub open spec fn explains(&self,error:ReplaceError)->bool {
        match self {
            Self::Capacity {owner,observed}=>error==ReplaceError::Capacity && observed.wf() && observed.owner==*owner
                && observed.revision as int+observed.state().depth as int+2>u64::MAX,
            Self::Closed {owner,terminal}=>error==ReplaceError::Closed && owner.receipt_matches(*terminal) && terminal.event().after is RetiredPayload,
        }
    }
}
impl<T:?Sized> SharedPayload<T> {
    pub fn apply(&self,value:Arc<T>)->(out:Result<Applied<T>,Rejected<Arc<T>>>)
        ensures out.is_ok() ==> out->Ok_0.wf(false) && out->Ok_0.inverse.owner()==*self && out->Ok_0.inverse.after().value==value,
            out.is_err() ==> out->Err_0.value==value && (out->Err_0.error==ReplaceError::Capacity || out->Err_0.error==ReplaceError::Closed),
    {self.apply_managed(value,Ghost(false))}
    pub(crate) fn apply_managed(&self,value:Arc<T>,Ghost(managed):Ghost<bool>)->(out:Result<Applied<T>,Rejected<Arc<T>>>)
        ensures out.is_ok() ==> out->Ok_0.wf(managed) && out->Ok_0.inverse.owner()==*self && out->Ok_0.inverse.after().value==value,
            out.is_err() ==> out->Err_0.value==value && (out->Err_0.error==ReplaceError::Capacity || out->Err_0.error==ReplaceError::Closed),
    {let tracked empty=Map::tracked_empty();self.apply_managed_following(value,Ghost(managed),Tracked(&empty)).0}
    pub(crate) fn apply_managed_following(&self,value:Arc<T>,Ghost(managed):Ghost<bool>,Tracked(causes):Tracked<&super::super::registration::ReceiptMap>)->(out:ApplyResult<T>)
        requires super::super::registration::witnesses(*causes),
        ensures out.0.is_err() ==> out.1@.is_some() && out.1@.unwrap().owner()==*self && out.1@.unwrap().explains(out.0->Err_0.error),
            out.0.is_ok() ==> forall|k:(int,bool)|causes.contains_key(k) && #[trigger] causes[k].journal()==self.journal_spec() ==> out.0->Ok_0.inverse.after().commit.follows(&causes[k]),
            out.0.is_ok() ==> out.0->Ok_0.wf(managed) && out.0->Ok_0.inverse.owner()==*self && out.0->Ok_0.inverse.after().value==value,
            out.0.is_err() ==> out.0->Err_0.value==value && (out.0->Err_0.error==ReplaceError::Capacity || out.0->Err_0.error==ReplaceError::Closed),
    {
        let (mut storage,guard)=self.inner.acquire_write();
        let Some(mut cell)=storage.live.take() else {
            let ghost rejection=ForwardRejection::Closed {owner:*self,terminal:storage.retired@.unwrap()};
            guard.release_write(storage);return (Err(Rejected {error:ReplaceError::Closed,value}),Ghost(Some(rejection)));
        };
        let revision=cell.value.revision();
        // Subtraction avoids overflowing the guard itself. One revision for
        // this write and one for its inverse, in addition to existing debt.
        if u64::MAX-revision<2 || cell.depth>u64::MAX-revision-2 {
            let _observed=cell.evidence(self);let ghost rejection=ForwardRejection::Capacity {owner:*self,observed:_observed@};
            storage.live=Some(cell);guard.release_write(storage);return (Err(Rejected {error:ReplaceError::Capacity,value}),Ghost(Some(rejection)));
        }
        let before=cell.evidence(self);let head=cell.head;let depth=cell.depth;
        let journal=cell.member.domain();let Tracked(cause)=journal.join_receipts::<(int,bool)>(Tracked(causes),Tracked(None));
        let (previous,pending)=cell.advance(self,value,revision+1,depth+1,Ghost((joint::Change::PayloadApply,managed)),Tracked(cause));
        let after=cell.evidence(self);
        proof {assert forall|k:(int,bool)|causes.contains_key(k) && #[trigger] causes[k].journal()==self.journal_spec() implies after@.commit.follows(&causes[k]) by {
            after@.commit.after_cover(&cause.unwrap(),&causes[k]);
        }}
        let tracked origin=cell.member.receipt();let tracked witness=cell.authority.borrow().snapshot();
        let journal=cell.member.domain();
        storage.live=Some(cell);guard.release_write(storage);
        (Ok(Applied {inverse:Inverse {owner:self.clone(),journal,previous,head,depth,expected:revision+1,before,after,origin:Tracked(origin),witness:Tracked(witness)},pending}),Ghost(None))
    }
}
/// The revision allocated by the real owner is an explicit operation argument.
/// This is a law over the entire typed semantic carrier, not a one-point
/// specification containing only the observed before/after pair.
pub open spec fn operation<T:?Sized>(value:Arc<T>,head:u64)->crate::mediated::Operation<State<T>,()> {
    |input:State<T>| if input.depth==u64::MAX || head<=input.head {None} else {
        let after=State {value,head,depth:(input.depth+1) as u64};
        Some(crate::mediated::ValueYield {value:after,outcome:(),undo:|current:State<T>|if current==after {Some(input)} else {None}})
    }
}
pub proof fn primitive_law<T:?Sized>(value:Arc<T>,head:u64)
    ensures crate::mediated::operation_admissible(|a:State<T>,b:State<T>|a==b,operation(value,head)),
{ }
impl<T:?Sized> Inverse<T> {
    pub proof fn interpretation(&self)
        requires self.wf(),
        ensures operation(self.after().value,self.after().state().head)(self.before().state()).is_some(),
            operation(self.after().value,self.after().state().head)(self.before().state()).unwrap().value==self.after().state(),
            forall|current:State<T>| #[trigger] self.undo(current)==(operation(self.after().value,self.after().state().head)(self.before().state()).unwrap().undo)(current),
    {primitive_law(self.after().value,self.after().state().head);}
}
pub open spec fn chain<T:?Sized>(owner:SharedPayload<T>,initial:State<T>,stack:Seq<Inverse<T>>,last:State<T>)->bool {
    &&& if stack.len()==0 {last==initial} else {stack.first().before().state()==initial && stack.last().after().state()==last}
    &&& forall|i:int|0<=i<stack.len() ==> #[trigger] stack[i].wf() && stack[i].owner()==owner
    &&& forall|i:int|0<=i<stack.len()-1 ==> #[trigger] stack[i].after().state()==stack[i+1].before().state()
}
pub open spec fn reverse<T:?Sized>(stack:Seq<Inverse<T>>,state:State<T>)->Option<State<T>>
    decreases stack.len(),
{
    if stack.len()==0 {Some(state)} else {
        match stack.last().undo(state) {Some(previous)=>reverse(stack.drop_last(),previous),None=>None}
    }
}
/// A composing actual inverse stack restores its input; success of each
/// inverse is derived. Interfering writes and eventual scheduling remain
/// separate conditions, as in the existing scalar execution theorem.
pub proof fn roundtrip<T:?Sized>(owner:SharedPayload<T>,initial:State<T>,stack:Seq<Inverse<T>>,last:State<T>)
    requires chain(owner,initial,stack,last),
    ensures reverse(stack,last)==Some(initial),
    decreases stack.len(),
{
    if stack.len()>0 {
        let prefix=stack.drop_last();let before=stack.last().before().state();
        assert(chain(owner,initial,prefix,before));roundtrip(owner,initial,prefix,before);
    }
}

}

#[path = "payload_attempt.rs"]
pub mod attempt;
