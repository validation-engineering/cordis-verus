//! Shared storage for actual typed host payloads, including unsized trait
//! objects. Payloads, versions and lock ownership are executable; histories and
//! journal correspondence are erased. Interior user state remains explicit.
use super::history::{Authority, Witness};
use super::joint;
#[cfg(verus_keep_ghost)]
use super::joint::payload as p;
use crate::versioned_value::{Rejected, VersionedValue};
use std::sync::Arc;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::rwlock::{RwLock, RwLockPredicate};

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
/// Restorable semantic state. Revision is deliberately outside this carrier:
/// every successful restoration advances the anti-stale version.
pub ghost struct State<T:?Sized> {pub value:Arc<T>,pub head:u64,pub depth:u64}
pub open spec fn values<T:?Sized>(states:Seq<State<T>>)->Seq<Arc<T>> {states.map(|_:int,s:State<T>|s.value)}

#[allow(dead_code)]
struct Cell<T:?Sized> {
    value:VersionedValue<Arc<T>>,head:u64,depth:u64,authority:Tracked<Authority<State<T>>>,
    member:joint::Member,positions:Ghost<Seq<nat>>,
}
impl<T:?Sized> Cell<T> {
    spec fn state(&self)->State<T> {State {value:self.value.value(),head:self.head,depth:self.depth}}
    spec fn wf(&self)->bool {
        self.value.wf() && self.authority@.wf() && values(self.authority@.events())==self.value.history()
            && self.head<=self.value.revision_spec() && self.authority@.events()[self.head as int]==self.state()
            && self.authority@.events().last()==self.state() && self.value.revision_spec() as int+self.depth as int<=u64::MAX
            && self.member.wf() && self.member.record()==(joint::Record::Payload {source:self.authority@.source(),revision:self.value.revision_spec()})
            && p::indexed(self.value.history().len(),self.positions@,self.member.events(),self.member.key(),self.authority@.source())
    }
    spec fn belongs(&self,owner:SharedPayload<T>)->bool {
        self.wf() && self.authority@.source()==owner.source() && self.value.history().first()==owner.initial()
            && self.member.journal()==owner.journal_spec() && self.member.key()==owner.key()
    }
    fn evidence(&self,_owner:&SharedPayload<T>)->(out:Ghost<Observation<T>>)
        requires self.belongs(*_owner),
        ensures out@.wf(),out@.owner==*_owner,out@.value==self.value.value(),out@.revision==self.value.revision_spec(),
            out@.history==self.value.history(),out@.states==self.authority@.events(),out@.state()==self.state(),out@.positions==self.positions@,out@.commit.events()==self.member.events(),
    {
        proof {self.value.representation();}
        let tracked commit=self.member.receipt();
        Ghost(Observation {owner:*_owner,value:self.value.value(),revision:self.value.revision_spec(),history:self.value.history(),states:self.authority@.events(),positions:self.positions@,commit})
    }
    fn capture(&self,owner:&SharedPayload<T>)->(out:Capture<T>)
        requires self.belongs(*owner),
        ensures out.wf(),out.owner()==*owner,out.value_spec()==self.value.value(),out.revision_spec()==self.value.revision_spec(),
            out.observation().history==self.value.history(),out.observation().states==self.authority@.events(),out.observation().commit.events()==self.member.events(),
    {
        let observation=self.evidence(owner);
        let tracked witness=self.authority.borrow().snapshot();
        let (revision,value)=self.value.observe();
        Capture {owner:owner.clone(),revision,value:value.clone(),observation,witness:Tracked(witness)}
    }
}
#[allow(dead_code)]
struct Predicate<T:?Sized> {source:Loc,initial:Arc<T>,journal:joint::Journal,key:nat}
#[allow(dead_code)]
struct Storage<T:?Sized> {live:Option<Cell<T>>,retired:Tracked<Option<joint::Receipt>>}
impl<T:?Sized> RwLockPredicate<Storage<T>> for Predicate<T> {
    closed spec fn inv(self,storage:Storage<T>)->bool {
        match storage.live {
            Some(cell)=>cell.wf() && cell.authority@.source()==self.source && cell.value.history().first()==self.initial
                && cell.member.journal()==self.journal && cell.member.key()==self.key && storage.retired@.is_none(),
            None=>storage.retired@.is_some() && storage.retired@.unwrap().wf()
                && storage.retired@.unwrap().journal()==self.journal && storage.retired@.unwrap().event().key==self.key
                && storage.retired@.unwrap().event().after is RetiredPayload
                && storage.retired@.unwrap().event().after->RetiredPayload_source==self.source,
        }
    }
}
/// Low-level checked owner with explicit retirement. Call `retire` before
/// releasing the last owner; the production Runtime supplies a final-slot
/// release guard. The vstd lock does not automatically destroy stored values.
pub struct SharedPayload<T:?Sized> {inner:Arc<RwLock<Storage<T>,Predicate<T>>>}
impl<T:?Sized> Clone for SharedPayload<T> {
    fn clone(&self)->(out:Self) ensures out==*self, {Self {inner:self.inner.clone()}}
}
impl<T:?Sized> SharedPayload<T> {
    pub closed spec fn source(&self)->Loc {self.inner.pred().source}
    pub closed spec fn initial(&self)->Arc<T> {self.inner.pred().initial}
    pub closed spec fn journal_spec(&self)->joint::Journal {self.inner.pred().journal}
    pub closed spec fn key(&self)->nat {self.inner.pred().key}
    pub open spec fn receipt_matches(&self,receipt:joint::Receipt)->bool {
        receipt.wf() && receipt.journal()==self.journal_spec() && receipt.event().key==self.key()
            && p::present(receipt.event().after) && p::source(receipt.event().after)==self.source()
    }
    pub open spec fn observed_state(&self,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {
        self.journal_spec()==journal ==> state.contains_key(self.key()) && p::present(state[self.key()])
            && p::source(state[self.key()])==self.source()
    }
    /// No arbitrary payload is cloned or dropped while collecting evidence.
    pub(crate) fn receipt(&self)->(out:Tracked<joint::Receipt>)
        ensures self.receipt_matches(out@),
    {
        let guard=self.inner.acquire_read();let _storage=guard.borrow();
        let tracked receipt=match &_storage.live {Some(cell)=>cell.member.receipt(),None=>_storage.retired.borrow().tracked_borrow().duplicate()};
        guard.release_read();Tracked(receipt)
    }
    pub fn new(value:Arc<T>)->(out:Self) ensures out.initial()==value,
    {Self::new_in(&joint::Journal::new(),value)}
    /// The supplied Journal is an actual shared owner, never a numeric domain.
    pub fn new_in(journal:&joint::Journal,value:Arc<T>)->(out:Self)
        ensures out.initial()==value,out.journal_spec()==*journal,
    {
        let tracked mut authority=Authority::new();proof {authority.append(State {value,head:0,depth:0});}
        let ghost source=authority.source();
        let member=journal.allocate(Ghost(joint::Record::Payload {source,revision:0}));
        let ghost key=member.key();let ghost positions=seq![(member.events().len()-1) as nat];
        let cell=Cell {value:VersionedValue::new(value),head:0,depth:0,authority:Tracked(authority),member,positions:Ghost(positions)};
        proof {assert(values(cell.authority@.events()) =~= cell.value.history());assert(cell.wf());}
        Self {inner:Arc::new(RwLock::new(Storage {live:Some(cell),retired:Tracked(None)},Ghost(Predicate {source,initial:value,journal:*journal,key})))}
    }
    pub fn capture(&self)->(out:Option<Capture<T>>)
        ensures out.is_some() ==> out.unwrap().wf() && out.unwrap().owner()==*self,
    {
        let guard=self.inner.acquire_read();
        let out=match &guard.borrow().live {Some(cell)=>Some(cell.capture(self)),None=>None};
        guard.release_read();out
    }
    /// A swap returns only the displaced executable payload. It does not clone
    /// the new payload into an audit object that could drop under a host lock.
    pub fn replace(&self,value:Arc<T>)->(out:Result<Replacement<T>,Rejected<Arc<T>>>)
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.before().owner==*self && out->Ok_0.after().value==value
                && out->Ok_0.after().commit.event().change==joint::Change::PayloadReplace,
            out.is_err() ==> out->Err_0.value==value && (out->Err_0.error==crate::versioned_value::ReplaceError::Capacity || out->Err_0.error==crate::versioned_value::ReplaceError::Closed),
    {
        let (mut storage,guard)=self.inner.acquire_write();
        let Some(mut cell)=storage.live.take() else {
            guard.release_write(storage);return Err(Rejected {error:crate::versioned_value::ReplaceError::Closed,value});
        };
        let before=cell.evidence(self);
        match cell.value.replace(value) {
            Ok(previous)=>{
                cell.head=cell.value.revision();cell.depth=0;
                proof {let state=cell.state();cell.authority.borrow_mut().append(state);
                    assert(values(cell.authority@.events()) =~= cell.value.history());reveal(joint::changes);}
                cell.member.update(Ghost(joint::Record::Payload {source:self.source(),revision:cell.value.revision_spec()}),Ghost(joint::Change::PayloadReplace));
                proof {
                    p::append_indexed(before@.history.len(),before@.positions,before@.commit.events(),cell.member.events(),self.key(),self.source());
                }
                cell.positions=Ghost(before@.positions.push((cell.member.events().len()-1) as nat));
                proof {assert(cell.belongs(*self));}
                let after=cell.evidence(self);storage.live=Some(cell);guard.release_write(storage);
                Ok(Replacement {previous,before,after})
            },
            Err(error)=>{storage.live=Some(cell);guard.release_write(storage);Err(error)},
        }
    }
    /// Retire once and return the executable payload, outside the lock. The
    /// host's final slot destructor calls this checked operation explicitly:
    /// vstd RwLock does not automatically drop the value stored inside it.
    pub fn retire(&self)->(out:Option<Retired<T>>)
        ensures out.is_some() ==> out.unwrap().wf() && out.unwrap().before().owner==*self,
    {
        let (mut storage,guard)=self.inner.acquire_write();
        let Some(mut cell)=storage.live.take() else {guard.release_write(storage);return None;};
        let before=cell.evidence(self);
        proof {reveal(joint::changes);}
        cell.member.update(Ghost(joint::Record::RetiredPayload {source:self.source(),revision:cell.value.revision_spec()}),Ghost(joint::Change::PayloadRetire));
        let tracked commit=cell.member.receipt();
        storage.retired=Tracked(Some(commit.duplicate()));
        guard.release_write(storage);
        let value=cell.value.into_inner();
        Some(Retired {value,before,commit:Tracked(commit)})
    }
    /// A live owner's actual payload and common version share this read epoch.
    pub fn execution_snapshot(&self)->(out:Option<Snapshot<T>>)
        ensures out.is_some() ==> out.unwrap().certified() && out.unwrap().capture_spec().owner()==*self
            && joint::classification::history(out.unwrap().joint_spec().events()),
    {
        let guard=self.inner.acquire_read();
        let out=match &guard.borrow().live {
            Some(cell)=>{
                let capture=cell.capture(self);let joint=cell.member.observe();
                proof {p::extend_indexed(capture.observation().history.len(),capture.observation().positions,cell.member.events(),joint.events(),self.key(),self.source());joint.classify();}
                Some(Snapshot {capture,joint})
            },
            None=>None,
        };
        guard.release_read();out
    }

}

/// Exact typed values are retained only in proof state. The common Journal
/// records their source and revision, not a serialization of arbitrary T.
pub ghost struct Observation<T:?Sized> {
    pub owner:SharedPayload<T>,pub revision:u64,pub value:Arc<T>,
    pub history:Seq<Arc<T>>,pub states:Seq<State<T>>,pub positions:Seq<nat>,pub commit:joint::Receipt,
}
impl<T:?Sized> Observation<T> {
    pub open spec fn state(&self)->State<T> {self.states.last()}
    pub open spec fn wf(&self)->bool {
        self.history.len()==self.revision as nat+1 && self.history.last()==self.value && self.history.first()==self.owner.initial()
            && values(self.states)==self.history && self.state().head<=self.revision && self.states[self.state().head as int]==self.state()
            && self.revision as int+self.state().depth as int<=u64::MAX
            && self.commit.wf() && self.commit.journal()==self.owner.journal_spec()
            && self.commit.event().key==self.owner.key()
            && self.commit.event().after==(joint::Record::Payload {source:self.owner.source(),revision:self.revision})
            && p::indexed(self.history.len(),self.positions,self.commit.events(),self.owner.key(),self.owner.source())
    }
    pub open spec fn extends(&self,earlier:Self)->bool {
        self.owner==earlier.owner && earlier.revision<=self.revision
            && self.history.take(earlier.history.len() as int)==earlier.history
            && self.states.take(earlier.states.len() as int)==earlier.states
    }
}
#[allow(dead_code)]
pub struct Capture<T:?Sized> {
    owner:SharedPayload<T>,revision:u64,value:Arc<T>,observation:Ghost<Observation<T>>,witness:Tracked<Witness<State<T>>>,
}
impl<T:?Sized> Capture<T> {
    pub closed spec fn owner(&self)->SharedPayload<T> {self.owner}
    pub closed spec fn revision_spec(&self)->u64 {self.revision}
    pub closed spec fn value_spec(&self)->Arc<T> {self.value}
    pub closed spec fn observation(&self)->Observation<T> {self.observation@}
    pub closed spec fn wf(&self)->bool {
        self.observation().wf() && self.observation().owner==self.owner() && self.observation().value==self.value_spec()
            && self.observation().revision==self.revision_spec() && self.witness@.wf()
            && self.witness@.source()==self.owner().source() && self.witness@.events()==self.observation().states
    }
    pub fn value(&self)->(out:&Arc<T>) ensures *out==self.value_spec(), {&self.value}
    pub fn revision(&self)->(out:u64) ensures out==self.revision_spec(), {self.revision}
    pub fn refresh(&self)->(out:Option<Self>)
        requires self.wf(),
        ensures out.is_some() ==> out.unwrap().wf() && out.unwrap().observation().extends(self.observation())
            && out.unwrap().observation().history[self.revision_spec() as int]==self.value_spec(),
    {
        let guard=self.owner.inner.acquire_read();
        let out=match &guard.borrow().live {
            Some(cell)=>{
                proof {cell.authority.borrow().extends(self.witness.borrow());cell.value.representation();
                    assert(values(cell.authority@.events()).take(self.observation().history.len() as int) =~= self.observation().history);}
                Some(cell.capture(&self.owner))
            },None=>None,
        };
        guard.release_read();out
    }
    /// The retained owner is reread after the callback. Retirement, like an
    /// intervening replacement, prevents acceptance of an earlier result.
    pub fn check_result(&self,result:bool)->(out:Check<T>)
        requires self.wf(),
        ensures out.current().is_some() ==> out.current().unwrap().wf() && out.current().unwrap().extends(self.observation()),
            out.accepted_spec()==(result && out.current().is_some() && out.current().unwrap().revision==self.revision_spec()),
    {
        let guard=self.owner.inner.acquire_read();
        let out=match &guard.borrow().live {
            Some(cell)=>{
                proof {cell.authority.borrow().extends(self.witness.borrow());cell.value.representation();
                    assert(values(cell.authority@.events()).take(self.observation().history.len() as int) =~= self.observation().history);}
                let _current=cell.evidence(&self.owner);
                let accepted=cell.value.accepts_result(self.revision,result);
                Check {accepted,current:Ghost(Some(_current@))}
            },None=>Check {accepted:false,current:Ghost(None)},
        };
        guard.release_read();out
    }
}
#[allow(dead_code)]
pub struct Check<T:?Sized> {accepted:bool,current:Ghost<Option<Observation<T>>>}
impl<T:?Sized> Check<T> {
    pub closed spec fn accepted_spec(&self)->bool {self.accepted}
    pub closed spec fn current(&self)->Option<Observation<T>> {self.current@}
    pub fn accepted(&self)->(out:bool) ensures out==self.accepted_spec(), {self.accepted}
}
#[allow(dead_code)]
pub struct Retired<T:?Sized> {value:Arc<T>,before:Ghost<Observation<T>>,commit:Tracked<joint::Receipt>}
impl<T:?Sized> Retired<T> {
    pub closed spec fn before(&self)->Observation<T> {self.before@}
    pub closed spec fn commit(&self)->joint::Receipt {self.commit@}
    pub closed spec fn wf(&self)->bool {
        self.before().wf() && self.value==self.before().value && self.commit().wf()
            && self.commit().follows(&self.before().commit) && self.commit().event().key==self.before().owner.key()
            && self.commit().event().change==joint::Change::PayloadRetire
            && self.commit().event().after==(joint::Record::RetiredPayload {source:self.before().owner.source(),revision:self.before().revision})
    }
    pub fn into_value(self)->(out:Arc<T>) requires self.wf(),ensures out==self.before().value, {self.value}
}

#[allow(dead_code)]
pub struct Replacement<T:?Sized> {previous:Arc<T>,before:Ghost<Observation<T>>,after:Ghost<Observation<T>>}
impl<T:?Sized> Replacement<T> {
    pub closed spec fn before(&self)->Observation<T> {self.before@}
    pub closed spec fn after(&self)->Observation<T> {self.after@}
    pub closed spec fn wf(&self)->bool {
        self.before().wf() && self.after().wf() && self.previous==self.before().value
            && self.after().owner==self.before().owner && self.after().revision==self.before().revision+1
            && self.after().history==self.before().history.push(self.after().value)
            && self.after().states==self.before().states.push(self.after().state())
            && self.after().commit.follows(&self.before().commit)
            && joint::payload::mutation(self.after().commit.event().change)
    }
    pub proof fn production_aliases<K,M>(&self,values:Map<K,Arc<super::slot::ServiceSlot<SharedPayload<T>,M>>>)
        requires self.wf(),
        ensures {
            let receipt=self.after().commit;let before=joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
            forall|k:K| values.contains_key(k) && !crate::lifecycle_state::services::payloads::affected(values,receipt.journal(),receipt.event().key).contains(k) ==>
                #[trigger] crate::lifecycle_state::services::payloads::projection(values,receipt.journal(),after)[k]==
                    crate::lifecycle_state::services::payloads::projection(values,receipt.journal(),before)[k]
        },
    {
        let receipt=self.after().commit;
        assert(joint::step(joint::state_at(receipt.events(),receipt.at()),receipt.events().last().state,receipt.event()));
        crate::lifecycle_state::services::payloads::project_replacement(values,receipt.journal(),joint::state_at(receipt.events(),receipt.at()),receipt.events().last().state,receipt.event());
    }
    pub fn into_previous(self)->(out:Arc<T>) requires self.wf(),ensures out==self.before().value, {self.previous}
}
pub struct Snapshot<T:?Sized> {capture:Capture<T>,joint:joint::Snapshot}
impl<T:?Sized> Snapshot<T> {
    pub closed spec fn capture_spec(&self)->Capture<T> {self.capture}
    pub closed spec fn joint_spec(&self)->joint::Snapshot {self.joint}
    pub open spec fn certified(&self)->bool {
        let c=self.capture_spec();
        c.wf() && self.joint_spec().certified() && self.joint_spec().journal_spec()==c.owner().journal_spec()
            && self.joint_spec().last().contains_pair(c.owner().key(),joint::Record::Payload {source:c.owner().source(),revision:c.revision_spec()})
            && p::indexed(c.observation().history.len(),c.observation().positions,self.joint_spec().events(),c.owner().key(),c.owner().source())
    }
    /// Every mutation of this actual typed owner is represented. Unrelated
    /// lifecycle and payload events remain in the same complete execution.
    pub proof fn complete_projection(&self)
        requires self.certified(),
        ensures forall|n:int|0<=n<self.joint_spec().events().len() && #[trigger] self.joint_spec().events()[n].event.key==self.capture_spec().owner().key()
            ==> exists|i:int|0<=i<self.capture_spec().observation().history.len() && self.capture_spec().observation().positions[i]==n,
    {
        let c=self.capture_spec();self.joint.valid_history();
        assert(c.observation().history.len()==c.revision_spec() as nat+1);
        assert((c.observation().history.len()-1) as u64==c.revision_spec());
        p::complete_projection(self.joint_spec().events(),c.observation().positions,c.owner().key(),c.owner().source(),c.observation().history.len());
    }

    pub fn capture(&self)->(out:&Capture<T>) ensures *out==self.capture_spec(), {&self.capture}
    pub fn joint(&self)->(out:&joint::Snapshot) ensures *out==self.joint_spec(), {&self.joint}
}
/// Collect all actual owners before the common read epoch; no payload lock is
/// acquired while the Journal guard is held. Aliases share their real owner.
#[allow(dead_code)]
pub(crate) struct Evidence<T:?Sized> {receipts:Tracked<Map<SharedPayload<T>,joint::Receipt>>}
impl<T:?Sized> Evidence<T> {
    pub closed spec fn contains(&self,owner:SharedPayload<T>)->bool {self.receipts@.contains_key(owner)}
    pub closed spec fn wf(&self)->bool {
        forall|owner:SharedPayload<T>| self.receipts@.contains_key(owner) ==> owner.receipt_matches(#[trigger] self.receipts@[owner])
    }
    pub(crate) fn new()->(out:Self)
        ensures out.wf(),forall|owner:SharedPayload<T>| !out.contains(owner),
    {Self {receipts:Tracked(Map::tracked_empty())}}
    pub(crate) fn add(&mut self,owner:&SharedPayload<T>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).contains(*owner),forall|other:SharedPayload<T>| old(self).contains(other) ==> final(self).contains(other),
    {
        let Tracked(receipt)=owner.receipt();
        proof {self.receipts.borrow_mut().tracked_insert(*owner,receipt);}
    }
    pub(crate) fn certify(&self,view:&joint::ReadView)
        requires self.wf(),view.wf(),
        ensures forall|owner:SharedPayload<T>| self.contains(owner) ==> #[trigger] owner.observed_state(view.journal_spec(),view.state()),
    {
        view.certify_receipts::<SharedPayload<T>>(Tracked(self.receipts.borrow()));view.valid_history();
        proof {
            assert forall|owner:SharedPayload<T>| self.contains(owner) implies #[trigger] owner.observed_state(view.journal_spec(),view.state()) by {
                if owner.journal_spec()==view.journal_spec() {
                    let receipt=self.receipts@[owner];let at=receipt.at();
                    assert(view.events()[at as int]==receipt.events()[at as int]);
                    assert(joint::step(joint::state_at(view.events(),at),view.events()[at as int].state,view.events()[at as int].event));
                    p::retained(view.events(),at+1,view.events().len(),owner.key());
                }
            }
        }
    }
}

}

#[path = "payload_inverse.rs"]
pub mod restoration;
