//! Actual typed service slots. Replacing a slot changes its current object;
//! captured values, programs and inverses retain the original allocation.
//! Non-scalar storage is supplied separately; the production host uses the
//! checked shared payload owner, without adding user code to this scalar lock.
use super::history::{Authority, Witness};
use super::joint;
use super::{ReversibleValue, Snapshot};
use crate::lifecycle_state::services::{NativeEpisode, NativeReadError};
use crate::versioned_value::{Rejected, VersionedValue};
use crate::Port;
use std::sync::Arc;
use vstd::prelude::*;
use vstd::resource::Loc;
use vstd::rwlock::{RwLock, RwLockPredicate};

verus! {
#[allow(dead_code)]
struct Cell {value:VersionedValue<Arc<ReversibleValue>>,authority:Tracked<Authority<Arc<ReversibleValue>>>,joint:joint::Member}
impl Cell {
    spec fn wf(&self)->bool {self.value.wf() && self.authority@.wf() && self.authority@.events()==self.value.history() && self.joint.wf()
        && self.joint.record()==(joint::Record::Slot {source:self.authority@.source(),revision:self.value.revision_spec(),object:self.value.value().object()})}
    fn capture(&self,slot:&Slot)->(out:Capture)
        requires self.wf(),self.authority@.source()==slot.source(),self.value.history().first()==slot.initial(),self.joint.journal()==slot.journal_spec(),self.joint.key()==slot.key(),
        ensures out.wf(),out.slot()==*slot,out.revision_spec()==self.value.revision_spec(),
            out.value_spec()==self.value.value(),out.history()==self.value.history(),
            out.commit().events()==self.joint.events(),
    {
        proof {self.value.representation();}
        let (revision,value)=self.value.observe();
        let tracked witness=self.authority.borrow().snapshot();
        let tracked commit=self.joint.receipt();
        Capture {slot:slot.clone(),revision,value:value.clone(),witness:Tracked(witness),commit:Tracked(commit)}
    }
}
#[allow(dead_code)]
struct Predicate {source:Loc,initial:Arc<ReversibleValue>,journal:joint::Journal,key:nat}
impl RwLockPredicate<Cell> for Predicate {
    closed spec fn inv(self,cell:Cell)->bool {cell.wf() && cell.authority@.source()==self.source && cell.value.history().first()==self.initial && cell.joint.journal()==self.journal && cell.joint.key()==self.key}
}
pub struct Slot {inner:Arc<RwLock<Cell,Predicate>>}
impl Clone for Slot {
    fn clone(&self)->(out:Self) ensures out==*self, {Self {inner:self.inner.clone()}}
}
impl Slot {
    pub closed spec fn source(&self)->Loc {self.inner.pred().source}
    pub closed spec fn initial(&self)->Arc<ReversibleValue> {self.inner.pred().initial}
    pub closed spec fn journal_spec(&self)->joint::Journal {self.inner.pred().journal}
    pub closed spec fn key(&self)->nat {self.inner.pred().key}
    pub open spec fn receipt_matches(&self,receipt:joint::Receipt)->bool {
        receipt.wf() && receipt.journal()==self.journal_spec() && receipt.event().key==self.key()
            && receipt.event().after is Slot && receipt.event().after->Slot_source==self.source()
    }
    pub open spec fn observed_state(&self,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {
        self.journal_spec()==journal ==> state.contains_key(self.key()) && state[self.key()] is Slot
            && state[self.key()]->Slot_source==self.source()
            && joint::references::present(state,state[self.key()]->Slot_object,journal.source())
    }
    /// Collect under the slot lock, before acquiring a Journal read epoch.
    /// The returned evidence is erased and retains no executable payload.
    pub(crate) fn receipt(&self)->(out:Tracked<joint::Receipt>)
        ensures self.receipt_matches(out@),
    {
        let guard=self.inner.acquire_read();let _cell=guard.borrow();
        let tracked receipt=_cell.joint.receipt();
        guard.release_read();Tracked(receipt)
    }
    pub fn new(value:Arc<ReversibleValue>)->(out:Self)
        ensures out.initial()==value,
    {
        let tracked mut authority=Authority::new();
        proof {authority.append(value);}
        let ghost source=authority.source();
        let (journal,Tracked(target))=value.reference();
        let joint=journal.allocate_referencing(Ghost(joint::Record::Slot {source,revision:0,object:value.object()}),Tracked(Some(target)));
        let ghost key=joint.key();
        let cell=Cell {value:VersionedValue::new(value),authority:Tracked(authority),joint};
        Self {inner:Arc::new(RwLock::new(cell,Ghost(Predicate {source,initial:value,journal,key})))}
    }
    fn domain(&self)->(out:joint::Journal)
        ensures out==self.journal_spec(),
    {let guard=self.inner.acquire_read();let out=guard.borrow().joint.domain();guard.release_read();out}
    pub fn capture(&self)->(out:Capture)
        ensures out.wf(),out.slot()==*self,
    {
        let guard=self.inner.acquire_read();let out=guard.borrow().capture(self);guard.release_read();out
    }
    /// Both observations come from the same real swap under the slot lock.
    /// The previous object is returned intact, not retargeted to the new one.
    pub fn replace(&self,value:Arc<ReversibleValue>)->(out:Result<Replacement,Rejected<Arc<ReversibleValue>>>)
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.previous().slot()==*self
            && out->Ok_0.current().value_spec()==value,
            out.is_err() ==> out->Err_0.value==value && out->Err_0.error==crate::versioned_value::ReplaceError::Capacity,
    {
        let (_domain,Tracked(target))=value.reference();
        let (mut cell,guard)=self.inner.acquire_write();
        let previous=cell.capture(self);
        match cell.value.replace(value) {
            Ok(_old)=>{
                proof {cell.authority.borrow_mut().append(value);reveal(joint::changes);}
                let _pending=cell.joint.update_following(Ghost(joint::Record::Slot {source:self.source(),revision:cell.value.revision_spec(),object:value.object()}),
                    Ghost(joint::Change::Replace),Tracked(Some(target)),Ghost(false),Tracked(None));
                let current=cell.capture(self);
                proof {assert(current.history().take(previous.history().len() as int) =~= previous.history());}
                guard.release_write(cell);
                Ok(Replacement {previous,current})
            },
            Err(error)=>{guard.release_write(cell);Err(error)},
        }
    }
}

/// A private, immutable selection of an actual slot version and object. It
/// owns its slot reference, so refresh cannot substitute a different source.
#[allow(dead_code)]
pub struct Capture {slot:Slot,revision:u64,value:Arc<ReversibleValue>,witness:Tracked<Witness<Arc<ReversibleValue>>>,commit:Tracked<joint::Receipt>}
impl Capture {
    pub closed spec fn slot(&self)->Slot {self.slot}
    pub closed spec fn revision_spec(&self)->u64 {self.revision}
    pub closed spec fn value_spec(&self)->Arc<ReversibleValue> {self.value}
    pub closed spec fn history(&self)->Seq<Arc<ReversibleValue>> {self.witness@.events()}
    pub open spec fn object(&self)->Loc {self.value_spec().source()}
    pub closed spec fn commit(&self)->joint::Receipt {self.commit@}
    pub closed spec fn wf(&self)->bool {
        self.witness@.wf() && self.witness@.source()==self.slot.source()
            && self.history().len()==self.revision_spec() as nat+1 && self.history().last()==self.value_spec() && self.history().first()==self.slot().initial()
            && self.slot().receipt_matches(self.commit())
            && self.commit().event().after==(joint::Record::Slot {source:self.slot().source(),revision:self.revision_spec(),object:self.value_spec().object()})
    }
    pub open spec fn extends(&self,earlier:&Self)->bool {
        self.slot()==earlier.slot() && earlier.revision_spec()<=self.revision_spec()
            && self.history().take(earlier.history().len() as int)==earlier.history()
    }
    /// Erased causal evidence for the selection actually retained by this call.
    pub fn selection_receipt(&self)->(out:Tracked<joint::Receipt>)
        requires self.wf(),ensures out@.wf(),out@.same(&self.commit()),
    {let tracked receipt=self.commit.borrow().duplicate();Tracked(receipt)}
    pub fn value(&self)->(out:&Arc<ReversibleValue>) ensures *out==self.value_spec(), {&self.value}
    pub fn revision(&self)->(out:u64) ensures out==self.revision_spec(), {self.revision}
    pub fn observe_value(&self)->(out:Snapshot)
        requires self.wf(),
        ensures out.certified(),out.source()==self.object(),out.initial()==self.value_spec().initial(),
            out.object()==self.value_spec().object(),out.journal_spec()==self.value_spec().journal_spec(),
            self.commit().journal()==out.journal_spec() ==> self.commit().events().len()<=out.joint_spec().events().len()
                && out.joint_spec().events().take(self.commit().events().len() as int)==self.commit().events(),
    {self.value.snapshot_following(Tracked(self.commit.borrow()))}
    /// Include this exact selection in an authentic shared execution prefix.
    /// Later replacements may change the current slot, never this selection.
    pub fn execution_snapshot(&self)->(out:joint::Snapshot)
        requires self.wf(),
        ensures out.certified(),out.journal_spec()==self.slot().journal_spec(),
            self.commit().events().len()<=out.events().len(),out.events().take(self.commit().events().len() as int)==self.commit().events(),
            out.events()[self.commit().at() as int].event.after==(joint::Record::Slot {
                source:self.slot().source(),revision:self.revision_spec(),object:self.value_spec().object()}),
            self.slot().observed_state(out.journal_spec(),out.last()),
            self.value_spec().object().domain==out.domain() ==> out.resolve(self.value_spec().object()).is_some(),
    {
        #[allow(unused_mut)] // Only the erased receipt collection changes.
        let mut evidence=Evidence::new();
        proof {evidence.receipts.borrow_mut().tracked_insert(self.slot(),self.commit.borrow().duplicate());}
        // A replacement can point to a foreign object, so use the slot owner.
        let slot_domain=self.slot.domain();let view=slot_domain.read();
        evidence.certify(&view);let snapshot=view.finish();
        proof {snapshot.retained_reference(self.commit());}
        snapshot
    }
    pub fn refresh(&self)->(out:Self)
        requires self.wf(),
        ensures out.wf(),out.extends(self),out.history()[self.revision_spec() as int]==self.value_spec(),
    {
        let guard=self.slot.inner.acquire_read();let cell=guard.borrow();
        proof {cell.authority.borrow().extends(self.witness.borrow());cell.value.representation();}
        let out=cell.capture(&self.slot);
        guard.release_read();out
    }
    /// A real callback result is accepted only while this captured revision
    /// remains current. No separately supplied slot or version is trusted.
    pub fn check_result(&self,result:bool)->(out:Check)
        requires self.wf(),
        ensures out.current().wf(),out.current().extends(self),
            out.accepted_spec()==(result && out.current().revision_spec()==self.revision_spec()),
    {
        let current=self.refresh();
        let accepted=result && current.revision==self.revision;
        Check {accepted,current}
    }
    pub proof fn retained_object(&self,later:&Self)
        requires self.wf(),later.wf(),later.extends(self),
        ensures later.history()[self.revision_spec() as int]==self.value_spec(),
            later.history()[self.revision_spec() as int].source()==self.object(),
    { }
}
/// A slot entry keeps its source and monotonically increasing revision through
/// every intervening global event, including changes to unrelated owners.
pub proof fn retained(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat)
    requires joint::valid(frames),start<=end<=frames.len(),joint::state_at(frames,start).contains_key(key),joint::state_at(frames,start)[key] is Slot,
    ensures joint::state_at(frames,end).contains_key(key),joint::state_at(frames,end)[key] is Slot,
        joint::state_at(frames,end)[key]->Slot_source==joint::state_at(frames,start)[key]->Slot_source,
        joint::state_at(frames,start)[key]->Slot_revision<=joint::state_at(frames,end)[key]->Slot_revision,
    decreases end-start,
{
    if start<end {
        retained(frames,start,(end-1) as nat,key);
        assert(joint::step(joint::state_at(frames,(end-1) as nat),frames[end-1].state,frames[end-1].event));
        if frames[end-1].event.key==key {reveal(joint::changes);}
    }
}
/// Erased certificates collected from actual service maps before the shared
/// read epoch. Repeated aliases share a key; opaque values are not enumerated.
#[allow(dead_code)]
pub(crate) struct Evidence {receipts:Tracked<Map<Slot,joint::Receipt>>}
impl Evidence {
    pub closed spec fn receipts(&self)->Map<Slot,joint::Receipt> {self.receipts@}
    pub closed spec fn contains(&self,slot:Slot)->bool {self.receipts@.contains_key(slot)}
    pub closed spec fn wf(&self)->bool {forall|s:Slot| self.receipts@.contains_key(s) ==> s.receipt_matches(#[trigger] self.receipts@[s])}
    pub(crate) fn new()->(out:Self)
        ensures out.wf(),forall|s:Slot| !out.contains(s),
    {Self {receipts:Tracked(Map::tracked_empty())}}
    pub(crate) fn add(&mut self,slot:&Slot)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).contains(*slot),forall|s:Slot| old(self).contains(s) ==> final(self).contains(s),
    {
        let Tracked(receipt)=slot.receipt();
        proof {self.receipts.borrow_mut().tracked_insert(*slot,receipt);}
    }
    pub(crate) fn certify(&self,view:&joint::ReadView)
        requires self.wf(),view.wf(),
        ensures forall|s:Slot| self.contains(s) ==> #[trigger] s.observed_state(view.journal_spec(),view.state()),
            forall|s:Slot| self.contains(s) && s.journal_spec()==view.journal_spec() ==>
                self.receipts()[s].events().len()<=view.events().len()
                    && view.events().take(self.receipts()[s].events().len() as int)==self.receipts()[s].events(),
    {
        view.certify_receipts::<Slot>(Tracked(self.receipts.borrow()));view.valid_history();
        proof {
            joint::references::at(view.events(),view.events().len(),view.journal_spec().source());
            assert forall|s:Slot| self.contains(s) implies #[trigger] s.observed_state(view.journal_spec(),view.state()) by {
                if s.journal_spec()==view.journal_spec() {
                    let receipt=self.receipts@[s];let at=receipt.at();
                    assert(view.events()[at as int]==receipt.events()[at as int]);
                    assert(joint::step(joint::state_at(view.events(),at),view.events()[at as int].state,view.events()[at as int].event));
                    retained(view.events(),at+1,view.events().len(),s.key());
                }
            }
        }
    }
}
pub struct Check {accepted:bool,current:Capture}
impl Check {
    pub closed spec fn accepted_spec(&self)->bool {self.accepted}
    pub closed spec fn current(&self)->Capture {self.current}
    pub fn observation(&self)->(out:&Capture) ensures *out==self.current(), {&self.current}
    pub fn accepted(&self)->(out:bool) ensures out==self.accepted_spec(), {self.accepted}
}
pub struct Replacement {previous:Capture,current:Capture}
impl Replacement {
    pub closed spec fn previous(&self)->Capture {self.previous}
    pub closed spec fn current(&self)->Capture {self.current}
    pub open spec fn wf(&self)->bool {
        self.previous().wf() && self.current().wf() && self.current().extends(&self.previous())
            && self.current().revision_spec()==self.previous().revision_spec()+1
            && self.current().history()==self.previous().history().push(self.current().value_spec())
            && self.current().commit().event().change==joint::Change::Replace
            && self.current().commit().follows(&self.previous().commit())
    }
    /// The authentic swap is a resolution transition, never an object write.
    pub proof fn production_aliases<K,T,M>(&self,values:Map<K,Arc<ServiceSlot<T,M>>>)
        requires self.wf(),
        ensures {
            let receipt=self.current().commit();let before=joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
            &&& super::access::objects(after)==super::access::objects(before)
            &&& forall|key:K| values.contains_key(key) && (values[key].managed().is_none()
                || values[key].managed().unwrap().journal_spec()!=receipt.journal() || values[key].managed().unwrap().key()!=receipt.event().key) ==>
                #[trigger] crate::lifecycle_state::services::slots::projection(values,receipt.journal(),after)[key]==
                    crate::lifecycle_state::services::slots::projection(values,receipt.journal(),before)[key]
        },
    {
        let receipt=self.current().commit();
        super::alias::production_replace(values,receipt.journal(),joint::state_at(receipt.events(),receipt.at()),receipt.events().last().state,receipt.event());
    }
    pub fn observations(&self)->(out:(&Capture,&Capture)) ensures *out.0==self.previous(),*out.1==self.current(), {(&self.previous,&self.current)}
    pub fn into_previous(self)->(out:Arc<ReversibleValue>) ensures out==self.previous().value_spec(), {self.previous.value}
}

/// The native registry stores this actual sum, not an auxiliary identity map.
/// Metadata and opaque payloads stay outside the scalar slot lock.
enum Payload<T> {Opaque(T),Reversible(Slot)}
pub struct ServiceSlot<T,M> {payload:Payload<T>,metadata:M}
impl<T,M> ServiceSlot<T,M> {
    pub closed spec fn managed(&self)->Option<Slot> {match self.payload {Payload::Reversible(slot)=>Some(slot),_=>None}}
    pub closed spec fn opaque_spec(&self)->Option<T> {match self.payload {Payload::Opaque(value)=>Some(value),_=>None}}
    pub proof fn payload_partition(&self)
        ensures self.opaque_spec().is_some()!=self.managed().is_some(),
    {}
    pub fn new_opaque(value:T,metadata:M)->(out:Self) ensures out.managed().is_none(),out.opaque_spec()==Some(value), {Self {payload:Payload::Opaque(value),metadata}}
    pub fn new_reversible(value:Arc<ReversibleValue>,metadata:M)->(out:Self)
        ensures out.managed().is_some(),out.managed().unwrap().initial()==value,
    {
        Self {payload:Payload::Reversible(Slot::new(value)),metadata}
    }
    pub fn metadata(&self)->&M {&self.metadata}
    pub fn opaque(&self)->(out:Option<&T>)
        ensures out.is_some()==self.opaque_spec().is_some(),out.is_some() ==> *out.unwrap()==self.opaque_spec().unwrap(),
    {match &self.payload {Payload::Opaque(value)=>Some(value),_=>None}}
    pub fn reversible(&self)->(out:Option<&Slot>)
        ensures out.is_some()==self.managed().is_some(),out.is_some() ==> *out.unwrap()==self.managed().unwrap(),
    {match &self.payload {Payload::Reversible(slot)=>Some(slot),_=>None}}
    pub fn capture_binding(&self,provider:usize,port:Port)->(out:Option<ServiceBinding>)
        ensures out.is_some()==self.managed().is_some(),
            out.is_some() ==> out.unwrap().wf() && out.unwrap().provider_spec()==provider && out.unwrap().port_spec()==port
                && Some(out.unwrap().capture_spec().slot())==self.managed(),
    {
        let slot=self.reversible()?;
        Some(ServiceBinding {provider,port,capture:slot.capture()})
    }
}

pub struct ServiceBinding {provider:usize,port:Port,capture:Capture}
impl ServiceBinding {
    pub closed spec fn provider_spec(&self)->usize {self.provider}
    pub closed spec fn port_spec(&self)->Port {self.port}
    pub closed spec fn capture_spec(&self)->Capture {self.capture}
    pub open spec fn wf(&self)->bool {self.capture_spec().wf()}
    pub fn provider(&self)->(out:usize) ensures out==self.provider_spec(), {self.provider}
    pub fn port(&self)->(out:Port) ensures out==self.port_spec(), {self.port}
    pub fn capture(&self)->(out:&Capture) ensures *out==self.capture_spec(), {&self.capture}
    pub fn value(&self)->(out:&Arc<ReversibleValue>) ensures *out==self.capture_spec().value_spec(), {self.capture.value()}
}
#[derive(Debug)]
pub enum ReadError {Native(NativeReadError),NotReversible {provider:usize}}
impl<T,M> NativeEpisode<ServiceSlot<T,M>> {
    pub open spec fn selects_slot(&self,provider:usize,port:Port,slot:Slot)->bool {
        if self.provisions().contains(port) {
            provider==self.origin().id && self.owned().contains_key((port.key,port.realm))
                && self.owned()[(port.key,port.realm)].managed()==Some(slot)
        } else {
            self.bindings().contains(crate::Binding {provider,key:port.key,realm:port.realm})
                && self.capture().imports.contains_key((provider,port.key,port.realm))
                && self.capture().imports[(provider,port.key,port.realm)].managed()==Some(slot)
        }
    }
    /// Read from the actual episode-committed provider, then capture the actual
    /// slot. No caller supplies a provider, object identity or expected version.
    pub open spec fn reversible_read_failed(&self,port:Port,error:ReadError)->bool {
        match error {
            ReadError::Native(error)=>self.read_failed(port,error),
            ReadError::NotReversible {provider}=>!self.closed() && if self.provisions().contains(port) {
                provider==self.origin().id && self.owned().contains_key((port.key,port.realm)) && self.owned()[(port.key,port.realm)].managed().is_none()
            } else {self.bindings().contains(crate::Binding {provider,key:port.key,realm:port.realm})
                && self.imports().contains_key((provider,port.key,port.realm)) && self.imports()[(provider,port.key,port.realm)].managed().is_none()},
        }
    }
    pub fn read_reversible(&self,port:Port)->(out:Result<ServiceBinding,ReadError>)
        requires self.wf(),
        ensures out.is_err() ==> self.reversible_read_failed(port,out->Err_0),
            out.is_ok() ==> !self.closed() && out->Ok_0.wf() && out->Ok_0.port_spec()==port
            && self.selects_slot(out->Ok_0.provider_spec(),port,out->Ok_0.capture_spec().slot()),
            out.is_ok() && !self.provisions().contains(port) ==>
                self.capture().available(out->Ok_0.provider_spec(),port)
                && self.capture().sources[out->Ok_0.provider_spec()].origin.id==out->Ok_0.provider_spec()
                && self.capture().sources[out->Ok_0.provider_spec()].values[(port.key,port.realm)].managed()==Some(out->Ok_0.capture_spec().slot()),
    {
        let (provider,slot)=match self.read(port) {Ok(value)=>value,Err(error)=>return Err(ReadError::Native(error))};
        match slot.capture_binding(provider,port) {Some(binding)=>Ok(binding),None=>{
            assert(exists|value:Arc<ServiceSlot<T,M>>| #[trigger] self.selects_value(provider,port,value) && value.managed().is_none());
            let error=ReadError::NotReversible {provider};
            assert(self.reversible_read_failed(port,error));
            Err(error)
        }}
    }
}
}
