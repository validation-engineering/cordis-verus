//! The real shared native Child request/inverse, including synchronization.
//! Only scalar lifecycle data lives inside the vstd lock: it has explicit lock
//! release and no automatic payload destructor. Diagnostic strings stay with
//! the host. No user callback runs while the lock is held.
use super::child::{ChildSlot, ChildStatus};
use super::{ChildIdentity, PluginDefinition};
use crate::cleanup_groups::CleanupGroups;
use crate::lifecycle_state::native::NativeHost;
use crate::setup_work::SetupWork;
use crate::{Error, Port};
use std::collections::BTreeMap;
use std::sync::Arc;
use vstd::prelude::*;
use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo};
use vstd::resource::Loc;
use vstd::rwlock::{RwLock, RwLockPredicate};

verus! {

#[derive(Clone, Copy)]
struct ChildOrigin {domain:u64,parent:usize,generation:Option<u64>}
// These private fields carry proof resources erased by Cargo.
#[allow(dead_code)] // Erased proof fields are intentionally unread by Cargo.
struct ChildCell {
    slot:ChildSlot<()>,
    auth:Tracked<GhostMapAuth<(),ChildStatus<()>>>,
    decision:Tracked<Option<GhostPersistentPointsTo<(),ChildStatus<()>>>>,
}
#[allow(dead_code)] // Erased proof fields are intentionally unread by Cargo.
struct ChildPredicate {origin:ChildOrigin,resource:Loc}
impl RwLockPredicate<ChildCell> for ChildPredicate {
    closed spec fn inv(self,cell:ChildCell)->bool {
        cell.wf() && cell.slot.domain_id()==self.origin.domain && cell.slot.owner()==self.origin.parent
            && cell.slot.episode()==self.origin.generation && cell.auth@.id()==self.resource
    }
}
impl ChildCell {
    spec fn recorded(&self)->bool {
        if self.decision@ is Some {
            let d=self.decision@->Some_0;
            &&& d.id()==self.auth@.id() && d.key()==()
            &&& d.value()==self.slot.state() && !(self.slot.state() is Pending)
            &&& self.auth@@==Map::empty().insert((),d.value())
        } else {self.auth@@==Map::empty()}
    }
    spec fn wf(&self)->bool {self.slot.wf() && self.recorded() && (self.decision@.is_none()==(self.slot.state() is Pending))}
    proof fn record(tracked &mut self)
        requires old(self).slot.wf(),old(self).recorded(),
        ensures final(self).wf(),final(self).slot==old(self).slot,final(self).auth@.id()==old(self).auth@.id(),
    {
        if self.decision@.is_none() && !(self.slot.state() is Pending) {
            let tracked token=self.auth.borrow_mut().insert((),self.slot.state()).persist();
            *self.decision.borrow_mut()=Some(token);
        }
    }
    fn new(slot:ChildSlot<()>)->(out:Self)
        requires slot.wf(),
        ensures out.wf(),out.slot==slot,
    {
        let tracked (auth,_empty)=GhostMapAuth::new(Map::empty());
        #[allow(unused_mut)] // The mutation below changes erased proof resources only.
        let mut out=Self {slot,auth:Tracked(auth),decision:Tracked(None)};
        proof {out.record();}
        out
    }
    fn snapshot(&self)->(out:ChildSnapshot)
        requires self.wf(),
        ensures out.wf(),out.state()==self.slot.state(),out.source()==self.auth@.id(),
    {
        let state=match self.slot.identity() {
            Some(child)=>ChildStatus::Assigned(child),
            None=>if self.slot.pending() {ChildStatus::Pending}
                else if self.slot.error().is_some() {ChildStatus::Failed(())} else {ChildStatus::Cancelled},
        };
        let tracked witness=match self.decision.borrow() {Some(token)=>Some(token.duplicate()),None=>None};
        ChildSnapshot {state,source:Ghost(self.auth@.id()),witness:Tracked(witness)}
    }
}

/// A real observation under the lock plus persistent evidence for any terminal
/// assignment. Pending is only a snapshot, never a promise of future admission.
#[allow(dead_code)] // Erased proof fields are intentionally unread by Cargo.
pub struct ChildSnapshot {
    state:ChildStatus<()>,source:Ghost<Loc>,
    witness:Tracked<Option<GhostPersistentPointsTo<(),ChildStatus<()>>>>,
}
impl ChildSnapshot {
    pub closed spec fn state(&self)->ChildStatus<()> {self.state}
    pub closed spec fn source(&self)->Loc {self.source@}
    pub closed spec fn wf(&self)->bool {
        if self.state() is Pending {self.witness@.is_none()} else {
            self.witness@.is_some() && self.witness@->Some_0.id()==self.source()
                && self.witness@->Some_0.key()==() && self.witness@->Some_0.value()==self.state()
        }
    }
    /// Terminal observations of the same shared slot cannot disagree, even
    /// when another thread took the lock between these observations.
    pub proof fn terminal_agrees(tracked &self,tracked other:&Self)
        requires self.wf(),other.wf(),self.source()==other.source(),
            !(self.state() is Pending),!(other.state() is Pending),
        ensures self.state()==other.state(),
    {
        let tracked _ = match (self.witness.borrow(),other.witness.borrow()) {
            (Some(left),Some(right))=>{let tracked mut copy=left.duplicate();copy.intersection_agrees(right);},
            _=>{assert(false);},
        };
    }
    pub fn identity(&self)->(out:Option<ChildIdentity>)
        ensures out==match self.state() {ChildStatus::Assigned(child)=>Some(child),_=>None},
    {match &self.state {ChildStatus::Assigned(child)=>Some(*child),_=>None}}
    pub fn pending(&self)->(out:bool) ensures out==(self.state() is Pending), {matches!(self.state,ChildStatus::Pending)}
    pub fn cancelled(&self)->(out:bool) ensures out==(self.state() is Cancelled), {matches!(self.state,ChildStatus::Cancelled)}
    pub fn failed(&self)->(out:bool) ensures out==(self.state() is Failed), {matches!(self.state,ChildStatus::Failed(_))}
}

pub struct SharedChild {inner:Arc<RwLock<ChildCell,ChildPredicate>>,origin:ChildOrigin}
impl Clone for SharedChild {
    fn clone(&self)->(out:Self)
        ensures out==*self,
    {Self {inner:self.inner.clone(),origin:self.origin}}
}
impl SharedChild {
    pub closed spec fn source(&self)->Loc {self.inner.pred().resource}
    pub closed spec fn domain_id(&self)->u64 {self.origin.domain}
    pub closed spec fn owner(&self)->usize {self.origin.parent}
    pub closed spec fn episode(&self)->Option<u64> {self.origin.generation}
    pub closed spec fn wf(&self)->bool {self.inner.pred().origin==self.origin}
    fn new(slot:ChildSlot<()>,origin:ChildOrigin)->(out:(Self,ChildSnapshot))
        requires slot.wf(),slot.domain_id()==origin.domain,slot.owner()==origin.parent,slot.episode()==origin.generation,
        ensures out.0.wf(),out.0.origin==origin,out.1.wf(),out.1.source()==out.0.source(),out.1.state()==slot.state(),
    {
        let cell=ChildCell::new(slot);
        let snapshot=cell.snapshot();
        let ghost predicate=ChildPredicate {origin,resource:cell.auth@.id()};
        (Self {inner:Arc::new(RwLock::new(cell,Ghost(predicate))),origin},snapshot)
    }
    fn from_work<C,G>(work:&SetupWork<C,G>)->(out:Option<Self>)
        requires work.wf(),
        ensures out.is_some()==work.origin().is_some(),out.is_some() ==> out.unwrap().wf()
            && out.unwrap().domain_id()==work.origin().unwrap().domain && out.unwrap().owner()==work.origin().unwrap().id
            && out.unwrap().episode()==Some(work.origin().unwrap().generation),
    {
        match ChildSlot::from_work(work) {
            Some(slot)=>{let ticket=work.lifecycle_ticket().unwrap();Some(Self::new(slot,ChildOrigin {domain:ticket.domain,parent:ticket.id,generation:Some(ticket.generation)}).0)},
            None=>None,
        }
    }
    pub fn from_identity(child:ChildIdentity)->(out:(Self,ChildSnapshot))
        ensures out.0.wf(),out.0.domain_id()==child.domain_id(),out.0.owner()==child.owner(),out.0.episode().is_none(),
            out.1.wf(),out.1.source()==out.0.source(),out.1.state()==ChildStatus::<()>::Assigned(child),
    {Self::new(ChildSlot::from_identity(child),ChildOrigin {domain:child.domain,parent:child.parent,generation:None})}
    pub fn domain(&self)->(out:u64) ensures out==self.domain_id(), {self.origin.domain}
    pub fn generation(&self)->(out:Option<u64>) ensures out==self.episode(), {self.origin.generation}
    pub fn parent_id(&self)->(out:usize) ensures out==self.owner(), {self.origin.parent}
    pub fn snapshot(&self)->(out:ChildSnapshot)
        requires self.wf(),
        ensures out.wf(),out.source()==self.source(),out.state() is Assigned ==> out.state()->Assigned_0.domain_id()==self.domain_id()
            && out.state()->Assigned_0.owner()==self.owner(),
    {
        let guard=self.inner.acquire_read();
        let cell=guard.borrow();
        let out=cell.snapshot();
        guard.release_read();out
    }
    pub fn reject(&self)->(out:ChildTransition<bool>)
        requires self.wf(),
        ensures out.wf(self),out.result==(out.before.state() is Pending),
            out.result ==> out.after.state() is Failed,
            !out.result ==> out.after.state()==out.before.state(),
    {
        let (mut cell,guard)=self.inner.acquire_write();
        let before=cell.snapshot();
        let accepted=cell.slot.reject(()).is_ok();
        proof {cell.record();}
        let snapshot=cell.snapshot();
        guard.release_write(cell);ChildTransition {result:accepted,before,after:snapshot}
    }
}

/// Observations immediately before and after a single exclusive operation.
/// Their persistent tokens remain meaningful after this operation releases the lock.
pub struct ChildTransition<T> {pub result:T,pub before:ChildSnapshot,pub after:ChildSnapshot}
impl<T> ChildTransition<T> {
    pub open spec fn wf(&self,child:&SharedChild)->bool {
        self.before.wf() && self.after.wf() && self.before.source()==child.source() && self.after.source()==child.source()
    }
}
pub proof fn cancellation_precludes_assignment(tracked cancelled:&ChildSnapshot,tracked later:&ChildSnapshot)
    requires cancelled.wf(),later.wf(),cancelled.source()==later.source(),cancelled.state() is Cancelled,
    ensures !(later.state() is Assigned),
{
    if later.state() is Assigned {cancelled.terminal_agrees(later);}
}

pub struct NativeChildRequest<P> {payload:P,child:SharedChild}
impl<P> NativeChildRequest<P> {
    pub closed spec fn payload(&self)->P {self.payload}
    pub closed spec fn child(&self)->SharedChild {self.child}
    pub fn into_parts(self)->(out:(P,SharedChild)) ensures out.0==self.payload(),out.1==self.child(), {(self.payload,self.child)}
}
pub enum ChildDispatch<P,X> {Native(NativeChildRequest<P>),External(X)}
pub enum ChildCleanup<C,X> {Callback(C),Native(SharedChild),External(X),Value(crate::reversible_value::Inverse)}
impl<P,X,G> SetupWork<ChildDispatch<P,X>,G> {
    /// The caller supplies only the actual request payload. This method creates
    /// the shared state and both queue entries; a different inverse cannot be
    /// substituted by the host between the request and cleanup registration.
    pub fn enqueue_native_child<C,Y>(&mut self,cleanups:&mut CleanupGroups<ChildCleanup<C,Y>>,group:usize,payload:P)
        ->(out:Result<(SharedChild,usize),P>)
        requires old(self).wf(),old(cleanups).wf(),
        ensures final(cleanups).link()==old(cleanups).link(),final(cleanups).execution_journal()==old(cleanups).execution_journal(),final(self).link()==old(self).link(),final(cleanups).queues().dom()==old(cleanups).queues().dom(), final(self).domain_id()==old(self).domain_id(), final(self).accepts()==old(self).accepts(), final(self).is_closed()==old(self).is_closed(), final(cleanups).origin()==old(cleanups).origin(), final(cleanups).domain_ids()==old(cleanups).domain_ids(), final(cleanups).closed()==old(cleanups).closed(), final(cleanups).live(0)==old(cleanups).live(0), final(self).wf(),final(self).origin()==old(self).origin(),final(cleanups).wf(),
            out.is_ok()==(old(self).origin().is_some() && old(self).owns(old(cleanups)) && old(self).accepts()
                && old(self).next_id()<u64::MAX && old(cleanups).acquisition_open(group)),
            out.is_err() ==> out->Err_0==payload && *final(self)==*old(self) && *final(cleanups)==*old(cleanups),
            out.is_ok() ==> {
                let child=out->Ok_0.0;let token=out->Ok_0.1;
                &&& child.wf() && old(self).origin().is_some()
                &&& child.domain_id()==old(self).origin().unwrap().domain && child.owner()==old(self).origin().unwrap().id
                &&& child.episode()==Some(old(self).origin().unwrap().generation)
                &&& final(self).child_requests().len()==old(self).child_requests().len()+1
                &&& final(self).child_requests().last().value() is Native
                &&& final(self).child_requests().last().value()->Native_0.payload()==payload
                &&& final(self).child_requests().last().value()->Native_0.child()==child
                &&& token==old(cleanups).queues()[group].slots().len()
                &&& final(cleanups).queues()[group].slots()==old(cleanups).queues()[group].slots().push(Some(ChildCleanup::<C,Y>::Native(child)))
            },
    {
        if !self.matches(cleanups) || !self.can_enqueue() || !cleanups.accepts_acquisition(group) {return Err(payload);}
        let child=match SharedChild::from_work(self) {Some(child)=>child,None=>return Err(payload)};
        let request=ChildDispatch::Native(NativeChildRequest {payload,child:child.clone()});
        match self.enqueue_owned_child(cleanups,group,request,ChildCleanup::Native(child.clone())) {
            Ok(token)=>Ok((child,token)),
            Err((request,_inverse))=>match request {ChildDispatch::Native(request)=>Err(request.payload),ChildDispatch::External(_)=>{assert(false);panic!("native request");}},
        }
    }
}

impl<R,H> NativeHost<R,H> {
    #[allow(clippy::type_complexity)]
    pub fn register_shared_child(&mut self,child:&SharedChild,realms:&BTreeMap<u64,u64>,anchor:Port,definition:PluginDefinition<R>,host:H)
        ->(out:ChildTransition<Result<usize,(Error,PluginDefinition<R>,H)>>)
        requires old(self).wf(),child.wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),out.wf(child),
            out.result.is_ok()==(out.before.state() is Pending && child.domain_id()==old(self).state().protocol().domain_id()
                && child.episode()==old(self).state().control().generation_of(child.owner())
                && (old(self).state().control().phase_of(child.owner())==Some(crate::Phase::Loading)
                    || old(self).state().control().phase_of(child.owner())==Some(crate::Phase::Active))
                && old(self).state().registration_enabled(Some(child.owner()),realms@,anchor,&definition)),
            out.result.is_err() ==> out.result->Err_0.1==definition && out.result->Err_0.2==host
                && out.after.state()==out.before.state()
                && final(self).state().same(&old(self).state()) && final(self).entries()==old(self).entries(),
            out.result.is_ok() ==> out.after.state() is Assigned && out.after.state()->Assigned_0.child()==out.result->Ok_0
                && final(self).entries().dom()==old(self).entries().dom().insert(out.result->Ok_0)
                && (forall|n:usize| #[trigger] old(self).entries().contains_key(n) ==> final(self).entries()[n]==old(self).entries()[n])
                && final(self).entries()[out.result->Ok_0].recipe().version()==0
                && final(self).entries()[out.result->Ok_0].recipe().payload()==definition.payload()
                && final(self).entries()[out.result->Ok_0].recipe().realms()==realms@
                && final(self).entries()[out.result->Ok_0].recipe().anchor_port()==anchor
                && final(self).entries()[out.result->Ok_0].bookkeeping()==host
                && final(self).entries()[out.result->Ok_0].recipe().parent_id()==Some(child.owner())
                && crate::refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),out.result->Ok_0,crate::refinement::Rule::Insert),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let (mut cell,guard)=child.inner.acquire_write();
        let before=cell.snapshot();
        let result=self.register_child(&mut cell.slot,realms,anchor,definition,host);
        proof {cell.record();}
        let after=cell.snapshot();
        guard.release_write(cell);ChildTransition {result,before,after}
    }
    pub fn retire_shared_child(&mut self,child:&SharedChild)->(out:ChildTransition<Result<Option<ChildIdentity>,Error>>)
        requires old(self).wf(),child.wf(),
        ensures out.result.is_ok() && out.result->Ok_0.is_none() ==> final(self).state().same(&old(self).state()), final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),out.wf(child),
            out.result.is_err() ==> final(self).state().same(&old(self).state()) && out.after.state()==out.before.state(),
            out.result.is_ok() ==> !(out.after.state() is Pending)
                && (if out.before.state() is Pending {out.after.state() is Cancelled && out.result->Ok_0.is_none()}
                    else {out.after.state()==out.before.state()})
                && (out.result->Ok_0.is_some() ==> out.after.state()==ChildStatus::<()>::Assigned(out.result->Ok_0.unwrap())
                    && (if old(self).state().control().registered(out.result->Ok_0.unwrap().child()) {
                        crate::refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),out.result->Ok_0.unwrap().child(),crate::refinement::Rule::Retire)
                    } else {final(self).state().same(&old(self).state())})),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let (mut cell,guard)=child.inner.acquire_write();
        let before=cell.snapshot();
        let result=self.retire_child_slot(&mut cell.slot);
        proof {cell.record();}
        let after=cell.snapshot();
        guard.release_write(cell);ChildTransition {result,before,after}
    }
}

}
