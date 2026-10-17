//! One-shot native Child assignment shared by its request and inverse.
//! The ordinary host synchronizes access; all successful allocation and native
//! retirement decisions mutate this private state through verified operations.
use super::{ChildIdentity, PluginDefinition, RegisteredPlugin};
use crate::action_ledger::ActionTicket;
use crate::lifecycle_state::LifecycleState;
use crate::setup_work::SetupWork;
#[cfg(verus_keep_ghost)]
use crate::Kernel;
use crate::{Error, Phase, Port};
use std::collections::BTreeMap;
use vstd::prelude::*;

verus! {

pub enum ChildStatus<E> { Pending, Assigned(ChildIdentity), Failed(E), Cancelled }
pub struct ChildSlot<E> {domain:u64,parent:usize,generation:Option<u64>,status:ChildStatus<E>}
impl<E> ChildSlot<E> {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn owner(&self)->usize {self.parent}
    pub closed spec fn episode(&self)->Option<u64> {self.generation}
    pub closed spec fn state(&self)->ChildStatus<E> {self.status}
    pub open spec fn wf(&self)->bool {
        (self.state() is Assigned ==> self.state()->Assigned_0.domain_id()==self.domain_id()
            && self.state()->Assigned_0.owner()==self.owner())
        && (self.state() is Pending ==> self.episode().is_some())
    }
    pub open spec fn same_origin(&self,prior:&Self)->bool {
        self.domain_id()==prior.domain_id() && self.owner()==prior.owner() && self.episode()==prior.episode()
    }
    /// This constructor cannot invent a successful assignment.
    pub fn from_work<C,G>(work:&SetupWork<C,G>)->(out:Option<Self>)
        requires work.wf(),
        ensures out.is_some()==work.origin().is_some(),out.is_some() ==> out.unwrap().wf()
            && out.unwrap().domain_id()==work.origin().unwrap().domain && out.unwrap().owner()==work.origin().unwrap().id
            && out.unwrap().episode()==Some(work.origin().unwrap().generation) && out.unwrap().state() is Pending,
    {
        work.lifecycle_ticket().map(|ticket:ActionTicket| -> (out:Self)
            ensures out.wf(),out.domain_id()==ticket.domain,out.owner()==ticket.id,
                out.episode()==Some(ticket.generation),out.state() is Pending,
            {Self {domain:ticket.domain,parent:ticket.id,generation:Some(ticket.generation),status:ChildStatus::Pending}})
    }
    /// Externally mounted native children already carry a registration identity.
    pub fn from_identity(child:ChildIdentity)->(out:Self)
        ensures out.wf(),out.domain_id()==child.domain_id(),out.owner()==child.owner(),
            out.episode().is_none(),out.state()==ChildStatus::<E>::Assigned(child),
    {Self {domain:child.domain,parent:child.parent,generation:None,status:ChildStatus::Assigned(child)}}
    pub fn identity(&self)->(out:Option<ChildIdentity>)
        ensures out==match self.state() {ChildStatus::Assigned(child)=>Some(child),_=>None},
    {match &self.status {ChildStatus::Assigned(child)=>Some(*child),_=>None}}
    pub fn error(&self)->(out:Option<&E>)
        ensures out.is_some()==(self.state() is Failed),out.is_some() ==> *out.unwrap()==self.state()->Failed_0,
    {match &self.status {ChildStatus::Failed(error)=>Some(error),_=>None}}
    pub fn parent_id(&self)->(out:usize) ensures out==self.owner(), {self.parent}
    pub fn pending(&self)->(out:bool) ensures out==(self.state() is Pending), {matches!(self.status,ChildStatus::Pending)}
    /// Host validation may reject a request, but cannot assign a child or erase
    /// a successful assignment. A duplicate rejection returns the real input.
    pub fn reject(&mut self,error:E)->(out:Result<(),E>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_origin(old(self)),out.is_ok()==(old(self).state() is Pending),
            out.is_ok() ==> final(self).state()==ChildStatus::<E>::Failed(error),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==error,
    {
        if !self.pending() {return Err(error);}
        self.status=ChildStatus::Failed(error);Ok(())
    }
}
impl LifecycleState {
    /// Allocate from the real definition and write that exact child's identity
    /// into the slot. Closed, foreign or obsolete requests allocate nothing.
    pub fn register_child_slot<T,E>(&mut self,slot:&mut ChildSlot<E>,realms:&BTreeMap<u64,u64>,anchor:Port,definition:PluginDefinition<T>)
        ->(out:Result<RegisteredPlugin<T>,(Error,PluginDefinition<T>)>)
        requires old(self).wf(),old(slot).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(slot).wf(),final(slot).same_origin(old(slot)),
            final(self).protocol().same(&old(self).protocol()),
            out.is_ok()==(old(slot).state() is Pending && old(slot).domain_id()==old(self).protocol().domain_id()
                && old(slot).episode()==old(self).control().generation_of(old(slot).owner())
                && (old(self).control().phase_of(old(slot).owner())==Some(Phase::Loading)
                    || old(self).control().phase_of(old(slot).owner())==Some(Phase::Active))
                && old(self).registration_enabled(Some(old(slot).owner()),realms@,anchor,&definition)),
            out.is_err() ==> final(self).same(old(self)) && *final(slot)==*old(slot) && out->Err_0.1==definition,
            out.is_ok() ==> {
                let plugin=out->Ok_0;
                &&& old(slot).state() is Pending
                &&& final(slot).state() is Assigned
                &&& final(slot).state()->Assigned_0.child()==plugin.owner()
                &&& plugin.domain_id()==old(slot).domain_id() && plugin.parent_id()==Some(old(slot).owner())
                &&& plugin.owner()==old(self).control().next_id() && plugin.payload()==definition.payload()
                &&& plugin.anchor_port()==anchor && plugin.realms()==realms@ && plugin.version()==0
                &&& final(self).control().paper().fibers[plugin.owner()].parent==plugin.parent_id()
                &&& (forall|p:Port| #[trigger] final(self).control().paper().fibers[plugin.owner()].dependencies.contains(p)==plugin.dependencies_spec().contains(p))
                &&& (forall|p:Port| #[trigger] final(self).control().paper().fibers[plugin.owner()].provisions.contains(p)==(plugin.provisions_spec().contains(p) || p==anchor))
                &&& crate::refinement::step(old(self).control().paper(),final(self).control().paper(),plugin.owner(),crate::refinement::Rule::Insert)
            },
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {reveal(Kernel::unchanged);self.actions.same_reflexive();}
        if !slot.pending() || slot.domain!=self.domain() || slot.generation!=self.kernel.episode_generation(slot.parent) {
            return Err((Error::InvalidState,definition));
        }
        let phase=self.kernel.phase(slot.parent);
        if phase!=Some(Phase::Loading) && phase!=Some(Phase::Active) {return Err((Error::InvalidState,definition));}
        match self.register_plugin(Some(slot.parent),realms,anchor,definition) {
            Ok(plugin)=>{
                let identity=plugin.child_identity().unwrap();
                slot.status=ChildStatus::Assigned(identity);
                Ok(plugin)
            },
            Err(error)=>Err(error),
        }
    }
    /// Pending inverses cancel the slot before reporting completion. A later
    /// request cannot allocate an unowned child after that inverse was consumed.
    pub fn retire_child_slot<E>(&mut self,slot:&mut ChildSlot<E>)->(out:Result<Option<ChildIdentity>,Error>)
        requires old(self).wf(),old(slot).wf(),
        ensures out.is_ok() && out->Ok_0.is_none() ==> final(self).same(old(self)), final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(slot).wf(),final(slot).same_origin(old(slot)),
            final(self).protocol().same(&old(self).protocol()),
            out.is_err() ==> final(self).same(old(self)) && *final(slot)==*old(slot),
            out.is_ok() ==> old(slot).domain_id()==old(self).protocol().domain_id()
                && !(final(slot).state() is Pending)
                && (if old(slot).state() is Assigned {
                    let child=old(slot).state()->Assigned_0;
                    &&& *final(slot)==*old(slot) && out->Ok_0==Some(child)
                    &&& if old(self).control().registered(child.child()) {
                        old(self).control().paper().fibers[child.child()].parent==Some(child.owner())
                            && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),child.child(),crate::refinement::Rule::Retire)
                    } else {final(self).same(old(self))}
                } else {
                    &&& out->Ok_0.is_none() && final(self).same(old(self))
                    &&& if old(slot).state() is Pending {final(slot).state() is Cancelled} else {*final(slot)==*old(slot)}
                }),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {reveal(Kernel::unchanged);self.actions.same_reflexive();}
        if slot.domain!=self.domain() {return Err(Error::InvalidState);}
        match slot.identity() {
            Some(child)=>match self.retire_child(child) {Ok(())=>Ok(Some(child)),Err(error)=>Err(error)},
            None=>{if slot.pending() {slot.status=ChildStatus::Cancelled;} Ok(None)},
        }
    }
}

}
