//! Publications and their actual opaque payloads have one verified owner.
//! No public mutable registry or caller-selected slot can break this association.
//! Payload identity is proved; interior mutation and external I/O are separate.
#[cfg(verus_keep_ghost)]
use super::Publication;
use super::{LeaseId, PublicationError, PublicationId, PublicationRegistry};
use crate::lifecycle_actions::resources::CleanupReleaseError;
use crate::lifecycle_state::LifecycleState;
use crate::Port;
use vstd::prelude::*;

verus! {

pub struct RejectedValue<T> { pub error:PublicationError, pub value:T }
pub struct ReleasedValue<T> { pub publication:PublicationId, pub value:T }

pub struct PublicationStore<T> {
    registry:PublicationRegistry,
    payloads:Vec<Option<T>>,
    revisions:Vec<u64>,
}

impl<T> PublicationStore<T> {
    pub closed spec fn registry_view(&self)->PublicationRegistry {self.registry}
    pub closed spec fn values(&self)->Seq<Option<T>> {self.payloads@}
    pub closed spec fn revisions(&self)->Seq<u64> {self.revisions@}
    pub closed spec fn wf(&self)->bool {
        &&& self.registry.wf()
        &&& self.payloads.len()==self.registry.publications().len()
        &&& self.revisions.len()==self.payloads.len()
        &&& forall|i:int| 0<=i<self.payloads.len() ==> {
            &&& self.registry.publications()[i].slot==i
            &&& self.payloads[i].is_some()==self.registry.publications()[i].retained
        }
    }
    pub closed spec fn same(&self,prior:&Self)->bool {
        self.registry.unchanged(&prior.registry) && self.values()==prior.values() && self.revisions()==prior.revisions()
    }
    pub proof fn same_reflexive(&self)
        ensures self.same(self),
    {self.registry.unchanged_reflexive();}
    pub proof fn same_observations(&self,prior:&Self)
        requires self.same(prior),
        ensures self.registry_view().unchanged(&prior.registry_view()),self.values()==prior.values(),self.revisions()==prior.revisions(),
            self.registry_view().domain_id()==prior.registry_view().domain_id(),
    {self.registry.unchanged_observations(&prior.registry);}
    pub proof fn visible_value(&self,id:PublicationId)
        requires self.wf(),id.0<self.registry_view().publications().len(),self.registry_view().publications()[id.0 as int].visible,
        ensures id.0<self.values().len(),id.0<self.revisions().len(),self.values()[id.0 as int].is_some(),
    {reveal(PublicationRegistry::wf);}
    pub proof fn retained_value(&self,id:PublicationId)
        requires self.wf(),id.0<self.registry_view().publications().len(),self.registry_view().publications()[id.0 as int].retained,
        ensures id.0<self.values().len(),id.0<self.revisions().len(),self.values()[id.0 as int].is_some(),
    {}
    pub proof fn value_is_retained(&self,id:PublicationId)
        requires self.wf(),id.0<self.values().len(),self.values()[id.0 as int].is_some(),
        ensures id.0<self.registry_view().publications().len(),self.registry_view().publications()[id.0 as int].retained,
    {}
    pub proof fn visible_unique(&self,a:PublicationId,b:PublicationId)
        requires self.wf(),a.0<self.registry_view().publications().len(),b.0<self.registry_view().publications().len(),
            self.registry_view().publications()[a.0 as int].visible,self.registry_view().publications()[b.0 as int].visible,
            self.registry_view().publications()[a.0 as int].port==self.registry_view().publications()[b.0 as int].port,
        ensures a==b,
    {
        reveal(PublicationRegistry::wf);
        if a.0<b.0 {assert(self.registry_view().publications()[a.0 as int].port!=self.registry_view().publications()[b.0 as int].port);}
        if b.0<a.0 {assert(self.registry_view().publications()[b.0 as int].port!=self.registry_view().publications()[a.0 as int].port);}
    }
    pub open spec fn lease_frame(&self,prior:&Self)->bool {
        self.registry_view().domain_id()==prior.registry_view().domain_id()
            && self.registry_view().lease_records()==prior.registry_view().lease_records()
            && self.registry_view().lease_allocations()==prior.registry_view().lease_allocations()
    }
    pub open spec fn released(&self,prior:&Self,leases:Seq<LeaseId>,publications:Seq<PublicationId>)->bool {
        &&& self.registry_view().domain_id()==prior.registry_view().domain_id()
        &&& self.registry_view().lease_allocations()==prior.registry_view().lease_allocations()
        &&& forall|lease:LeaseId|self.registry_view().active_lease(lease)==if leases.contains(lease) {None} else {prior.registry_view().active_lease(lease)}
        &&& self.registry_view().publications().len()==prior.registry_view().publications().len()
        &&& forall|i:int|0<=i<self.registry_view().publications().len() ==> self.registry_view().publications()[i]==
            if publications.contains(PublicationId(i as usize)) {Publication {retained:false,..prior.registry_view().publications()[i]}} else {prior.registry_view().publications()[i]}
        &&& self.values().len()==prior.values().len()
        &&& forall|i:int|0<=i<self.values().len() ==> self.values()[i]==if publications.contains(PublicationId(i as usize)) {None} else {prior.values()[i]}
        &&& self.revisions()==prior.revisions()
    }
    pub fn for_domain(domain:u64)->(out:Self)
        ensures out.wf(),out.registry_view().domain_id()==Some(domain),out.values().len()==0,
            out.revisions().len()==0,out.registry_view().publications().len()==0,
            out.registry_view().lease_records().len()==0,out.registry_view().lease_allocations()==0,
    {Self {registry:PublicationRegistry::for_domain(domain),payloads:Vec::new(),revisions:Vec::new()}}

    pub proof fn slot_count(&self)
        requires self.wf(),ensures self.registry_view().wf(),self.values().len()==self.registry_view().publications().len(),self.values().len()<=usize::MAX,
    {}

    pub fn registry(&self)->(out:&PublicationRegistry)
        requires self.wf(),ensures *out==self.registry_view(),out.wf(),
    {&self.registry}

    pub fn publish(&mut self,owner:usize,generation:u64,port:Port,value:T)
        ->(out:Result<PublicationId,RejectedValue<T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).lease_frame(old(self)),
            out.is_err() ==> final(self).same(old(self)) && out->Err_0.value==value,
            out.is_ok() ==> old(self).lookup(port).is_none()
                && final(self).visible_table()==crate::coeffects::put(old(self).visible_table(),port,Some(value)),
            out.is_ok() ==> out->Ok_0.0==old(self).values().len()
                && final(self).values()==old(self).values().push(Some(value))
                && final(self).revisions()==old(self).revisions().push(0)
                && final(self).registry_view().publications()==old(self).registry_view().publications().push(
                    Publication {owner,generation,port,slot:out->Ok_0.0,visible:true,retained:true}),
    {
        let ghost prior=*self;
        let slot=self.payloads.len();
        match self.registry.publish(owner,generation,port,slot) {
            Err(error)=>Err(RejectedValue {error,value}),
            Ok(id)=>{self.payloads.push(Some(value));self.revisions.push(0);proof {self.appended_value(&prior,owner,generation,port,value);} Ok(id)},
        }
    }

    /// Production managed publication checks the real control owner and
    /// generation and the store domain in the same exclusive value operation.
    pub fn publish_checked(&mut self,state:&LifecycleState,owner:usize,generation:u64,port:Port,value:T)
        ->(out:Result<PublicationId,RejectedValue<T>>)
        requires old(self).wf(),state.wf(),
        ensures final(self).wf(),final(self).lease_frame(old(self)),
            out.is_err() ==> final(self).same(old(self)) && out->Err_0.value==value,
            out.is_ok() ==> state.service_open(owner,generation)
                && old(self).registry_view().domain_id()==Some(state.protocol().domain_id())
                && old(self).lookup(port).is_none()
                && final(self).visible_table()==crate::coeffects::put(old(self).visible_table(),port,Some(value))
                && out->Ok_0.0==old(self).values().len()
                && final(self).values()==old(self).values().push(Some(value))
                && final(self).revisions()==old(self).revisions().push(0)
                && final(self).registry_view().publications()==old(self).registry_view().publications().push(
                    Publication {owner,generation,port,slot:out->Ok_0.0,visible:true,retained:true}),
    {
        if self.registry.domain()!=Some(state.domain()) || state.check_service_access(owner,generation).is_err() {
            proof {self.registry.unchanged_reflexive();}
            return Err(RejectedValue {error:PublicationError::InvalidState,value});
        }
        self.publish(owner,generation,port,value)
    }
    pub fn replace_checked(&mut self,state:&LifecycleState,id:PublicationId,owner:usize,generation:u64,value:T)
        ->(out:Result<T,RejectedValue<T>>)
        requires old(self).wf(),state.wf(),
        ensures final(self).wf(),final(self).registry_view().unchanged(&old(self).registry_view()),final(self).registry_view().domain_id()==old(self).registry_view().domain_id(),
            out.is_err() ==> final(self).same(old(self)) && out->Err_0.value==value,
            out.is_ok() ==> state.service_open(owner,generation)
                && old(self).registry_view().domain_id()==Some(state.protocol().domain_id())
                && id.0<old(self).values().len() && old(self).values()[id.0 as int]==Some(out->Ok_0)
                && old(self).registry_view().publications()[id.0 as int].visible
                && old(self).registry_view().publications()[id.0 as int].owner==owner
                && old(self).registry_view().publications()[id.0 as int].generation==generation
                && final(self).values()==old(self).values().update(id.0 as int,Some(value))
                && old(self).revisions()[id.0 as int]<u64::MAX
                && final(self).revisions()==old(self).revisions().update(id.0 as int,(old(self).revisions()[id.0 as int]+1) as u64)
                && final(self).visible_table()==crate::coeffects::put(old(self).visible_table(),old(self).registry_view().publications()[id.0 as int].port,Some(value))
                && old(self).lookup(old(self).registry_view().publications()[id.0 as int].port)==Some(out->Ok_0),
    {
        if self.registry.domain()!=Some(state.domain()) || state.check_service_access(owner,generation).is_err() {
            proof {self.registry.unchanged_reflexive();}
            return Err(RejectedValue {error:PublicationError::InvalidState,value});
        }
        self.replace(id,owner,generation,value)
    }

    /// Read the exact retained payload, including after visibility is revoked.
    pub fn value(&self,id:PublicationId)->(out:Option<&T>)
        requires self.wf(),
        ensures out.is_some()==(id.0<self.values().len() && self.values()[id.0 as int].is_some()),
            out.is_some() ==> *out.unwrap()==self.values()[id.0 as int].unwrap(),
    {
        if id.0>=self.payloads.len() {None} else {self.payloads[id.0].as_ref()}
    }

    /// The retained payload and its replacement version come from the same
    /// owner. Reclamation does not reuse the publication identity or revision.
    pub fn observation(&self,id:PublicationId)->(out:Option<(u64,&T)>)
        requires self.wf(),
        ensures out.is_some()==(id.0<self.values().len() && self.values()[id.0 as int].is_some()),
            out.is_some() ==> id.0<self.revisions().len() && out.unwrap().0==self.revisions()[id.0 as int]
                && Some(*out.unwrap().1)==self.values()[id.0 as int],
    {
        if id.0>=self.payloads.len() {return None;}
        match &self.payloads[id.0] {Some(value)=>Some((self.revisions[id.0],value)),None=>None}
    }

    /// Resolve a retained value from the actual lease record, so the caller
    /// cannot substitute a different publication while presenting a valid lease.
    pub fn leased_value(&self,token:LeaseId)->(out:Result<(PublicationId,&T),PublicationError>)
        requires self.wf(),
        ensures out.is_ok()==self.registry_view().active_lease(token).is_some(),
            out.is_ok() ==> out->Ok_0.0==self.registry_view().active_lease(token).unwrap().publication
                && self.values()[out->Ok_0.0.0 as int]==Some(*out->Ok_0.1),
    {
        let lease=match self.registry.lease(token) {
            Some(lease)=>lease,
            None=>return Err(if token.0>=self.registry.lease_allocation_count() {PublicationError::Unknown} else {PublicationError::Released}),
        };
        proof {
            reveal(PublicationRegistry::active_lease);reveal(PublicationRegistry::wf);
            let i=choose|i:int|0<=i<self.registry.lease_records().len() && self.registry.lease_records()[i].id==token;
            assert(lease==self.registry.lease_records()[i].lease);
        }
        Ok((lease.publication,self.payloads[lease.publication.0].as_ref().unwrap()))
    }

    pub fn leased_observation(&self,token:LeaseId)->(out:Result<(PublicationId,u64,&T),PublicationError>)
        requires self.wf(),
        ensures out.is_ok()==self.registry_view().active_lease(token).is_some(),
            out.is_ok() ==> out->Ok_0.0==self.registry_view().active_lease(token).unwrap().publication
                && out->Ok_0.1==self.revisions()[out->Ok_0.0.0 as int]
                && self.values()[out->Ok_0.0.0 as int]==Some(*out->Ok_0.2),
    {
        match self.leased_value(token) {
            Err(error)=>Err(error),
            Ok((publication,value))=>Ok((publication,self.revisions[publication.0],value)),
        }
    }

    /// Replacement returns the actual previous payload. The publication and
    /// all leases keep their identities; a rejection returns the input intact.
    pub fn replace(&mut self,id:PublicationId,owner:usize,generation:u64,value:T)
        ->(out:Result<T,RejectedValue<T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).registry_view().unchanged(&old(self).registry_view()),final(self).registry_view().domain_id()==old(self).registry_view().domain_id(),
            out.is_err() ==> final(self).same(old(self)) && out->Err_0.value==value,
            out.is_ok() ==> id.0<old(self).values().len()
                && old(self).registry_view().publications()[id.0 as int].visible
                && old(self).registry_view().publications()[id.0 as int].owner==owner
                && old(self).registry_view().publications()[id.0 as int].generation==generation
                && old(self).values()[id.0 as int]==Some(out->Ok_0)
                && final(self).values()==old(self).values().update(id.0 as int,Some(value))
                && old(self).revisions()[id.0 as int]<u64::MAX
                && final(self).revisions()==old(self).revisions().update(id.0 as int,(old(self).revisions()[id.0 as int]+1) as u64)
                && final(self).visible_table()==crate::coeffects::put(old(self).visible_table(),old(self).registry_view().publications()[id.0 as int].port,Some(value))
                && old(self).lookup(old(self).registry_view().publications()[id.0 as int].port)==Some(out->Ok_0),
    {
        let ghost prior=*self;
        proof {self.registry.unchanged_reflexive();}
        let entry=match self.registry.entry(id) {Some(entry)=>entry,None=>return Err(RejectedValue {error:PublicationError::Unknown,value})};
        if entry.owner!=owner || entry.generation!=generation {return Err(RejectedValue {error:PublicationError::InvalidState,value});}
        if !entry.visible {return Err(RejectedValue {error:PublicationError::Revoked,value});}
        if self.revisions[id.0]==u64::MAX {return Err(RejectedValue {error:PublicationError::Capacity,value});}
        let previous=self.payloads[id.0].take().unwrap();
        self.payloads[id.0]=Some(value);
        self.revisions.set(id.0,self.revisions[id.0]+1);
        proof {
            reveal(PublicationRegistry::unchanged);
            assert(self.values() =~= prior.values().update(id.0 as int,Some(value)));
            self.replaced_value(&prior,id,value);
        }
        Ok(previous)
    }

    pub fn revoke(&mut self,id:PublicationId)->(out:Result<(),PublicationError>)
        requires old(self).wf(),
        ensures out.is_ok()==(id.0<old(self).values().len()),final(self).wf(),final(self).lease_frame(old(self)),final(self).values()==old(self).values(),final(self).revisions()==old(self).revisions(),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> id.0<old(self).values().len()
                && final(self).registry_view().publications()==old(self).registry_view().publications().update(id.0 as int,
                    Publication {visible:false,..old(self).registry_view().publications()[id.0 as int]})
                && final(self).visible_table()==
                if old(self).registry_view().publications()[id.0 as int].visible {
                    old(self).visible_table().remove(old(self).registry_view().publications()[id.0 as int].port)
                } else {old(self).visible_table()},
    {
        let ghost prior=*self;let out=self.registry.revoke(id);
        proof {if out.is_ok() {self.revoked_value(&prior,id);}}
        out
    }

    pub fn acquire_for(&mut self,id:PublicationId,owner:usize,generation:u64)->(out:Result<LeaseId,PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).values()==old(self).values(),final(self).revisions()==old(self).revisions(),
            final(self).visible_table()==old(self).visible_table(),
            final(self).registry_view().domain_id()==old(self).registry_view().domain_id(),
            final(self).registry_view().publications()==old(self).registry_view().publications(),
            out.is_ok()==old(self).registry_view().acquisition_enabled(id),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> out->Ok_0.0==old(self).registry_view().lease_allocations()
                && final(self).registry_view().lease_allocations()==old(self).registry_view().lease_allocations()+1
                && final(self).registry_view().lease_records()==old(self).registry_view().lease_records().push(
                    super::LeaseRecord {id:out->Ok_0,lease:super::Lease {publication:id,live:true,consumer:Some(super::LeaseOwner {owner,generation})}})
                && final(self).registry_view().active_lease(out->Ok_0)==Some(super::Lease {publication:id,live:true,consumer:Some(super::LeaseOwner {owner,generation})}),
    {
        let ghost prior=*self;
        let out=self.registry.acquire_for(id,owner,generation);
        proof {self.visible_frame(&prior);if out.is_ok() {
            let i=self.registry.lease_records().len()-1;
            self.registry.lease_at_position(i);
        }}
        out
    }

    pub fn release(&mut self,lease:LeaseId)->(out:Result<(),PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).values()==old(self).values(),final(self).visible_table()==old(self).visible_table(),final(self).revisions()==old(self).revisions(),
    {let ghost prior=*self;let out=self.registry.release(lease);proof {reveal(PublicationRegistry::unchanged);self.visible_frame(&prior);}out}

    pub fn adopt(&mut self,id:PublicationId,owner:usize,generation:u64)->(out:Result<(),PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).lease_frame(old(self)),final(self).values()==old(self).values(),final(self).visible_table()==old(self).visible_table(),final(self).revisions()==old(self).revisions(),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> id.0<old(self).values().len() && old(self).registry_view().publications()[id.0 as int].owner==owner
                && old(self).registry_view().publications()[id.0 as int].generation==0 && generation==1 && old(self).registry_view().unleased(id)
                && final(self).registry_view().publications()==old(self).registry_view().publications().update(id.0 as int,
                    Publication {generation,..old(self).registry_view().publications()[id.0 as int]}),
    {let ghost prior=*self;let out=self.registry.adopt(id,owner,generation);proof {reveal(PublicationRegistry::unchanged);self.visible_frame(&prior);}out}

    pub fn reclaim(&mut self,id:PublicationId)->(out:Result<T,PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).lease_frame(old(self)),final(self).visible_table()==old(self).visible_table(),final(self).revisions()==old(self).revisions(),out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> id.0<old(self).values().len() && old(self).values()[id.0 as int]==Some(out->Ok_0)
                && final(self).values()==old(self).values().update(id.0 as int,None)
                && final(self).registry_view().publications()==old(self).registry_view().publications().update(id.0 as int,
                    Publication {retained:false,..old(self).registry_view().publications()[id.0 as int]})
                && old(self).registry_view().unleased(id)
                && !old(self).registry_view().publications()[id.0 as int].visible,
    {
        let ghost prior=*self;
        let slot=match self.registry.reclaim(id) {
            Ok(slot)=>slot,
            Err(error)=>{proof {reveal(PublicationRegistry::unchanged);self.visible_frame(&prior);}return Err(error);},
        };
        let value=self.payloads[slot].take().unwrap();
        proof {self.visible_frame(&prior);}
        Ok(value)
    }

    /// Transfer payloads only after the composed lifecycle/lease protocol has
    /// accepted the exact cleanup attempt and its complete resource manifest.
    pub fn finish_resources(&mut self,state:&mut LifecycleState,id:usize,reservation:bool,
        leases:&[LeaseId],publications:&[PublicationId])->(out:Result<Vec<ReleasedValue<T>>,CleanupReleaseError>)
        requires old(self).wf(),old(state).wf(),
        ensures out.is_ok()==(old(self).registry_view().domain_id()==Some(old(state).protocol().domain_id())
                && old(state).protocol().resource_finish_enabled(&old(state).control(),id,reservation)
                && old(self).registry_view().cleanup_batch_enabled(super::LeaseOwner {owner:id,generation:old(state).control().generation_of(id).unwrap()},leases@,publications@)),
            final(self).wf(),final(state).wf(),
            final(self).registry_view().domain_id()==old(self).registry_view().domain_id(),
            final(state).control_history().extends(old(state).control_history()),
            final(state).cleanup_step(old(state),crate::lifecycle_state::cleanup::CleanupCommand::Release {id,reservation},crate::lifecycle_state::cleanup::resource_reply(out)),
            reservation ==> final(state).control().unchanged(&old(state).control()),
            out.is_ok() ==> final(self).released(old(self),leases@,publications@),final(self).visible_table()==old(self).visible_table(),final(self).revisions()==old(self).revisions(),
            out.is_err() ==> final(self).same(old(self))
                && final(state).control().unchanged(&old(state).control())
                && final(state).protocol().same(&old(state).protocol()),
            out.is_ok() ==> out->Ok_0.len()==publications.len()
                && (forall|i:int| 0<=i<out->Ok_0.len() ==> out->Ok_0[i].publication==publications[i]
                    && publications[i].0<old(self).values().len()
                    && old(self).values()[publications[i].0 as int]==Some(out->Ok_0[i].value))
                && (forall|i:int| 0<=i<final(self).values().len() ==> final(self).values()[i]==
                    if publications@.contains(PublicationId(i as usize)) {None} else {old(self).values()[i]})
                && old(state).protocol().resource_finish_enabled(&old(state).control(),id,reservation)
                && !final(state).protocol().blocked_spec(id)
                && final(self).registry_view().episode_resources_cleared(super::LeaseOwner {owner:id,generation:old(state).control().generation_of(id).unwrap()}),
            out.is_ok() && !reservation ==> crate::refinement::step(old(state).control().paper(),final(state).control().paper(),id,crate::refinement::Rule::Unload),
    {
        let ghost prior=*self;
        let released=match state.finish_cleanup_resources(&mut self.registry,id,reservation,leases,publications) {
            Ok(released)=>released,
            Err(error)=>{proof {reveal(PublicationRegistry::unchanged);self.visible_frame(&prior);}return Err(error);},
        };
        let mut values:Vec<ReleasedValue<T>>=Vec::new();
        let mut i=0;
        while i<released.len()
            invariant i<=released.len(),values.len()==i,prior.wf(),self.registry.wf(),
                self.registry.cleanup_batch_released(&prior.registry,leases@,publications@,released@),
                self.payloads.len()==prior.payloads.len(),
                forall|k:int| 0<=k<self.payloads.len() ==> self.payloads[k]==
                    if publications@.subrange(0,i as int).contains(PublicationId(k as usize)) {None} else {prior.payloads[k]},
                forall|k:int| 0<=k<i ==> values[k].publication==publications[k] && prior.payloads[publications[k].0 as int]==Some(values[k].value),
                forall|k:int,j:int| 0<=k<j<publications.len() ==> publications[k]!=publications[j],
                forall|k:int| 0<=k<publications.len() ==> publications[k].0<prior.payloads.len() && prior.payloads[publications[k].0 as int].is_some(),
            decreases released.len()-i,
        {
            let item=released[i];
            proof {
                assert(item.publication==publications[i as int]);
                assert(item.slot==prior.registry.publications()[item.publication.0 as int].slot);
                assert(item.slot==item.publication.0);
                assert(!publications@.subrange(0,i as int).contains(item.publication)) by {
                    assert forall|j:int| 0<=j<i implies publications[j]!=item.publication by {}
                }
            }
            let value=self.payloads[item.slot].take().unwrap();
            values.push(ReleasedValue {publication:item.publication,value});
            proof {
                assert forall|k:int| 0<=k<self.payloads.len() implies self.payloads[k]==
                    if publications@.subrange(0,i as int+1).contains(PublicationId(k as usize)) {None} else {prior.payloads[k]} by {
                    super::cleanup::prefix_member(publications@,i as int,PublicationId(k as usize));
                }
            }
            i+=1;
        }
        assert(publications@.subrange(0,i as int)==publications@);
        proof {self.visible_frame(&prior);}
        Ok(values)
    }

    pub fn retained_count(&self)->(out:usize)
        requires self.wf(),ensures out<=self.values().len(),
    {
        let mut i=0;let mut count=0;
        while i<self.payloads.len()
            invariant count<=i,i<=self.payloads.len(),
            decreases self.payloads.len()-i,
        {if self.payloads[i].is_some() {count+=1;}i+=1;}
        count
    }
}

impl PublicationStore<u64> {
    pub fn contains_handle(&self,value:u64)->(out:bool)
        ensures out==(exists|i:int| 0<=i<self.values().len() && self.values()[i]==Some(value)),
    {
        let mut i=0;
        while i<self.payloads.len()
            invariant i<=self.payloads.len(),forall|k:int| 0<=k<i ==> self.payloads[k]!=Some(value),
            decreases self.payloads.len()-i,
        {if self.payloads[i]==Some(value) {return true;}i+=1;}
        false
    }
}

/// Used inside the ordinary host's mutex. The kernel moves the actual value;
/// it neither clones arbitrary payloads nor executes their destructors.
pub struct ValueCell<T> {value:T}
impl<T> ValueCell<T> {
    pub closed spec fn view(&self)->T {self.value}
    pub fn new(value:T)->(out:Self) ensures out.view()==value, {Self {value}}
    pub fn get(&self)->(out:&T) ensures *out==self.view(), {&self.value}
    pub fn replace(&mut self,value:T)->(out:T)
        ensures out==old(self).view(),final(self).view()==value,
    {let mut previous=value;core::mem::swap(&mut self.value,&mut previous);previous}
}

}

#[path = "publication_projection.rs"]
pub mod projection;
