//! Checked, atomic release of one consumer episode's managed resources.
//!
//! The manifest comes from the host. Every selected lease and publication is
//! checked against its recorded owner/generation before any mutation. The registry
//! also checks that no resource of this episode was omitted. Callback reports
//! and opaque host-value destruction remain outside this proof.
#[cfg(verus_keep_ghost)]
use super::Publication;
use super::{LeaseId, LeaseOwner, PublicationError, PublicationId, PublicationRegistry};
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct ReleasedPublication { pub publication: PublicationId, pub slot: usize }

fn has_lease(items:&[LeaseId],item:LeaseId)->(found:bool)
    ensures found==items@.contains(item),
{
    let mut i=0;
    while i<items.len()
        invariant i<=items.len(),forall|k:int| 0<=k<i ==> items[k]!=item,
        decreases items.len()-i,
    {
        if items[i]==item {return true;}
        i+=1;
    }
    false
}

fn has_publication(items:&[PublicationId],item:PublicationId)->(found:bool)
    ensures found==items@.contains(item),
{
    let mut i=0;
    while i<items.len()
        invariant i<=items.len(),forall|k:int| 0<=k<i ==> items[k]!=item,
        decreases items.len()-i,
    {
        if items[i]==item {return true;}
        i+=1;
    }
    false
}

proof fn prefix_member<T>(items:Seq<T>,i:int,value:T)
    requires 0<=i<items.len(),
    ensures items.subrange(0,i+1).contains(value)==(items.subrange(0,i).contains(value) || items[i]==value),
{
    let short=items.subrange(0,i);let long=items.subrange(0,i+1);
    if long.contains(value) {
        let j=choose|j:int| 0<=j<long.len() && long[j]==value;
        if j<i {assert(short[j]==value);assert(short.contains(value));}
    }
    if short.contains(value) {
        let j=choose|j:int| 0<=j<short.len() && short[j]==value;
        assert(long[j]==value);assert(long.contains(value));
    }
    if items[i]==value {assert(long[i]==value);assert(long.contains(value));}
}

impl PublicationRegistry {
    proof fn same_lease_projection(&self,prior:&Self)
        requires self.wf(),prior.wf(),self.lease_records()==prior.lease_records(),
        ensures forall|token:LeaseId| self.active_lease(token)==prior.active_lease(token),
    {
        reveal(PublicationRegistry::active_lease);
        assert forall|token:LeaseId| self.active_lease(token)==prior.active_lease(token) by {
            if prior.active_lease(token).is_some() {
                let j=choose|j:int| 0<=j<prior.leases.len() && prior.leases[j].id==token;
                prior.lease_at_position(j);self.lease_at_position(j);
            }
        }
    }

    pub closed spec fn cleanup_batch_enabled(&self,owner:LeaseOwner,leases:Seq<LeaseId>,publications:Seq<PublicationId>)->bool {
        &&& forall|i:int| 0<=i<leases.len() ==> self.active_lease(leases[i]).is_some()
            && self.active_lease(leases[i]).unwrap().consumer==Some(owner)
        &&& forall|i:int,j:int| 0<=i<j<leases.len() ==> leases[i]!=leases[j]
        &&& forall|i:int| 0<=i<publications.len() ==> publications[i].0<self.publications().len()
            && self.publications()[publications[i].0 as int].retained
            && !self.publications()[publications[i].0 as int].visible
            && self.publications()[publications[i].0 as int].owner==owner.owner
            && self.publications()[publications[i].0 as int].generation==owner.generation
        &&& forall|i:int,j:int| 0<=i<j<publications.len() ==> publications[i]!=publications[j]
        &&& forall|token:LeaseId| self.active_lease(token).is_some()
            && (publications.contains(self.active_lease(token).unwrap().publication)
                || self.active_lease(token).unwrap().consumer==Some(owner)) ==> leases.contains(token)
        &&& forall|i:int| 0<=i<self.publications().len() && self.publications()[i].retained
            && self.publications()[i].owner==owner.owner && self.publications()[i].generation==owner.generation
            ==> publications.contains(PublicationId(i as usize))
    }

    pub closed spec fn episode_resources_cleared(&self,owner:LeaseOwner)->bool {
        &&& forall|token:LeaseId| self.active_lease(token).is_some() ==> self.active_lease(token).unwrap().consumer!=Some(owner)
        &&& forall|i:int| 0<=i<self.publications().len() && self.publications()[i].owner==owner.owner
            && self.publications()[i].generation==owner.generation ==> !self.publications()[i].retained
    }

    proof fn batch_clears_episode(&self,prior:&Self,owner:LeaseOwner,leases:Seq<LeaseId>,publications:Seq<PublicationId>,released:Seq<ReleasedPublication>)
        requires prior.cleanup_batch_enabled(owner,leases,publications),self.cleanup_batch_released(prior,leases,publications,released),
        ensures self.episode_resources_cleared(owner),
    {
        assert forall|token:LeaseId| self.active_lease(token).is_some() implies self.active_lease(token).unwrap().consumer!=Some(owner) by {
            if self.active_lease(token).unwrap().consumer==Some(owner) {
                assert(!leases.contains(token));assert(prior.active_lease(token)==self.active_lease(token));
                assert(leases.contains(token));
            }
        }
        assert forall|i:int| 0<=i<self.publications().len() && self.publications()[i].owner==owner.owner
            && self.publications()[i].generation==owner.generation implies !self.publications()[i].retained by {
            assert(prior.publications()[i].owner==owner.owner);
            assert(prior.publications()[i].generation==owner.generation);
        }
    }

    pub closed spec fn cleanup_batch_released(&self,prior:&Self,leases:Seq<LeaseId>,publications:Seq<PublicationId>,released:Seq<ReleasedPublication>)->bool {
        &&& self.lease_allocations()==prior.lease_allocations()
        &&& forall|token:LeaseId| self.active_lease(token)==if leases.contains(token) {None} else {prior.active_lease(token)}
        &&& self.publications().len()==prior.publications().len()
        &&& forall|i:int| 0<=i<self.publications().len() ==> self.publications()[i]==
            if publications.contains(PublicationId(i as usize)) {
                Publication {retained:false,..prior.publications()[i]}
            } else {prior.publications()[i]}
        &&& released.len()==publications.len()
        &&& forall|i:int| 0<=i<released.len() ==> released[i].publication==publications[i]
            && released[i].slot==prior.publications()[publications[i].0 as int].slot
    }

    /// Validate the complete manifest before either leases or publications move.
    #[verifier::loop_isolation(false)]
    pub fn check_cleanup_batch(&self,owner:LeaseOwner,leases:&[LeaseId],publications:&[PublicationId])
        ->(out:Result<(),PublicationError>)
        requires self.wf(),
        ensures out.is_ok()==self.cleanup_batch_enabled(owner,leases@,publications@),
    {
        reveal(PublicationRegistry::active_lease);
        let mut i=0;
        while i<leases.len()
            invariant i<=leases.len(),
                forall|k:int| 0<=k<i ==> self.active_lease(leases[k]).is_some()
                    && self.active_lease(leases[k]).unwrap().consumer==Some(owner),
                forall|k:int,j:int| 0<=k<j<i ==> leases[k]!=leases[j],
            decreases leases.len()-i,
        {
            let token=leases[i];
            let entry=match self.lease(token) {Some(entry)=>entry,None=>return Err(PublicationError::Released)};
            if entry.consumer!=Some(owner) {return Err(PublicationError::InvalidState);}
            let mut j=0;
            while j<i
                invariant j<=i,i<leases.len(),forall|k:int| 0<=k<j ==> leases[k]!=token,
                decreases i-j,
            {
                if leases[j]==token {return Err(PublicationError::Conflict);}
                j+=1;
            }
            i+=1;
        }
        let mut i=0;
        while i<publications.len()
            invariant i<=publications.len(),
                forall|k:int| 0<=k<i ==> publications[k].0<self.publications().len()
                    && self.publications()[publications[k].0 as int].retained
                    && !self.publications()[publications[k].0 as int].visible
                    && self.publications()[publications[k].0 as int].owner==owner.owner
                    && self.publications()[publications[k].0 as int].generation==owner.generation,
                forall|k:int,j:int| 0<=k<j<i ==> publications[k]!=publications[j],
            decreases publications.len()-i,
        {
            let id=publications[i];
            let entry=match self.entry(id) {Some(entry)=>entry,None=>return Err(PublicationError::Unknown)};
            if !entry.retained {return Err(PublicationError::Released);}
            if entry.visible {return Err(PublicationError::Visible);}
            if entry.owner!=owner.owner || entry.generation!=owner.generation {return Err(PublicationError::InvalidState);}
            let mut j=0;
            while j<i
                invariant j<=i,i<publications.len(),forall|k:int| 0<=k<j ==> publications[k]!=id,
                decreases i-j,
            {
                if publications[j]==id {return Err(PublicationError::Conflict);}
                j+=1;
            }
            i+=1;
        }
        let mut i=0;
        while i<self.leases.len()
            invariant i<=self.leases.len(),
                forall|k:int| 0<=k<i ==> (publications@.contains(self.leases[k].lease.publication) || self.leases[k].lease.consumer==Some(owner)) ==> leases@.contains(self.leases[k].id),
            decreases self.leases.len()-i,
        {
            let record=self.leases[i];
            if (has_publication(publications,record.lease.publication) || record.lease.consumer==Some(owner)) && !has_lease(leases,record.id) {
                proof {self.lease_at_position(i as int);}
                return Err(PublicationError::Relied);
            }
            i+=1;
        }
        proof {
            assert forall|token:LeaseId| self.active_lease(token).is_some()
                && (publications@.contains(self.active_lease(token).unwrap().publication)
                    || self.active_lease(token).unwrap().consumer==Some(owner)) implies leases@.contains(token) by {
                let k=choose|k:int| 0<=k<self.leases.len() && self.leases[k].id==token;
                self.lease_at_position(k);
            }
        }
        let mut i=0;
        while i<self.entries.len()
            invariant i<=self.entries.len(),
                forall|k:int| 0<=k<i && self.entries[k].retained && self.entries[k].owner==owner.owner
                    && self.entries[k].generation==owner.generation ==> publications@.contains(PublicationId(k as usize)),
            decreases self.entries.len()-i,
        {
            let entry=self.entries[i];
            if entry.retained && entry.owner==owner.owner && entry.generation==owner.generation
                && !has_publication(publications,PublicationId(i)) {return Err(PublicationError::InvalidState);}
            i+=1;
        }
        Ok(())
    }

    /// A validated batch has no fallible mutation. On any rejection the whole
    /// registry is unchanged, including leases, visibility and allocation IDs.
    pub fn cleanup_batch(&mut self,owner:LeaseOwner,leases:&[LeaseId],publications:&[PublicationId])
        ->(out:Result<Vec<ReleasedPublication>,PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).domain_id()==old(self).domain_id(),out.is_ok()==old(self).cleanup_batch_enabled(owner,leases@,publications@),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> final(self).cleanup_batch_released(old(self),leases@,publications@,out.unwrap()@)
                && final(self).episode_resources_cleared(owner),
    {
        reveal(PublicationRegistry::active_lease);
        self.check_cleanup_batch(owner,leases,publications)?;
        let ghost prior=*self;
        let mut i=0;
        while i<leases.len()
            invariant self.wf(),self.domain_id()==prior.domain_id(),i<=leases.len(),self.publications()==prior.publications(),
                self.lease_allocations()==prior.lease_allocations(),prior.cleanup_batch_enabled(owner,leases@,publications@),
                forall|token:LeaseId| self.active_lease(token)==if leases@.subrange(0,i as int).contains(token) {None} else {prior.active_lease(token)},
            decreases leases.len()-i,
        {
            let token=leases[i];
            proof {
                assert(!leases@.subrange(0,i as int).contains(token)) by {
                    assert forall|k:int| 0<=k<i implies leases[k]!=token by {}
                }
            }
            let ghost before=*self;
            self.release(token).unwrap();
            proof {
                assert forall|key:LeaseId| self.active_lease(key)==if leases@.subrange(0,i as int+1).contains(key) {None} else {prior.active_lease(key)} by {
                    if key==token {assert(self.active_lease(key).is_none());}
                    else {assert(self.active_lease(key)==before.active_lease(key));}
                    prefix_member(leases@,i as int,key);
                    assert(before.active_lease(key)==if leases@.subrange(0,i as int).contains(key) {None} else {prior.active_lease(key)});
                    assert(leases@.subrange(0,i as int+1)==leases@.subrange(0,i as int).push(token));
                }
            }
            i+=1;
        }
        proof {
            assert(leases@.subrange(0,leases.len() as int)==leases@);
            assert forall|k:int| 0<=k<publications.len() implies self.unleased(publications[k]) by {
                assert forall|j:int| 0<=j<self.leases.len() implies self.leases[j].lease.publication!=publications[k] by {
                    let token=self.leases[j].id;
                    self.lease_at_position(j);
                    if self.leases[j].lease.publication==publications[k] {
                        assert(prior.active_lease(token).is_some());
                        assert(leases@.contains(token));
                        assert(false);
                    }
                }
            }
        }
        let ghost after_leases=*self;
        let mut released:Vec<ReleasedPublication>=Vec::new();
        let mut i=0;
        while i<publications.len()
            invariant self.wf(),self.domain_id()==prior.domain_id(),i<=publications.len(),released.len()==i,
                prior.cleanup_batch_enabled(owner,leases@,publications@),
                self.lease_records()==after_leases.lease_records(),self.lease_allocations()==prior.lease_allocations(),
                forall|token:LeaseId| self.active_lease(token)==if leases@.contains(token) {None} else {prior.active_lease(token)},
                forall|k:int| 0<=k<publications.len() ==> self.unleased(publications[k]),
                self.publications().len()==prior.publications().len(),self.publications().len()<=usize::MAX,
                forall|k:int| 0<=k<self.publications().len() ==> self.publications()[k]==
                    if publications@.subrange(0,i as int).contains(PublicationId(k as usize)) {Publication {retained:false,..prior.publications()[k]}} else {prior.publications()[k]},
                forall|k:int| 0<=k<i ==> released[k].publication==publications[k] && released[k].slot==prior.publications()[publications[k].0 as int].slot,
            decreases publications.len()-i,
        {
            let id=publications[i];
            proof {
                assert(!publications@.subrange(0,i as int).contains(id)) by {
                    assert forall|k:int| 0<=k<i implies publications[k]!=id by {}
                }
            }
            let ghost before=*self;
            assert(self.publications()[id.0 as int]==prior.publications()[id.0 as int]);
            let slot=self.reclaim(id).unwrap();
            proof {self.same_lease_projection(&before);}
            released.push(ReleasedPublication {publication:id,slot});
            proof {
                assert forall|k:int| 0<=k<self.publications().len() implies self.publications()[k]==
                    if publications@.subrange(0,i as int+1).contains(PublicationId(k as usize)) {Publication {retained:false,..prior.publications()[k]}} else {prior.publications()[k]} by {
                    if k==id.0 {assert(self.publications()[k]==Publication {retained:false,..before.publications()[k]});}
                    else {assert(self.publications()[k]==before.publications()[k]);}
                    prefix_member(publications@,i as int,PublicationId(k as usize));
                    assert(before.publications()[k]==if publications@.subrange(0,i as int).contains(PublicationId(k as usize)) {Publication {retained:false,..prior.publications()[k]}} else {prior.publications()[k]});
                    assert(publications@.subrange(0,i as int+1)==publications@.subrange(0,i as int).push(id));
                }
            }
            i+=1;
        }
        assert(publications@.subrange(0,publications.len() as int)==publications@);
        proof {self.batch_clears_episode(&prior,owner,leases@,publications@,released@);}
        Ok(released)
    }
}
}
