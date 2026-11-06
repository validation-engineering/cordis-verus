//! Episode-owned publication mutations used by the real Node command adapter.
//! Admission and ownership checks stay with the state they authorize. Cleanup
//! may revoke/reclaim an old visible choice while its own generation is current.
#[cfg(verus_keep_ghost)]
use super::interfaces::{batch_result, prefix, prefix_append, prefix_reflexive, prefix_transitive};
use super::*;
use crate::publication::Publication;

verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum ServiceError {
    Access(EpisodeError),
    StalePublication,
    Publication(PublicationError),
    Declaration(Error),
}

pub open spec fn ownership(a:Observation,owner:usize,generation:u64,id:PublicationId)->Result<Publication,ServiceError> {
    let publications=a.store.registry_view().publications();
    if id.0>=publications.len() {Err(ServiceError::Publication(PublicationError::Unknown))}
    else {
        let p=publications[id.0 as int];
        if p.owner!=owner || p.generation!=generation || a.control.control().generation_of(owner)!=Some(generation) {
            Err(ServiceError::StalePublication)
        } else {Ok(p)}
    }
}
pub open spec fn replacement_guard(a:Observation,owner:usize,generation:u64,id:PublicationId)->Result<(),ServiceError> {
    match episode::validation(a,owner,generation) {
        Err(e)=>Err(ServiceError::Access(e)),
        Ok(())=>match ownership(a,owner,generation,id) {
            Err(e)=>Err(e),Ok(p)=>if !p.visible {Err(ServiceError::Publication(PublicationError::Revoked))} else {Ok(())},
        },
    }
}
pub open spec fn appended(a:History,b:History,event:Event)->bool {b==a.append(b.states.last(),event)}

#[verifier::opaque]
pub open spec fn service_replaced(a:History,b:History,owner:usize,generation:u64,id:PublicationId,value:u64,out:Result<(),ServiceError>)->bool {
    prefix(a,b) && match replacement_guard(a.states.last(),owner,generation,id) {
        Err(e)=>b==a && out==Err(e),
        Ok(())=>exists|reply:Result<u64,RejectedValue<u64>>|
            appended(a,b,Event::Replace {id,owner,generation,value,out:reply})
                && out==match reply {Ok(_)=>Ok(()),Err(e)=>Err(ServiceError::Publication(e.error))},
    }
}
#[verifier::opaque]
pub open spec fn service_revoked(a:History,b:History,owner:usize,generation:u64,id:PublicationId,out:Result<(),ServiceError>)->bool {
    prefix(a,b) && match ownership(a.states.last(),owner,generation,id) {
        Err(e)=>b==a && out==Err(e),
        Ok(_)=>exists|reply:Result<(),PublicationError>|
            appended(a,b,Event::Revoke {id,restoring:false,out:reply})
                && out==match reply {Ok(())=>Ok(()),Err(e)=>Err(ServiceError::Publication(e))},
    }
}
/// Checked bookkeeping and the complete dynamic-port reconciliation follow the
/// actual reclaim. A later declaration error keeps this real partial prefix.
pub open spec fn reclaim_tail(a:History,b:History,id:PublicationId,out:Result<bool,ServiceError>)->bool {
    exists|checked:History,ports:Seq<Port>,runs:Seq<History>,results:Seq<Result<(),Error>>,result:Result<(),Error>|
        appended(a,checked,Event::Checked {publication:id.0,enabled:false}) && prefix(checked,b)
            && batch_result(checked,b,ports,runs,results,result)
            && out==match result {Ok(())=>Ok(true),Err(e)=>Err(ServiceError::Declaration(e))}
}
#[verifier::opaque]
pub open spec fn service_reclaimed(a:History,b:History,owner:usize,generation:u64,id:PublicationId,out:Result<bool,ServiceError>)->bool {
    prefix(a,b) && match ownership(a.states.last(),owner,generation,id) {
        Err(e)=>b==a && out==Err(e),
        Ok(p)=>if !p.retained {b==a && out==Ok(true)} else {
            exists|reclaimed:History,reply:Result<u64,PublicationError>|
                appended(a,reclaimed,Event::Reclaim {id,out:reply}) && prefix(reclaimed,b)
                    && match reply {
                        Err(PublicationError::Relied)=>b==reclaimed && out==Ok(false),
                        Err(e)=>b==reclaimed && out==Err(ServiceError::Publication(e)),
                        Ok(_)=>reclaim_tail(reclaimed,b,id,out),
                    }
        },
    }
}
impl NodeRuntime {
    fn owned_publication(&self,owner:usize,generation:u64,id:PublicationId)->(out:Result<Publication,ServiceError>)
        requires self.wf(),
        ensures out==ownership(self.observation(),owner,generation,id),
    {
        let p=match self.store.registry().entry(id) {
            Some(p)=>p,None=>return Err(ServiceError::Publication(PublicationError::Unknown)),
        };
        if p.owner!=owner || p.generation!=generation || self.control.kernel().episode_generation(owner)!=Some(generation) {
            return Err(ServiceError::StalePublication);
        }
        Ok(p)
    }
    pub(super) fn check_replacement(&self,owner:usize,generation:u64,id:PublicationId)->(out:Result<(),ServiceError>)
        requires self.wf(),ensures out==replacement_guard(self.observation(),owner,generation,id),
    {
        if let Err(e)=self.validate(owner,generation) {return Err(ServiceError::Access(e));}
        let p=self.owned_publication(owner,generation,id)?;
        if !p.visible {return Err(ServiceError::Publication(PublicationError::Revoked));}
        Ok(())
    }
    // Shared by metadata and real object-table writes. The exclusive Node borrow
    // retains the admission checked before object-key validation; no token escapes.
    pub(super) fn replace_admitted(&mut self,owner:usize,generation:u64,id:PublicationId,value:u64)->(out:Result<(),ServiceError>)
        requires old(self).wf(),replacement_guard(old(self).observation(),owner,generation,id)==Ok(()),
        ensures final(self).wf(),service_replaced(old(self).history(),final(self).history(),owner,generation,id,value,out),
    {
        let ghost before=self.history();
        let result=self.replace(id,owner,generation,value);
        proof {
            reveal(service_replaced);
            prefix_append(before,self.observation(),Event::Replace {id,owner,generation,value,out:result});
            assert(appended(before,self.history(),Event::Replace {id,owner,generation,value,out:result}));
        }
        let out=match result {Ok(_)=>Ok(()),Err(e)=>Err(ServiceError::Publication(e.error))};
        proof {
            assert(exists|reply:Result<u64,RejectedValue<u64>>|
                appended(before,self.history(),Event::Replace {id,owner,generation,value,out:reply})
                    && out==match reply {Ok(_)=>Ok(()),Err(e)=>Err(ServiceError::Publication(e.error))});
        }
        out
    }
    /// New writes require an open episode before publication ownership is read.
    /// Rejection preserves the exact history, including diagnostic precedence.
    pub fn replace_service(&mut self,owner:usize,generation:u64,id:PublicationId,value:u64)->(out:Result<(),ServiceError>)
        requires old(self).wf(),
        ensures final(self).wf(),service_replaced(old(self).history(),final(self).history(),owner,generation,id,value,out),
            replacement_guard(old(self).observation(),owner,generation,id).is_err() ==>
                final(self).observation()==old(self).observation() && final(self).history()==old(self).history(),
    {
        proof {reveal(service_replaced);prefix_reflexive(self.history());}
        self.check_replacement(owner,generation,id)?;
        self.replace_admitted(owner,generation,id,value)
    }
    /// Revocation during cleanup is allowed; current owner/generation still
    /// comes from this same state, not a host-supplied ownership assertion.
    pub fn revoke_service(&mut self,owner:usize,generation:u64,id:PublicationId)->(out:Result<(),ServiceError>)
        requires old(self).wf(),
        ensures final(self).wf(),service_revoked(old(self).history(),final(self).history(),owner,generation,id,out),
            ownership(old(self).observation(),owner,generation,id).is_err() ==>
                final(self).observation()==old(self).observation() && final(self).history()==old(self).history(),
    {
        let ghost before=self.history();
        proof {reveal(service_revoked);prefix_reflexive(before);}
        self.owned_publication(owner,generation,id)?;
        let result=self.revoke(id);
        proof {
            prefix_append(before,self.observation(),Event::Revoke {id,restoring:false,out:result});
            assert(appended(before,self.history(),Event::Revoke {id,restoring:false,out:result}));
        }
        let out=match result {Ok(())=>Ok(()),Err(e)=>Err(ServiceError::Publication(e))};
        proof {
            assert(exists|reply:Result<(),PublicationError>|
                appended(before,self.history(),Event::Revoke {id,restoring:false,out:reply})
                    && out==match reply {Ok(())=>Ok(()),Err(e)=>Err(ServiceError::Publication(e))});
        }
        out
    }
    /// Retained leases block reclamation. Already reclaimed slots are
    /// idempotent; only a real successful reclaim clears checks/reconciles ports.
    pub fn reclaim_service(&mut self,owner:usize,generation:u64,id:PublicationId)->(out:Result<bool,ServiceError>)
        requires old(self).wf(),
        ensures final(self).wf(),service_reclaimed(old(self).history(),final(self).history(),owner,generation,id,out),
            ownership(old(self).observation(),owner,generation,id).is_err() ==>
                final(self).observation()==old(self).observation() && final(self).history()==old(self).history(),
    {
        let ghost before=self.history();
        proof {reveal(service_reclaimed);prefix_reflexive(before);}
        let p=self.owned_publication(owner,generation,id)?;
        if !p.retained {return Ok(true);}
        let result=self.reclaim(id);
        let ghost reclaimed=self.history();
        proof {
            prefix_append(before,self.observation(),Event::Reclaim {id,out:result});prefix_reflexive(reclaimed);
            assert(appended(before,reclaimed,Event::Reclaim {id,out:result}));
        }
        match result {
            Err(PublicationError::Relied)=>return Ok(false),
            Err(e)=>return Err(ServiceError::Publication(e)),
            Ok(_)=>{},
        }
        self.set_checked(id.0,false);
        let ghost checked=self.history();
        proof {prefix_append(reclaimed,self.observation(),Event::Checked {publication:id.0,enabled:false});}
        let result=self.reconcile_declarations();
        proof {prefix_transitive(reclaimed,checked,self.history());prefix_transitive(before,reclaimed,self.history());}
        let out=match result {Ok(())=>Ok(true),Err(e)=>Err(ServiceError::Declaration(e))};
        proof {
            assert(reclaim_tail(reclaimed,self.history(),id,out));
            assert(exists|mid:History,r:Result<u64,PublicationError>|
                appended(before,mid,Event::Reclaim {id,out:r}) && prefix(mid,self.history())
                    && match r {
                        Err(PublicationError::Relied)=>self.history()==mid && out==Ok(false),
                        Err(e)=>self.history()==mid && out==Err(ServiceError::Publication(e)),
                        Ok(_)=>reclaim_tail(mid,self.history(),id,out),
                    });
        }
        out
    }
}
}
