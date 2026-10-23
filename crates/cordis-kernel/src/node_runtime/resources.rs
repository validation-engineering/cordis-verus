//! Publication lists are derived from the real registry. The checked owner
//! also retains the actual withdrawn lookup selection used during cleanup.
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::seq_lib::*;

verus! {
pub open spec fn selected(a:Observation,owner:usize,id:PublicationId,visible:bool)->bool {
    id.0<a.store.registry_view().publications().len() && {
        let p=a.store.registry_view().publications()[id.0 as int];
        p.owner==owner && p.retained && (!visible || p.visible)
    }
}
pub open spec fn manifest(a:Observation,owner:usize,ids:Seq<PublicationId>,visible:bool)->bool {
    ids.len()<=a.store.registry_view().publications().len()
        && (forall|i:int|0<=i<ids.len() ==> selected(a,owner,ids[i],visible))
        && (forall|i:int,j:int|0<=i<j<ids.len() ==> ids[i].0<ids[j].0)
        && (forall|id:PublicationId|ids.contains(id)==selected(a,owner,id,visible))
}
pub open spec fn keep_id(id:PublicationId)->spec_fn(PublicationId)->bool {|p:PublicationId|p!=id}
pub open spec fn forgotten(a:Map<usize,Vec<PublicationId>>,b:Map<usize,Vec<PublicationId>>,owner:usize,id:PublicationId)->bool {
    if a.contains_key(owner) {
        b.contains_key(owner) && b==a.insert(owner,b[owner]) && b[owner]@==a[owner]@.filter(keep_id(id))
    } else {b==a}
}
pub open spec fn step(a:Observation,b:Observation,event:Event)->bool {
    match event {
        Event::RememberPublications {owner,publications}=>manifest(a,owner,publications,true)
            && b.restoring.contains_key(owner) && b.restoring==a.restoring.insert(owner,b.restoring[owner]) && b.restoring[owner]@==publications,
        Event::Revoke {id,restoring,out}=>if out.is_ok() && !restoring {
            id.0<a.store.values().len() && forgotten(a.restoring,b.restoring,a.store.registry_view().publications()[id.0 as int].owner,id)
        } else {b.restoring==a.restoring},
        Event::Reclaim {id,out}=>if out.is_ok() {
            id.0<a.store.values().len() && forgotten(a.restoring,b.restoring,a.store.registry_view().publications()[id.0 as int].owner,id)
        } else {b.restoring==a.restoring},
        Event::Release {id,out,..}|Event::ReleaseReservation {id,out,..}=>b.restoring==if out.is_ok() {a.restoring.remove(id)} else {a.restoring},
        Event::Cleanup {command:CleanupCommand::Remove {id},out,..}=>b.restoring==if out.is_ok() {a.restoring.remove(id)} else {a.restoring},
        _=>b.restoring==a.restoring,
    }
}
impl NodeRuntime {
    /// Stable publication IDs in allocation order, including invisible retained
    /// versions. The list is computed from authoritative records, not host input.
    pub fn publications(&self,owner:usize)->(out:Vec<PublicationId>)
        requires self.wf(),ensures manifest(self.observation(),owner,out@,false),
    {self.publication_manifest(owner,false)}
    fn publication_manifest(&self,owner:usize,visible:bool)->(out:Vec<PublicationId>)
        requires self.wf(),ensures manifest(self.observation(),owner,out@,visible),
    {
        let count=self.store.registry().publication_records();let mut out:Vec<PublicationId>=Vec::new();let mut i=0;
        while i<count
            invariant self.wf(),count==self.observation().store.registry_view().publications().len(),i<=count,out.len()<=i,
                forall|j:int|0<=j<out.len() ==> out[j].0<i && selected(self.observation(),owner,out[j],visible),
                forall|j:int,k:int|0<=j<k<out.len() ==> out[j].0<out[k].0,
                forall|id:PublicationId|out@.contains(id)==(id.0<i && selected(self.observation(),owner,id,visible)),
            decreases count-i,
        {
            let id=PublicationId(i);let p=self.store.registry().entry(id).unwrap();let ghost prior=out@;
            if p.owner==owner && p.retained && (!visible || p.visible) {out.push(id);}
            proof {
                assert forall|q:PublicationId|out@.contains(q)==(q.0<i+1 && selected(self.observation(),owner,q,visible)) by {
                    assert(prior.contains(q)==(q.0<i && selected(self.observation(),owner,q,visible)));
                    if q.0==i {assert(q==id);}
                    if out@.contains(q) && out@!=prior {
                        let j=choose|j:int|0<=j<out.len() && out[j]==q;
                        if j<prior.len() {assert(prior[j]==q);assert(prior.contains(q));} else {assert(q==id);}
                    }
                    if prior.contains(q) {
                        let j=choose|j:int|0<=j<prior.len() && prior[j]==q;
                        assert(out[j]==q);assert(out@.contains(q));
                    }
                    if selected(self.observation(),owner,id,visible) {assert(out[out.len()-1]==id);assert(out@.contains(id));}
                }
            }
            i+=1;
        }
        out
    }
    pub fn restoring_publications(&self,owner:usize)->(out:Option<&Vec<PublicationId>>)
        ensures out.is_some()==self.observation().restoring.contains_key(owner),out.is_some() ==> *out.unwrap()==self.observation().restoring[owner],
    {self.restoring.get(&owner)}
    fn remember_publications(&mut self,owner:usize)
        requires old(self).wf(),ensures final(self).wf(),final(self).store==old(self).store,final(self).control==old(self).control,
            final(self).restoring@.contains_key(owner) && manifest(old(self).observation(),owner,final(self).restoring@[owner]@,true),
            exists|ids:Seq<PublicationId>|manifest(old(self).observation(),owner,ids,true)
                && final(self).history()==old(self).history().append(final(self).observation(),Event::RememberPublications {owner,publications:ids}),
    {
        let ghost before=self.observation();let ids=self.publication_manifest(owner,true);let ghost saved=ids@;
        self.restoring.insert(owner,ids);
        proof {self.scopes.unchanged_reflexive();reveal(history::operation);self.record(before,Event::RememberPublications {owner,publications:saved});}
    }
    /// Capture visible own slots, then hide all retained versions from new
    /// lookup. The capture and every actual revocation enter the same history.
    pub fn withdraw_publications(&mut self,owner:usize)->(out:Result<(),PublicationError>)
        requires old(self).wf(),ensures final(self).wf(),out.is_ok(),
            final(self).observation().control==old(self).observation().control,final(self).observation().store.values()==old(self).observation().store.values(),
            final(self).observation().store.revisions()==old(self).observation().store.revisions(),final(self).observation().store.lease_frame(&old(self).observation().store),
            final(self).observation().restoring.contains_key(owner) && manifest(old(self).observation(),owner,final(self).observation().restoring[owner]@,true),
            final(self).observation().store.registry_view().publications().len()==old(self).observation().store.registry_view().publications().len(),
            forall|k:int|0<=k<old(self).observation().store.registry_view().publications().len() ==> final(self).observation().store.registry_view().publications()[k]==
                if selected(old(self).observation(),owner,PublicationId(k as usize),false) {
                    crate::publication::Publication {visible:false,..old(self).observation().store.registry_view().publications()[k]}
                } else {old(self).observation().store.registry_view().publications()[k]},
            final(self).history().events.take(old(self).history().events.len() as int)==old(self).history().events,
            final(self).history().states.take(old(self).history().states.len() as int)==old(self).history().states,
    {
        let ghost before=self.observation();let ghost initial=self.history();
        let ids=self.publications(owner);self.remember_publications(owner);let ghost captured=self.restoring@;
        proof {self.store.slot_count();}
        let mut i=0;
        while i<ids.len()
            invariant self.wf(),i<=ids.len(),manifest(before,owner,ids@,false),before.store.wf(),
                before.store.values().len()==before.store.registry_view().publications().len(),before.store.values().len()<=usize::MAX,
                self.control==before.control,self.store.values()==before.store.values(),self.store.revisions()==before.store.revisions(),self.store.lease_frame(&before.store),
                self.restoring@==captured,captured.contains_key(owner) && manifest(before,owner,captured[owner]@,true),
                self.store.registry_view().publications().len()==before.store.registry_view().publications().len(),
                forall|k:int|0<=k<before.store.registry_view().publications().len() ==> self.store.registry_view().publications()[k]==
                    if ids@.take(i as int).contains(PublicationId(k as usize)) {crate::publication::Publication {visible:false,..before.store.registry_view().publications()[k]}} else {before.store.registry_view().publications()[k]},
                self.history().events.len()==initial.events.len()+1+i,self.history().states.len()==initial.states.len()+1+i,
                self.history().events.take(initial.events.len() as int)==initial.events,self.history().states.take(initial.states.len() as int)==initial.states,
            decreases ids.len()-i,
        {
            let ghost prior_publications=self.store.registry_view().publications();
            let current=ids[i];let result=self.revoke_with_restoring(current,true);
            proof {
                assert(result.is_ok());
                assert forall|k:int|0<=k<before.store.registry_view().publications().len() implies self.store.registry_view().publications()[k]==
                    if ids@.take(i as int+1).contains(PublicationId(k as usize)) {crate::publication::Publication {visible:false,..before.store.registry_view().publications()[k]}} else {before.store.registry_view().publications()[k]} by {
                    let id=PublicationId(k as usize);
                    crate::publication::cleanup::prefix_member(ids@,i as int,id);
                    assert(prior_publications[k]==if ids@.take(i as int).contains(id) {crate::publication::Publication {visible:false,..before.store.registry_view().publications()[k]}} else {before.store.registry_view().publications()[k]});
                    if current.0==k {
                        assert(current==id);assert(ids@.take(i as int+1).contains(id));
                        assert(self.store.registry_view().publications()[k]==crate::publication::Publication {visible:false,..prior_publications[k]});
                    } else {assert(current!=id);assert(self.store.registry_view().publications()[k]==prior_publications[k]);}
                }
                assert(self.history().events.take(initial.events.len() as int) =~= initial.events);
                assert(self.history().states.take(initial.states.len() as int) =~= initial.states);
            }
            result?;i+=1;
        }
        assert(ids@.take(i as int)==ids@);
        Ok(())
    }
    pub(super) fn forget_restoring(&mut self,id:PublicationId)
        requires old(self).store.wf(),
        ensures final(self).policy==old(self).policy,final(self).interfaces==old(self).interfaces,final(self).dynamic==old(self).dynamic,final(self).released@==old(self).released@,final(self).control==old(self).control,final(self).store==old(self).store,final(self).checks==old(self).checks,
            final(self).checked==old(self).checked,final(self).admissions==old(self).admissions,final(self).episodes==old(self).episodes,
            final(self).scopes==old(self).scopes,final(self).history()==old(self).history(),
            if id.0<old(self).store.registry_view().publications().len() {
                forgotten(old(self).restoring@,final(self).restoring@,old(self).store.registry_view().publications()[id.0 as int].owner,id)
            } else {final(self).restoring@==old(self).restoring@},
    {
        if let Some(p)=self.store.registry().entry(id) {
            if let Some(ids)=self.restoring.get(&p.owner) {
                let ghost keep=keep_id(id);
                proof {reveal(Seq::filter);}
                let mut kept:Vec<PublicationId>=Vec::new();let mut i=0;
                while i<ids.len()
                    invariant i<=ids.len(),kept.len()<=i,kept@==ids@.subrange(0,i as int).filter(keep),
                        forall|p:PublicationId|#[trigger] keep(p)==(p!=id),
                    decreases ids.len()-i,
                {
                    proof {
                        let prefix=ids@.subrange(0,i as int);
                        assert(ids@.subrange(0,i+1) =~= prefix.push(ids[i as int]));
                        prefix.lemma_filter_push(ids[i as int],keep);
                    }
                    if ids[i]!=id {kept.push(ids[i]);}i+=1;
                }
                assert(ids@.subrange(0,i as int)==ids@);
                assert(keep==keep_id(id));
                assert(kept@==ids@.filter(keep_id(id)));
                self.restoring.insert(p.owner,kept);
                assert(self.restoring@.contains_key(p.owner));
                assert(self.restoring@ =~= old(self).restoring@.insert(p.owner,self.restoring@[p.owner]));
                assert(self.restoring@[p.owner]@==old(self).restoring@[p.owner]@.filter(keep_id(id)));
                reveal(forgotten);
                assert(forgotten(old(self).restoring@,self.restoring@,p.owner,id));
            }
        }
    }
    /// Host adapters do not supply release manifests. All retained own slots,
    /// including withdrawn versions, are checked in the actual release call.
    pub fn release_owned(&mut self,id:usize)->(out:Result<Vec<ReleasedValue<u64>>,CleanupReleaseError>)
        requires old(self).wf(),ensures final(self).wf(),
            exists|ids:Seq<PublicationId>|manifest(old(self).observation(),id,ids,false)
                && final(self).history()==old(self).history().append(final(self).observation(),Event::Release {id,publications:ids,out}),
    {let ids=self.publications(id);self.release(id,ids.as_slice())}
    pub fn release_owned_reservation(&mut self,id:usize)->(out:Result<Vec<ReleasedValue<u64>>,CleanupReleaseError>)
        requires old(self).wf(),ensures final(self).wf(),
            exists|ids:Seq<PublicationId>|manifest(old(self).observation(),id,ids,false)
                && final(self).history()==old(self).history().append(final(self).observation(),Event::ReleaseReservation {id,publications:ids,out}),
    {let ids=self.publications(id);self.release_reservation(id,ids.as_slice())}
}
impl History {
    pub open spec fn release_owner(&self,index:int)->usize {match self.events[index] {Event::Release {id,..}|Event::ReleaseReservation {id,..}=>id,_=>0}}
    pub open spec fn publication_issued_at(&self,index:int,id:PublicationId,owner:usize,port:Port)->bool {
        0<=index<self.events.len() && match self.events[index] {
            Event::Publish {owner:actual,port:actual_port,out,..}=>out.is_ok() && out->Ok_0==id && actual==owner && actual_port==port,
            _=>false,
        }
    }
    /// Every real slot, including a withdrawn/reclaimed tombstone, comes from
    /// an actual successful publication here. Adoption never changes its owner.
    pub proof fn publication_origin(&self,end:int,id:PublicationId)
        requires self.valid(),0<=end<self.states.len(),id.0<self.states[end].store.registry_view().publications().len(),
        ensures exists|issued:int|0<=issued<end && self.publication_issued_at(issued,id,
            self.states[end].store.registry_view().publications()[id.0 as int].owner,
            self.states[end].store.registry_view().publications()[id.0 as int].port),
        decreases end,
    {
        assert(end>0);let i=end-1;
        assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
        let a=self.states[i];let b=self.states[i+1];
        if b.store.same(&a.store) {b.store.same_observations(&a.store);}
        if b.store.registry_view().unchanged(&a.store.registry_view()) {b.store.registry_view().unchanged_observations(&a.store.registry_view());}
        a.store.slot_count();b.store.slot_count();
        match self.events[i] {
            Event::Publish {out,..} if out.is_ok() && out->Ok_0==id=>{
                assert(self.publication_issued_at(i,id,b.store.registry_view().publications()[id.0 as int].owner,b.store.registry_view().publications()[id.0 as int].port));
            },
            _=>{
                assert(id.0<a.store.registry_view().publications().len());
                assert(a.store.registry_view().publications()[id.0 as int].owner==b.store.registry_view().publications()[id.0 as int].owner);
                assert(a.store.registry_view().publications()[id.0 as int].port==b.store.registry_view().publications()[id.0 as int].port);
                self.publication_origin(i,id);
            },
        }
    }
    /// A cleanup lookup selection originates in a real capture while that slot
    /// was visible. Later revocation/reclamation can only remove selections.
    pub proof fn restoring_origin(&self,end:int,owner:usize,id:PublicationId)
        requires self.valid(),0<=end<self.states.len(),self.states[end].restoring.contains_key(owner),self.states[end].restoring[owner]@.contains(id),
        ensures exists|captured:int|0<=captured<end && self.events[captured] is RememberPublications
            && self.events[captured]->RememberPublications_owner==owner
            && self.events[captured]->RememberPublications_publications.contains(id)
            && selected(self.states[captured],owner,id,true),
        decreases end,
    {
        assert(end>0);let i=end-1;
        assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
        let a=self.states[i];let b=self.states[i+1];
        match self.events[i] {
            Event::RememberPublications {owner:actual,publications} if actual==owner=>{
                assert(publications.contains(id));assert(selected(a,owner,id,true));
            },
            _=>{
                assert(a.restoring.contains_key(owner));
                if b.restoring[owner]@!=a.restoring[owner]@ {
                    let q=match self.events[i] {Event::Revoke {id,..}|Event::Reclaim {id,..}=>id,_=>id};
                    a.restoring[owner]@.lemma_filter_contains_rev(keep_id(q),id);
                }
                assert(a.restoring[owner]@.contains(id));self.restoring_origin(i,owner,id);
            },
        }
    }
    /// Release is about real publications of this owner, never identifiers
    /// invented by a supplied manifest. Completeness remains checked at release.
    pub proof fn released_publication_has_origin(&self,index:int,id:PublicationId)
        requires self.valid(),0<=index<self.events.len(),match self.events[index] {
            Event::Release {publications,out,..}|Event::ReleaseReservation {publications,out,..}=>out.is_ok() && publications.contains(id),_=>false},
        ensures exists|issued:int|0<=issued<index && #[trigger] self.publication_issued_at(issued,id,
            self.release_owner(index),
            self.states[index].store.registry_view().publications()[id.0 as int].port),
    {
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
        let publications=match self.events[index] {Event::Release {publications,..}|Event::ReleaseReservation {publications,..}=>publications,_=>Seq::empty()};
        let j=choose|j:int|0<=j<publications.len() && publications[j]==id;
        assert(self.states[index].store.registry_view().publications()[id.0 as int].owner==self.release_owner(index));
        self.publication_origin(index,id);
        let issued=choose|issued:int|0<=issued<index && self.publication_issued_at(issued,id,
            self.states[index].store.registry_view().publications()[id.0 as int].owner,
            self.states[index].store.registry_view().publications()[id.0 as int].port);
        assert(self.publication_issued_at(issued,id,self.release_owner(index),self.states[index].store.registry_view().publications()[id.0 as int].port));
    }
}

}
