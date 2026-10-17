//! Actual service reads, including committed and withdrawn cleanup views.
//! Returned handles name host objects; their interiors and invocation remain
//! outside this contract. Read events are erased from executable Rust.
use super::*;
#[cfg(verus_keep_ghost)]
use crate::availability::admission::ResourceBinding;

verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum ReadError {Unknown,Stale}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Source {Root,Own,Committed {binding:usize},Restoring {index:usize}}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Read {
    pub publication:PublicationId,pub owner:usize,pub value:u64,pub revision:u64,pub source:Source,
}
pub open spec fn bindings(a:Observation,consumer:usize)->Seq<ResourceBinding> {
    if a.admissions.contains_key(consumer) {a.admissions[consumer].resources_view()} else {Seq::empty()}
}
pub open spec fn first_binding(rs:Seq<ResourceBinding>,port:Port)->Option<usize> {
    if exists|i:int|0<=i<rs.len() && rs[i].port==port {
        Some((choose|i:int|0<=i<rs.len() && rs[i].port==port
            && forall|j:int|0<=j<i ==> rs[j].port!=port) as usize)
    } else {None}
}
pub open spec fn visible(a:Observation,port:Port,id:PublicationId)->bool {
    id.0<a.store.registry_view().publications().len()
        && a.store.registry_view().publications()[id.0 as int].visible
        && a.store.registry_view().publications()[id.0 as int].port==port
}
pub open spec fn visible_choice(a:Observation,port:Port)->Option<PublicationId> {
    if exists|id:PublicationId|visible(a,port,id) {Some(choose|id:PublicationId|visible(a,port,id))} else {None}
}
pub open spec fn restorable(a:Observation,consumer:usize,port:Port,index:int)->bool {
    a.restoring.contains_key(consumer) && 0<=index<a.restoring[consumer].len() && {
        let p=a.restoring[consumer][index];
        p.0<a.store.registry_view().publications().len()
            && a.store.registry_view().publications()[p.0 as int].retained
            && a.store.registry_view().publications()[p.0 as int].port==port
    }
}
pub open spec fn last_restoring(a:Observation,consumer:usize,port:Port)->Option<usize> {
    if exists|i:int|restorable(a,consumer,port,i) {
        Some((choose|i:int|restorable(a,consumer,port,i)
            && forall|j:int|i<j<a.restoring[consumer].len() ==> !restorable(a,consumer,port,j)) as usize)
    } else {None}
}
#[verifier::opaque]
pub open spec fn selection(a:Observation,port:Port,consumer:Option<usize>)->Option<(PublicationId,Source)> {
    let current=visible_choice(a,port);
    match consumer {
        Some(id)=>{
            let bound=first_binding(bindings(a,id),port);
            if bound.is_some() {
                Some((bindings(a,id)[bound.unwrap() as int].publication,Source::Committed {binding:bound.unwrap()}))
            } else if current.is_some() && a.store.registry_view().publications()[current.unwrap().0 as int].owner==id {
                Some((current.unwrap(),Source::Own))
            } else {
                let saved=last_restoring(a,id,port);
                if saved.is_some() {Some((a.restoring[id][saved.unwrap() as int],Source::Restoring {index:saved.unwrap()}))} else {None}
            }
        },
        None=>if current.is_some()
            && a.control.control().phase_of(a.store.registry_view().publications()[current.unwrap().0 as int].owner)==Some(Phase::Active)
            && !a.control.control().is_retired(a.store.registry_view().publications()[current.unwrap().0 as int].owner) {
                Some((current.unwrap(),Source::Root))
            } else {None},
    }
}
pub open spec fn materialized(a:Observation,id:PublicationId,source:Source)->Read {
    Read {publication:id,owner:a.store.registry_view().publications()[id.0 as int].owner,
        value:a.store.values()[id.0 as int].unwrap(),revision:a.store.revisions()[id.0 as int],source}
}
#[verifier::opaque]
pub open spec fn result(a:Observation,port:Port,consumer:Option<usize>,generation:Option<u64>)->Result<Option<Read>,ReadError> {
    if consumer.is_some() && !a.control.control().registered(consumer.unwrap()) {Err(ReadError::Unknown)}
    else if consumer.is_some() && generation.is_some() && a.control.control().generation_of(consumer.unwrap())!=generation {Err(ReadError::Stale)}
    else {
        let selected=selection(a,port,consumer);
        Ok(if selected.is_some() {Some(materialized(a,selected.unwrap().0,selected.unwrap().1))} else {None})
    }
}
pub open spec fn valid_read(a:Observation,r:Read)->bool {
    r.publication.0<a.store.registry_view().publications().len()
        && r.publication.0<a.store.values().len() && r.publication.0<a.store.revisions().len()
        && a.store.registry_view().publications()[r.publication.0 as int].retained
        && a.store.values()[r.publication.0 as int]==Some(r.value)
        && r==materialized(a,r.publication,r.source)
}

#[verifier::spinoff_prover]
pub proof fn first_binding_facts(rs:Seq<ResourceBinding>,port:Port)
    requires rs.len()<=usize::MAX,
    ensures first_binding(rs,port).is_some()==(exists|i:int|0<=i<rs.len() && rs[i].port==port),
        first_binding(rs,port).is_some() ==> {
            let i=first_binding(rs,port).unwrap() as int;
            0<=i<rs.len() && rs[i].port==port && forall|j:int|0<=j<i ==> rs[j].port!=port
        },
{
    let matched=rs.map(|_:int,r:ResourceBinding|r.port==port);matched.index_of_first_ensures(true);
    if exists|i:int|0<=i<rs.len() && rs[i].port==port {
        let j=choose|i:int|0<=i<rs.len() && rs[i].port==port;
        assert(matched[j]);assert(matched.contains(true));
        let i=matched.index_of_first(true).unwrap();
        assert(0<=i<rs.len() && rs[i].port==port);
        assert forall|j:int|0<=j<i implies rs[j].port!=port by {assert(!matched[j]);}
        assert(exists|i:int|0<=i<rs.len() && rs[i].port==port && forall|j:int|0<=j<i ==> rs[j].port!=port);
        let chosen=choose|i:int|0<=i<rs.len() && rs[i].port==port && forall|j:int|0<=j<i ==> rs[j].port!=port;
        assert(chosen==i);assert(first_binding(rs,port)==Some(i as usize));
    }
}
#[verifier::spinoff_prover]
pub proof fn last_restoring_facts(a:Observation,consumer:usize,port:Port)
    ensures last_restoring(a,consumer,port).is_some()==(exists|i:int|restorable(a,consumer,port,i)),
        last_restoring(a,consumer,port).is_some() ==> restorable(a,consumer,port,last_restoring(a,consumer,port).unwrap() as int),
{
    if a.restoring.contains_key(consumer) {
        let matched=Seq::new(a.restoring[consumer].len() as nat,|i:int|restorable(a,consumer,port,i));
        matched.index_of_last_ensures(true);
        if exists|i:int|restorable(a,consumer,port,i) {
            let j=choose|i:int|restorable(a,consumer,port,i);assert(matched[j]);assert(matched.contains(true));
            let i=matched.index_of_last(true).unwrap();
            assert(restorable(a,consumer,port,i));
            assert forall|j:int|i<j<a.restoring[consumer].len() implies !restorable(a,consumer,port,j) by {assert(!matched[j]);}
            assert(exists|i:int|restorable(a,consumer,port,i) && forall|j:int|i<j<a.restoring[consumer].len() ==> !restorable(a,consumer,port,j));
            let chosen=choose|i:int|restorable(a,consumer,port,i) && forall|j:int|i<j<a.restoring[consumer].len() ==> !restorable(a,consumer,port,j);
            assert(chosen==i);assert(last_restoring(a,consumer,port)==Some(i as usize));
        }
    }
}
pub proof fn result_source(a:Observation,port:Port,consumer:Option<usize>,generation:Option<u64>,r:Read)
    requires a.wf(),result(a,port,consumer,generation)==Ok(Some(r)),
    ensures r==materialized(a,r.publication,r.source),
        match r.source {
            Source::Committed {binding}=>consumer.is_some() && a.admissions.contains_key(consumer.unwrap())
                && binding<bindings(a,consumer.unwrap()).len() && bindings(a,consumer.unwrap())[binding as int].port==port
                && bindings(a,consumer.unwrap())[binding as int].publication==r.publication,
            Source::Restoring {index}=>consumer.is_some() && restorable(a,consumer.unwrap(),port,index as int)
                && a.restoring[consumer.unwrap()][index as int]==r.publication,
            Source::Own=>consumer==Some(r.owner) && visible(a,port,r.publication),
            Source::Root=>consumer.is_none() && visible(a,port,r.publication)
                && a.control.control().phase_of(r.owner)==Some(Phase::Active) && !a.control.control().is_retired(r.owner),
        },
{
    reveal(result);reveal(selection);
    if let Some(id)=consumer {
        first_binding_facts(bindings(a,id),port);last_restoring_facts(a,id,port);
    }
}

impl History {
    /// Every retained admission still owns its original live leases. A release
    /// of another episode cannot consume them, even across retry or compaction.
    pub proof fn admission_leases_live(&self,end:int)
        requires self.valid(),0<=end<self.states.len(),
        ensures forall|id:usize,j:int|self.states[end].admissions.contains_key(id)
            && 0<=j<self.states[end].admissions[id].resources_view().len() ==>
            #[trigger] self.states[end].store.registry_view().active_lease(self.states[end].admissions[id].resources_view()[j].lease)
                ==Some(self.states[end].admissions[id].lease_record(j).lease),
        decreases end,
    {
        if end>0 {
            self.admission_leases_live(end-1);let i=end-1;
            assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
            let a=self.states[i];let b=self.states[i+1];a.store.slot_count();b.store.slot_count();
            if b.store.same(&a.store) {b.store.same_observations(&a.store);}
            if b.store.registry_view().unchanged(&a.store.registry_view()) {b.store.registry_view().unchanged_observations(&a.store.registry_view());}
            assert forall|id:usize,j:int|b.admissions.contains_key(id) && 0<=j<b.admissions[id].resources_view().len()
                implies #[trigger] b.store.registry_view().active_lease(b.admissions[id].resources_view()[j].lease)==Some(b.admissions[id].lease_record(j).lease) by {
                let admitted=b.admissions[id];let token=admitted.resources_view()[j].lease;
                match self.events[i] {
                    Event::Begin {consumer,out} if out.is_ok() && consumer==id=>{},
                    _=>{
                        assert(a.admissions.contains_key(id) && a.admissions[id]==admitted);
                        assert(a.store.registry_view().active_lease(token)==Some(admitted.lease_record(j).lease));
                        match self.events[i] {
                            Event::Release {id:released,out,..} if out.is_ok()=>{
                                assert(released!=id);
                                if a.admissions[released].lease_ids().contains(token) {
                                    let k=choose|k:int|0<=k<a.admissions[released].lease_ids().len() && a.admissions[released].lease_ids()[k]==token;
                                    assert(a.admissions[released].resources_view()[k].lease==token);
                                    assert(a.store.registry_view().active_lease(token)==Some(a.admissions[released].lease_record(k).lease));
                                    assert(false);
                                }
                            },
                            Event::ReleaseReservation {out,..} if out.is_ok()=>{},
                            _=>{
                                a.store.registry_view().active_lease_facts(token);
                                let k=choose|k:int|0<=k<a.store.registry_view().lease_records().len() && a.store.registry_view().lease_records()[k].id==token
                                    && a.store.registry_view().lease_records()[k].lease==a.store.registry_view().active_lease(token).unwrap();
                                assert(k<b.store.registry_view().lease_records().len());
                                assert(b.store.registry_view().lease_records()[k]==a.store.registry_view().lease_records()[k]);
                                b.store.registry_view().lease_at_position(k);
                            },
                        }
                    },
                }
            }
        }
    }
}

impl NodeRuntime {
    fn bound_index(&self,consumer:usize,port:Port)->(out:Option<usize>)
        ensures out==first_binding(bindings(self.observation(),consumer),port),
            out.is_some() ==> out.unwrap()<bindings(self.observation(),consumer).len()
                && bindings(self.observation(),consumer)[out.unwrap() as int].port==port,
    {
        if let Some(admission)=self.admissions.get(&consumer) {
            let rs=admission.resources();let mut i=0;
            while i<rs.len()
                invariant i<=rs.len(),rs@==bindings(self.observation(),consumer),
                    forall|j:int|0<=j<i ==> rs[j].port!=port,
                decreases rs.len()-i,
            {
                if rs[i].port==port {
                    assert(exists|j:int|0<=j<rs.len() && rs[j].port==port);
                    let ghost chosen=choose|j:int|0<=j<rs.len() && rs[j].port==port && forall|k:int|0<=k<j ==> rs[k].port!=port;
                    assert(chosen==i);return Some(i);
                }
                i+=1;
            }
        }
        None
    }
    pub(super) fn visible_lookup(&self,port:Port)->(out:Option<PublicationId>)
        requires self.wf(),ensures out==visible_choice(self.observation(),port),
            out.is_some() ==> visible(self.observation(),port,out.unwrap()),
    {
        let out=self.store.registry().resolve(port);
        proof {
            if let Some(p)=out {
                assert(visible(self.observation(),port,p));
                assert(exists|id:PublicationId|visible(self.observation(),port,id));
                let q=choose|id:PublicationId|visible(self.observation(),port,id);
                self.store.visible_unique(p,q);
            }
        }
        out
    }
    fn restoring_index(&self,consumer:usize,port:Port)->(out:Option<usize>)
        requires self.wf(),ensures out==last_restoring(self.observation(),consumer,port),
            out.is_some() ==> restorable(self.observation(),consumer,port,out.unwrap() as int),
    {
        if let Some(ids)=self.restoring.get(&consumer) {
            let mut i=ids.len();
            while i>0
                invariant self.wf(),self.restoring@.contains_key(consumer),*ids==self.restoring@[consumer],i<=ids.len(),
                    forall|j:int|i<=j<ids.len() ==> !restorable(self.observation(),consumer,port,j),
                decreases i,
            {
                i-=1;
                if let Some(p)=self.store.registry().entry(ids[i]) {
                    if p.port==port && p.retained {
                        assert(restorable(self.observation(),consumer,port,i as int));
                        assert(exists|j:int|restorable(self.observation(),consumer,port,j));
                        let ghost chosen=choose|j:int|restorable(self.observation(),consumer,port,j)
                            && forall|k:int|j<k<ids.len() ==> !restorable(self.observation(),consumer,port,k);
                        assert(chosen==i);return Some(i);
                    }
                }
            }
        }
        None
    }
    #[verifier::spinoff_prover]
    fn read_value(&self,id:PublicationId,source:Source)->(out:Read)
        requires self.wf(),id.0<self.store.registry_view().publications().len(),
            self.store.registry_view().publications()[id.0 as int].retained,
        ensures valid_read(self.observation(),out),out==materialized(self.observation(),id,source),
    {
        proof {self.store.retained_value(id);}
        let entry=self.store.registry().entry(id).unwrap();
        let (revision,value)=self.store.observation(id).unwrap();
        Read {publication:id,owner:entry.owner,value:*value,revision,source}
    }
    #[verifier::spinoff_prover]
    fn lookup(&self,port:Port,consumer:Option<usize>,generation:Option<u64>)->(out:Result<Option<Read>,ReadError>)
        requires self.wf(),ensures out==result(self.observation(),port,consumer,generation),
            out.is_ok() && out->Ok_0.is_some() ==> valid_read(self.observation(),out->Ok_0.unwrap()),
    {
        proof {reveal(result);reveal(selection);}
        if let Some(id)=consumer {
            if !self.control.kernel().contains(id) {return Err(ReadError::Unknown);}
            if let Some(generation)=generation {
                if self.control.kernel().episode_generation(id)!=Some(generation) {return Err(ReadError::Stale);}
                assert(self.control.control().generation_of(id)==Some(generation));
            }
            if let Some(index)=self.bound_index(id,port) {
                let admission=self.admissions.get(&id).unwrap();let binding=admission.resources()[index];
                proof {
                    self.history@.admission_leases_live(self.history@.events.len() as int);
                    assert(self.store.registry_view().active_lease(binding.lease)==Some(admission.lease_record(index as int).lease));
                }
                let (publication,_,_)=self.store.leased_observation(binding.lease).unwrap();
                proof {self.store.slot_count();self.store.registry_view().active_lease_facts(binding.lease);}
                return Ok(Some(self.read_value(publication,Source::Committed {binding:index})));
            }
            assert(first_binding(bindings(self.observation(),id),port).is_none());
            if let Some(p)=self.visible_lookup(port) {
                let entry=self.store.registry().entry(p).unwrap();
                if entry.owner==id {
                    proof {self.store.visible_value(p);self.store.value_is_retained(p);}
                    return Ok(Some(self.read_value(p,Source::Own)));
                }
            }
            if let Some(index)=self.restoring_index(id,port) {
                let p=self.restoring.get(&id).unwrap()[index];
                return Ok(Some(self.read_value(p,Source::Restoring {index})));
            }
        } else if let Some(p)=self.visible_lookup(port) {
            let entry=self.store.registry().entry(p).unwrap();
            if self.control.kernel().phase(entry.owner)==Some(Phase::Active) && !self.control.kernel().retired(entry.owner) {
                proof {self.store.visible_value(p);self.store.value_is_retained(p);}
                return Ok(Some(self.read_value(p,Source::Root)));
            }
        }
        Ok(None)
    }
    /// Read the real service view and record the actual arguments and result.
    /// No lifecycle, publication, lease, pending release or callback state moves.
    pub fn resolve(&mut self,port:Port,consumer:Option<usize>,generation:Option<u64>)->(out:Result<Option<Read>,ReadError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),
            out==result(old(self).observation(),port,consumer,generation),
            out.is_ok() && out->Ok_0.is_some() ==> valid_read(old(self).observation(),out->Ok_0.unwrap()),
            final(self).history()==old(self).history().append(final(self).observation(),Event::Read {port,consumer,generation,out}),
    {
        let ghost before=self.observation();let out=self.lookup(port,consumer,generation);
        proof {self.scopes.unchanged_reflexive();reveal(history::operation);self.record(before,Event::Read {port,consumer,generation,out});}
        out
    }
}

/// The lookup carrier is relative to the caller's retained episode. It is not
/// the global visible table: an old consumer may still see a withdrawn slot.
pub open spec fn view(a:Observation,consumer:Option<usize>)->IMap<Port,u64> {
    IMap::new(|port:Port|selection(a,port,consumer).is_some(),
        |port:Port|materialized(a,selection(a,port,consumer).unwrap().0,selection(a,port,consumer).unwrap().1).value)
}
pub open spec fn read_operation()->crate::coeffects::Operation<u64,Option<u64>> {
    |value:Option<u64>|(value,|next:Option<u64>|next,value)
}

impl History {
    /// A stable publication never changes its logical owner or port. Adoption
    /// may advance its initial generation; replacement may change its payload.
    pub proof fn publication_identity(&self,start:int,end:int,id:PublicationId)
        requires self.valid(),0<=start<=end<self.states.len(),
            id.0<self.states[start].store.registry_view().publications().len(),
        ensures id.0<self.states[end].store.registry_view().publications().len(),
            self.states[end].store.registry_view().publications()[id.0 as int].owner==self.states[start].store.registry_view().publications()[id.0 as int].owner,
            self.states[end].store.registry_view().publications()[id.0 as int].port==self.states[start].store.registry_view().publications()[id.0 as int].port,
        decreases end-start,
    {
        if start<end {
            self.publication_identity(start,end-1,id);let i=end-1;
            assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
            let a=self.states[i];let b=self.states[i+1];a.store.slot_count();b.store.slot_count();
            if b.store.same(&a.store) {b.store.same_observations(&a.store);}
            if b.store.registry_view().unchanged(&a.store.registry_view()) {b.store.registry_view().unchanged_observations(&a.store.registry_view());}
        }
    }
    /// The actual returned handle has both publication and payload origins in
    /// this execution. It is never an invented value supplied by a receipt.
    pub proof fn read_has_origin(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is Read,
            self.events[index]->Read_out.is_ok(),self.events[index]->Read_out->Ok_0.is_some(),
        ensures {
            let r=self.events[index]->Read_out->Ok_0.unwrap();let a=self.states[index];
            &&& valid_read(a,r)
            &&& exists|published:int|0<=published<index && self.publication_issued_at(published,r.publication,r.owner,
                a.store.registry_view().publications()[r.publication.0 as int].port)
            &&& exists|written:int|0<=written<index && self.payload_written_at(written,r.publication.0 as int,r.value)
        },
    {
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
        let r=self.events[index]->Read_out->Ok_0.unwrap();
        self.publication_origin(index,r.publication);self.payload_origin(index,r.publication.0 as int,r.value);
        let published=choose|published:int|0<=published<index && self.publication_issued_at(published,r.publication,
            self.states[index].store.registry_view().publications()[r.publication.0 as int].owner,
            self.states[index].store.registry_view().publications()[r.publication.0 as int].port);
        assert(self.publication_issued_at(published,r.publication,r.owner,self.states[index].store.registry_view().publications()[r.publication.0 as int].port));
    }
    /// Committed reads retain the Begin-selected publication and declared port.
    /// Current visibility is irrelevant; replacement of that slot remains visible.
    pub proof fn committed_read_origin(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is Read,
            self.events[index]->Read_out.is_ok(),self.events[index]->Read_out->Ok_0.is_some(),
            self.events[index]->Read_out->Ok_0.unwrap().source is Committed,
        ensures {
            let a=self.states[index];let e=self.events[index];let r=e->Read_out->Ok_0.unwrap();let consumer=e->Read_consumer.unwrap();
            let admission=a.admissions[consumer];let j=r.source->Committed_binding as int;let s=admission.source();
            &&& e->Read_consumer.is_some() && a.admissions.contains_key(consumer)
            &&& 0<=j<admission.resources_view().len()
            &&& admission.resources_view()[j].port==e->Read_port && admission.resources_view()[j].publication==r.publication
            &&& a.store.registry_view().active_lease(admission.resources_view()[j].lease)==Some(admission.lease_record(j).lease)
            &&& a.store.registry_view().publications()[r.publication.0 as int].port==e->Read_port
            &&& r.owner==s.bindings[j].provider
            &&& s.control.control().paper().fibers[consumer].dependencies.contains(e->Read_port)
            &&& exists|issued:int|0<=issued<index && self.issued_at(issued,consumer,admission)
        },
    {
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
        let a=self.states[index];let e=self.events[index];let r=e->Read_out->Ok_0.unwrap();let consumer=e->Read_consumer.unwrap();
        let j=r.source->Committed_binding as int;let admitted=a.admissions[consumer];let s=admitted.source();
        result_source(a,e->Read_port,e->Read_consumer,e->Read_generation,r);
        assert(e->Read_consumer.is_some() && a.admissions.contains_key(consumer));
        assert(0<=j<admitted.resources_view().len());
        assert(admitted.resources_view()[j].publication==r.publication);
        self.admission_leases_live(index);self.admission_origin(index,consumer);
        let issued=choose|issued:int|0<=issued<index && self.issued_at(issued,consumer,admitted);
        admitted.value_provenance(j);self.publication_identity(issued,index,r.publication);
        s.control.control().paper_target_vector(consumer,s.bindings);
        assert(s.bindings.contains(s.bindings[j]));
        assert(ISet::new(|b:crate::Binding|s.bindings.contains(b)).contains(s.bindings[j]));
    }
    /// Cleanup's fallback comes from an earlier own-slot capture while visible,
    /// not the new provider that happens to occupy the same port now.
    pub proof fn restoring_read_origin(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is Read,
            self.events[index]->Read_out.is_ok(),self.events[index]->Read_out->Ok_0.is_some(),
            self.events[index]->Read_out->Ok_0.unwrap().source is Restoring,
        ensures {
            let e=self.events[index];let r=e->Read_out->Ok_0.unwrap();
            &&& e->Read_consumer==Some(r.owner)
            &&& self.states[index].store.registry_view().publications()[r.publication.0 as int].port==e->Read_port
            &&& exists|captured:int|0<=captured<index && self.events[captured] is RememberPublications
                && self.events[captured]->RememberPublications_owner==r.owner
                && self.events[captured]->RememberPublications_publications.contains(r.publication)
                && resources::selected(self.states[captured],r.owner,r.publication,true)
        },
    {
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
        let e=self.events[index];let r=e->Read_out->Ok_0.unwrap();let consumer=e->Read_consumer.unwrap();
        let j=r.source->Restoring_index as int;let a=self.states[index];
        result_source(a,e->Read_port,e->Read_consumer,e->Read_generation,r);
        assert(e->Read_consumer.is_some() && a.restoring.contains_key(consumer));
        assert(restorable(a,consumer,e->Read_port,j));
        assert(a.restoring[consumer][j]==r.publication);assert(a.restoring[consumer]@.contains(r.publication));
        self.restoring_origin(index,consumer,r.publication);
        let captured=choose|captured:int|0<=captured<index && self.events[captured] is RememberPublications
            && self.events[captured]->RememberPublications_owner==consumer
            && self.events[captured]->RememberPublications_publications.contains(r.publication)
            && resources::selected(self.states[captured],consumer,r.publication,true);
        self.publication_identity(captured,index,r.publication);
        assert(consumer==r.owner);
    }
    /// While its admission is retained, a successful read cannot silently fall
    /// back to a newly published same-name service. Stale requests can reject.
    pub proof fn committed_selection_retained(&self,start:int,index:int,consumer:usize,port:Port)
        requires self.valid(),0<=start<=index<self.events.len(),self.states[start].admissions.contains_key(consumer),
            first_binding(bindings(self.states[start],consumer),port).is_some(),
            forall|i:int|start<=i<index ==> !self.releases(i,consumer),
            self.events[index] is Read,self.events[index]->Read_consumer==Some(consumer),self.events[index]->Read_port==port,
        ensures {
            let out=self.events[index]->Read_out;let j=first_binding(bindings(self.states[start],consumer),port).unwrap();
            out.is_ok() ==> out->Ok_0.is_some() && out->Ok_0.unwrap().source==(Source::Committed {binding:j})
                && out->Ok_0.unwrap().publication==bindings(self.states[start],consumer)[j as int].publication
        },
    {
        self.admission_retained(start,index,consumer);
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
        reveal(result);reveal(selection);
    }
    /// Definition 29 / equation (31), specialized to reading an opaque handle:
    /// the returned outcome is the selected binding, and forward/inverse are
    /// identity on this caller's projected table. No JS method body is modeled.
    pub proof fn read_context_lift(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is Read,self.events[index]->Read_out.is_ok(),
        ensures {
            let e=self.events[index];let port=e->Read_port;let consumer=e->Read_consumer;
            let before=view(self.states[index],consumer);let after=view(self.states[index+1],consumer);
            let outcome=if e->Read_out->Ok_0.is_some() {Some(e->Read_out->Ok_0.unwrap().value)} else {None};
            let operation=read_operation()(crate::coeffects::get(before,port));
            &&& self.states[index+1]==self.states[index]
            &&& operation.2==outcome
            &&& after==crate::coeffects::put(before,port,operation.0)
            &&& crate::coeffects::lift(port,operation.1)(after)==before
        },
    {
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
        let e=self.events[index];let port=e->Read_port;let before=view(self.states[index],e->Read_consumer);
        reveal(result);
        crate::coeffects::update_restore(before,port,crate::coeffects::get(before,port));
        assert(crate::coeffects::put(before,port,crate::coeffects::get(before,port)) =~= before);
    }
}

/// A sealed result from a real service lookup. Static typed embeddings carry
/// this value instead of decoding provider/publication IDs from JSON again.
#[allow(dead_code)]
pub struct Selected {domain:u64,port:Port,consumer:Option<usize>,generation:Option<u64>,read:Read,origin:Ghost<History>}
impl Selected {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub fn domain(&self)->(out:u64) ensures out==self.domain_id(), {self.domain}
    pub closed spec fn read_spec(&self)->Read {self.read}
    pub closed spec fn origin(&self)->History {self.origin@}
    pub open spec fn certified(&self)->bool {
        self.origin().valid() && self.origin().events.len()>0
            && self.origin().states.last().control.protocol().domain_id()==self.domain_id()
            && valid_read(self.origin().states.last(),self.read_spec())
            && self.origin().events.last()==(Event::Read {port:self.port_spec(),consumer:self.consumer_spec(),generation:self.generation_spec(),out:Ok(Some(self.read_spec()))})
    }
    pub closed spec fn port_spec(&self)->Port {self.port}
    pub closed spec fn consumer_spec(&self)->Option<usize> {self.consumer}
    pub closed spec fn generation_spec(&self)->Option<u64> {self.generation}
    pub fn owner(&self)->(out:usize) ensures out==self.read_spec().owner, {self.read.owner}
    pub fn publication(&self)->(out:PublicationId) ensures out==self.read_spec().publication, {self.read.publication}
    pub fn value(&self)->(out:u64) ensures out==self.read_spec().value, {self.read.value}
    pub fn port(&self)->(out:Port) ensures out==self.port_spec(), {self.port}
    pub fn consumer(&self)->(out:Option<usize>) ensures out==self.consumer_spec(), {self.consumer}
    pub fn generation(&self)->(out:Option<u64>) ensures out==self.generation_spec(), {self.generation}
    pub proof fn interpretation(&self)
        requires self.certified(),
        ensures result(self.origin().states[self.origin().events.len()-1],self.port_spec(),self.consumer_spec(),self.generation_spec())==Ok(Some(self.read_spec())),
    {
        let i=self.origin().events.len()-1;
        assert(history::step(self.origin().states[i],self.origin().states[i+1],self.origin().events[i]));
        reveal(history::operation);
    }
}
impl NodeRuntime {
    pub fn select(&mut self,port:Port,consumer:Option<usize>,generation:Option<u64>)->(out:Result<Option<Selected>,ReadError>)
        requires old(self).wf(),ensures final(self).wf(),final(self).observation()==old(self).observation(),
            out.is_ok() && out->Ok_0.is_some() ==> {
                let selected=out->Ok_0.unwrap();
                selected.certified() && selected.origin()==final(self).history() && selected.port_spec()==port
                    && selected.consumer_spec()==consumer && selected.generation_spec()==generation
                    && result(old(self).observation(),port,consumer,generation)==Ok(Some(selected.read_spec()))
            },
    {
        match self.resolve(port,consumer,generation) {
            Err(error)=>Err(error),Ok(None)=>Ok(None),
            Ok(Some(read))=>Ok(Some(Selected {domain:self.state().domain(),port,consumer,generation,read,origin:Ghost(self.history())})),
        }
    }
}

}
