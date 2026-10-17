//! Production Node setup admission. Availability, actual publications, Begin
//! and cleanup leases are checked under one exclusive borrow, without invoking
//! host code. Values are opaque handles; cached checks use explicit notification.
use super::Availability;
use crate::action_ledger::ActionTicket;
use crate::lifecycle_actions::resources::CleanupReleaseError;
use crate::lifecycle_state::LifecycleState;
use crate::publication::values::PublicationStore;
use crate::publication::values::ReleasedValue;
#[cfg(verus_keep_ghost)]
use crate::publication::{Lease, LeaseOwner, LeaseRecord};
use crate::publication::{LeaseId, PublicationError, PublicationId};
use crate::{Binding, Error, Port};
use std::collections::BTreeSet;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum AdmissionError {Unavailable,Lifecycle(Error),Publication(PublicationError)}

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct ResourceBinding {pub port:Port,pub publication:PublicationId,pub lease:LeaseId}

/// The erased source is captured by the operation itself, not supplied by the
/// executor as a claimed expected result. It includes actual payload versions.
pub struct Capture {
    pub control:LifecycleState,pub store:PublicationStore<u64>,pub checks:Availability,
    pub checked:Set<usize>,pub bindings:Seq<Binding>,pub selected:Seq<PublicationId>,
}

/// Private construction prevents an adapter from substituting a resource list
/// after Begin. Dropping this owner does not release its real registry leases.
#[allow(dead_code)] // The admission source is erased in ordinary Rust.
pub struct Admission {ticket:ActionTicket,resources:Vec<ResourceBinding>,capture:Ghost<Capture>}
impl Admission {
    pub closed spec fn origin(&self)->ActionTicket {self.ticket}
    pub closed spec fn resources_view(&self)->Seq<ResourceBinding> {self.resources@}
    pub closed spec fn source(&self)->Capture {self.capture@}
    pub open spec fn wf(&self)->bool {
        let s=self.source();
        &&& s.control.wf() && s.store.wf() && s.checks.wf()
        &&& self.origin().kind==crate::action_ledger::ActionKind::Setup
        &&& self.origin().domain==s.control.protocol().domain_id()
        &&& s.control.control().generation_of(self.origin().id).is_some()
        &&& self.origin().generation as nat==s.control.control().generation_of(self.origin().id).unwrap() as nat+1
        &&& s.store.registry_view().lease_allocations()+self.resources_view().len()<=usize::MAX
        &&& s.control.control().complete_target(self.origin().id,s.bindings)
        &&& s.selected.len()==s.bindings.len() && self.resources_view().len()==s.bindings.len()
        &&& forall|i:int|0<=i<s.bindings.len() ==> {
            &&& s.checks.selects_publication(&s.control,&s.store,s.checked,self.origin().id,s.bindings[i],s.selected[i])
            &&& self.resources_view()[i]==ResourceBinding {
                port:Port {key:s.bindings[i].key,realm:s.bindings[i].realm},publication:s.selected[i],
                lease:LeaseId((s.store.registry_view().lease_allocations()+i) as usize)}
        }
    }
    pub open spec fn lease_record(&self,i:int)->LeaseRecord {
        LeaseRecord {id:self.resources_view()[i].lease,lease:Lease {publication:self.resources_view()[i].publication,live:true,
            consumer:Some(LeaseOwner {owner:self.origin().id,generation:self.origin().generation})}}
    }
    pub open spec fn leases(&self)->Seq<LeaseRecord> {
        self.resources_view().map(|i:int,_:ResourceBinding|self.lease_record(i))
    }
    pub fn ticket(&self)->(out:ActionTicket) ensures out==self.origin(), {self.ticket}
    pub fn resources(&self)->(out:&[ResourceBinding]) ensures out@==self.resources_view(), {self.resources.as_slice()}
    pub open spec fn lease_ids(&self)->Seq<LeaseId> {self.resources_view().map(|_:int,r:ResourceBinding|r.lease)}
    /// Release uses the retained admission, including for zero-dependency
    /// episodes. A stale empty manifest cannot authorize a later generation.
    pub fn finish(&self,control:&mut LifecycleState,store:&mut PublicationStore<u64>,publications:&[PublicationId])
        ->(out:Result<Vec<ReleasedValue<u64>>,CleanupReleaseError>)
        requires self.wf(),old(control).wf(),old(store).wf(),
        ensures out.is_ok()==(old(control).protocol().domain_id()==self.origin().domain
                && old(control).control().generation_of(self.origin().id)==Some(self.origin().generation)
                && old(store).registry_view().domain_id()==Some(self.origin().domain)
                && old(control).protocol().resource_finish_enabled(&old(control).control(),self.origin().id,false)
                && old(store).registry_view().cleanup_batch_enabled(LeaseOwner {owner:self.origin().id,generation:self.origin().generation},self.lease_ids(),publications@)),
            final(control).wf(),final(store).wf(),
            final(store).registry_view().domain_id()==old(store).registry_view().domain_id(),
            final(control).protocol().history_preserved(&old(control).protocol()),
            out.is_ok() ==> final(control).control_history().extends(old(control).control_history())
                && final(store).released(old(store),self.lease_ids(),publications@),final(store).visible_table()==old(store).visible_table(),
            final(store).revisions()==old(store).revisions(),
            out.is_err() ==> final(store).same(old(store)) && final(control).control().unchanged(&old(control).control())
                && final(control).protocol().same(&old(control).protocol()),
            out.is_ok() ==> {
                &&& old(control).protocol().domain_id()==self.origin().domain
                &&& old(control).control().generation_of(self.origin().id)==Some(self.origin().generation)
                &&& old(control).protocol().resource_finish_enabled(&old(control).control(),self.origin().id,false)
                &&& final(store).registry_view().episode_resources_cleared(LeaseOwner {owner:self.origin().id,generation:self.origin().generation})
                &&& crate::refinement::step(old(control).control().paper(),final(control).control().paper(),self.origin().id,crate::refinement::Rule::Unload)
                &&& out->Ok_0.len()==publications.len()
                &&& forall|i:int|0<=i<publications.len() ==> out->Ok_0[i].publication==publications[i]
                    && publications[i].0<old(store).values().len()
                    && old(store).values()[publications[i].0 as int]==Some(out->Ok_0[i].value)
            },
    {
        proof {control.same_reflexive();control.same_observations(control);store.same_reflexive();}
        if control.domain()!=self.ticket.domain || control.kernel().episode_generation(self.ticket.id)!=Some(self.ticket.generation) {
            return Err(CleanupReleaseError::Lifecycle(Error::InvalidState));
        }
        let mut leases=Vec::new();let mut i=0;
        while i<self.resources.len()
            invariant i<=self.resources.len(),leases@==self.lease_ids().take(i as int),
            decreases self.resources.len()-i,
        {leases.push(self.resources[i].lease);i+=1;}
        assert(leases@==self.lease_ids());
        store.finish_resources(control,self.ticket.id,false,&leases,publications)
    }
    /// Every captured slot has the real provider, retained value and revision.
    /// Later replacement is allowed; this describes the admission observation.
    pub proof fn value_provenance(&self,i:int)
        requires self.wf(),0<=i<self.resources_view().len(),
        ensures {
            let s=self.source();let r=self.resources_view()[i];let p=r.publication.0 as int;
            &&& 0<=p<s.store.values().len() && p<s.store.revisions().len()
            &&& s.store.values()[p].is_some()
            &&& s.store.registry_view().publications()[p].owner==s.bindings[i].provider
            &&& s.store.registry_view().publications()[p].port==r.port
            &&& s.store.registry_view().publications()[p].visible
        },
    {self.source().store.visible_value(self.resources_view()[i].publication);}
}

impl Availability {
    pub open spec fn selects_publication(&self,control:&LifecycleState,store:&PublicationStore<u64>,checked:Set<usize>,
        consumer:usize,b:Binding,p:PublicationId)->bool {
        let port=Port {key:b.key,realm:b.realm};
        &&& self.eligible(control,store,consumer,port,p)
        &&& store.registry_view().publications()[p.0 as int].owner==b.provider
        &&& (!checked.contains(p.0) || (self.rows().contains_key((consumer,b.key,b.realm))
            && self.rows()[(consumer,b.key,b.realm)].publication==p && self.rows()[(consumer,b.key,b.realm)].available))
    }
    /// Cached acceptance intentionally survives set/notify until a new check
    /// lands; current predicate truth is not assumed from that cached bit.
    pub open spec fn ready_spec(&self,control:&LifecycleState,store:&PublicationStore<u64>,checked:Set<usize>,consumer:usize)->bool {
        &&& control.protocol().domain_id()==self.domain_id() && store.registry_view().domain_id()==Some(self.domain_id())
        &&& !control.control().unavailable(consumer)
        &&& forall|b:Binding|control.control().binding_is_target(consumer,b) ==>
            exists|p:PublicationId|self.selects_publication(control,store,checked,consumer,b,p)
    }
    fn select(&self,control:&LifecycleState,store:&PublicationStore<u64>,checked:&BTreeSet<usize>,consumer:usize,b:Binding)
        ->(out:Option<PublicationId>)
        requires self.wf(),control.wf(),store.wf(),
        ensures out.is_some()==(exists|p:PublicationId|self.selects_publication(control,store,checked@,consumer,b,p)),
            out.is_some() ==> self.selects_publication(control,store,checked@,consumer,b,out.unwrap()),
    {
        let port=Port {key:b.key,realm:b.realm};
        let p=store.registry().resolve(port)?;
        proof {
            assert forall|other:PublicationId|self.selects_publication(control,store,checked@,consumer,b,other) implies other==p by {
                store.visible_unique(other,p);
            }
        }
        if !self.eligible_now(control,store,consumer,port,p) {return None;}
        let entry=store.registry().entry(p).unwrap();
        if entry.owner!=b.provider || (checked.contains(&p.0) && !self.available(consumer,port,p)) {return None;}
        assert(self.selects_publication(control,store,checked@,consumer,b,p));
        assert(exists|other:PublicationId|self.selects_publication(control,store,checked@,consumer,b,other));
        Some(p)
    }
    fn select_target(&self,control:&LifecycleState,store:&PublicationStore<u64>,checked:&BTreeSet<usize>,consumer:usize)
        ->(out:Option<(Vec<Binding>,Vec<PublicationId>)>)
        requires self.wf(),control.wf(),store.wf(),
        ensures out.is_some()==self.ready_spec(control,store,checked@,consumer),
            out.is_some() ==> control.control().complete_target(consumer,out.unwrap().0@)
                && out.unwrap().0.len()==control.control().target_count(consumer)
                && out.unwrap().0.len()==out.unwrap().1.len()
                && (forall|i:int|0<=i<out.unwrap().0.len() ==> self.selects_publication(control,store,checked@,consumer,out.unwrap().0[i],out.unwrap().1[i])),
    {
        if control.domain()!=self.domain || store.registry().domain()!=Some(self.domain) {return None;}
        let bindings=control.kernel().target(consumer)?;
        proof {control.control().complete_target_facts(consumer,bindings@);}
        let mut selected=Vec::new();let mut i=0;
        while i<bindings.len()
            invariant i<=bindings.len(),selected.len()==i,self.wf(),control.wf(),store.wf(),
                control.protocol().domain_id()==self.domain_id(),store.registry_view().domain_id()==Some(self.domain_id()),
                control.control().complete_target(consumer,bindings@),!control.control().unavailable(consumer),
                bindings.len()==control.control().target_count(consumer),
                forall|b:Binding|control.control().binding_is_target(consumer,b)==bindings@.contains(b),
                forall|j:int|0<=j<i ==> self.selects_publication(control,store,checked@,consumer,bindings[j],selected[j]),
            decreases bindings.len()-i,
        {
            let p=self.select(control,store,checked,consumer,bindings[i])?;
            selected.push(p);
            i+=1;
        }
        proof {
            assert forall|b:Binding|control.control().binding_is_target(consumer,b) implies
                exists|p:PublicationId|self.selects_publication(control,store,checked@,consumer,b,p) by {
                let j=choose|j:int|0<=j<bindings.len() && bindings[j]==b;
                assert(self.selects_publication(control,store,checked@,consumer,b,selected[j]));
            }
        }
        Some((bindings,selected))
    }
    pub fn ready(&self,control:&LifecycleState,store:&PublicationStore<u64>,checked:&BTreeSet<usize>,consumer:usize)->(out:bool)
        requires self.wf(),control.wf(),store.wf(),
        ensures out==self.ready_spec(control,store,checked@,consumer),
    {self.select_target(control,store,checked,consumer).is_some()}

    /// Capacity and actual publication selection are checked before Begin.
    /// Once Begin succeeds all lease allocations are proved to succeed; no
    /// partial rollback or caller-assembled expected resource list is needed.
    #[verifier::rlimit(30)]
    pub fn begin_setup(&self,control:&mut LifecycleState,store:&mut PublicationStore<u64>,checked:&BTreeSet<usize>,consumer:usize)
        ->(out:Result<Admission,AdmissionError>)
        requires self.wf(),old(control).wf(),old(store).wf(),
        ensures final(control).wf(),final(store).wf(),
            final(control).protocol().history_preserved(&old(control).protocol()),
            out.is_ok() ==> final(control).control_history().extends(old(control).control_history()),
            out.is_ok()==(self.ready_spec(old(control),old(store),checked@,consumer)
                && old(store).registry_view().lease_allocations()+old(control).control().target_count(consumer)<=usize::MAX
                && old(control).protocol().admission_enabled(consumer) && old(control).control().begin_enabled(consumer)),
            final(store).values()==old(store).values(),final(store).revisions()==old(store).revisions(),
            final(store).registry_view().domain_id()==old(store).registry_view().domain_id(),
            final(store).registry_view().publications()==old(store).registry_view().publications(),
            out.is_err() ==> final(control).same(old(control)) && final(store).same(old(store)),
            out.is_ok() ==> {
                let a=out->Ok_0;let s=a.source();
                &&& a.wf() && s.control==*old(control) && s.store==*old(store) && s.checks==*self && s.checked==checked@
                &&& a.origin().id==consumer && final(control).protocol().recorded(a.origin())
                &&& final(control).control().generation_of(consumer)==Some(a.origin().generation)
                &&& crate::refinement::step(old(control).control().paper(),final(control).control().paper(),consumer,crate::refinement::Rule::Begin)
                &&& crate::episode::binding_set(s.bindings)==final(control).control().paper().fibers[consumer].committed
                &&& final(store).registry_view().lease_records()==old(store).registry_view().lease_records()+a.leases()
                &&& final(store).registry_view().lease_allocations()==old(store).registry_view().lease_allocations()+a.resources_view().len()
                &&& forall|i:int|0<=i<a.resources_view().len() ==>
                    final(store).registry_view().active_lease(a.resources_view()[i].lease)==Some(a.lease_record(i).lease)
            },
    {
        proof {control.same_reflexive();control.same_observations(control);store.same_reflexive();}
        let (bindings,selected)=match self.select_target(control,store,checked,consumer) {
            Some(pair)=>pair,None=>return Err(AdmissionError::Unavailable),
        };
        if let Err(e)=store.registry().check_lease_capacity(bindings.len()) {return Err(AdmissionError::Publication(e));}
        let ghost source=Capture {control:*control,store:*store,checks:*self,checked:checked@,bindings:bindings@,selected:selected@};
        let _kernel=control.kernel();
        let ticket=match control.begin(consumer) {Ok(t)=>t,Err(e)=>return Err(AdmissionError::Lifecycle(e))};
        proof {
            source.control.control().refines_paper();
            source.control.control().paper_target_vector(consumer,bindings@);
            crate::refinement::target_unique(source.control.control().paper(),consumer,crate::episode::binding_set(bindings@),control.control().paper().fibers[consumer].committed);
        }
        let mut resources:Vec<ResourceBinding>=Vec::new();let mut i=0;
        while i<bindings.len()
            invariant i<=bindings.len(),resources.len()==i,bindings@==source.bindings,selected@==source.selected,selected.len()==bindings.len(),
                source.control==*old(control),source.store==*old(store),source.checks==*self,source.checked==checked@,
                source.control.wf(),source.store.wf(),self.wf(),store.wf(),control.wf(),
                self.ready_spec(&source.control,&source.store,checked@,consumer),
                source.control.protocol().admission_enabled(consumer),source.control.control().begin_enabled(consumer),
                bindings.len()==source.control.control().target_count(consumer),
                source.control.control().complete_target(consumer,bindings@),
                forall|j:int|0<=j<bindings.len() ==> self.selects_publication(&source.control,&source.store,checked@,consumer,bindings[j],selected[j]),
                ticket.id==consumer,ticket.domain==source.control.protocol().domain_id(),ticket.kind==crate::action_ledger::ActionKind::Setup,
                source.control.control().generation_of(consumer).is_some(),ticket.generation as nat==source.control.control().generation_of(consumer).unwrap() as nat+1,
                control.protocol().recorded(ticket),control.control().generation_of(consumer)==Some(ticket.generation),
                crate::refinement::step(source.control.control().paper(),control.control().paper(),consumer,crate::refinement::Rule::Begin),
                crate::episode::binding_set(bindings@)==control.control().paper().fibers[consumer].committed,
                store.values()==source.store.values(),store.revisions()==source.store.revisions(),
                store.registry_view().domain_id()==source.store.registry_view().domain_id(),store.registry_view().publications()==source.store.registry_view().publications(),
                store.registry_view().lease_allocations()==source.store.registry_view().lease_allocations()+i,
                source.store.registry_view().lease_allocations()+bindings.len()<=usize::MAX,
                forall|j:int|0<=j<i ==> resources[j]==(ResourceBinding {port:Port {key:bindings[j].key,realm:bindings[j].realm},publication:selected[j],lease:LeaseId((source.store.registry_view().lease_allocations()+j) as usize)}),
                store.registry_view().lease_records()==source.store.registry_view().lease_records()+resources@.map(|_:int,r:ResourceBinding|LeaseRecord {id:r.lease,lease:Lease {publication:r.publication,live:true,consumer:Some(LeaseOwner {owner:consumer,generation:ticket.generation})}}),
            decreases bindings.len()-i,
        {
            let p=selected[i];
            assert(store.registry_view().acquisition_enabled(p));
            let lease=store.acquire_for(p,consumer,ticket.generation).unwrap();
            resources.push(ResourceBinding {port:Port {key:bindings[i].key,realm:bindings[i].realm},publication:p,lease});
            i+=1;
        }
        let out=Admission {ticket,resources,capture:Ghost(source)};
        let _registry=store.registry();
        proof {
            assert(out.leases() =~= out.resources_view().map(|_:int,r:ResourceBinding|LeaseRecord {id:r.lease,lease:Lease {publication:r.publication,live:true,consumer:Some(LeaseOwner {owner:consumer,generation:ticket.generation})}}));
            assert forall|j:int|0<=j<out.resources_view().len() implies
                store.registry_view().active_lease(out.resources_view()[j].lease)==Some(out.lease_record(j).lease) by {
                store.registry_view().lease_at_position(source.store.registry_view().lease_records().len()+j);
            }
        }
        Ok(out)
    }
}
}
