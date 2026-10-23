//! Source evidence for native Child cleanup. A terminal shared-slot decision is
//! paired with the actual native observation; an assigned episode still needs
//! its own successful Unload. None of this evidence schedules cleanup.
#[cfg(verus_keep_ghost)]
use super::{episode::Unload, owner::EpisodeOwner};
use super::{NativeRuntime, ReleaseObservation};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::registration::child::ChildStatus;
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::registration::shared_child::ChildSnapshot;
use crate::lifecycle_state::registration::shared_child::{ChildTransition, Decision, SharedChild};
use crate::lifecycle_state::registration::ChildIdentity;
use crate::reversible_value::joint;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint::native;
use crate::Error;
#[cfg(verus_keep_ghost)]
use crate::Phase;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::resource::Loc;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub type Observation = (ChildTransition<Result<Option<ChildIdentity>,Error>>,Tracked<Option<Retirement>>);
/// Runtime result plus evidence from those same real operations. The nested
/// release result has the ordinary release shape; proof data erases in Cargo.
#[allow(dead_code)]
pub struct ChildRelease<V,I> {pub release:ReleaseObservation<V,I>,retirement:Tracked<Option<Retirement>>}
impl<V,I> ChildRelease<V,I> {
    pub closed spec fn observation(&self)->ReleaseObservation<V,I> {self.release}
    pub fn into_release(self)->(out:ReleaseObservation<V,I>) ensures out==self.observation(), {self.release}
    pub proof fn retirement_witness(tracked &self)->(tracked out:&Option<Retirement>)
        ensures *out==self.retirement(),
    {self.retirement.borrow()}
    pub proof fn release_witness(tracked &self)->(tracked out:&ReleaseObservation<V,I>)
        ensures *out==self.observation(),
    {&self.release}
    pub closed spec fn retirement(&self)->Option<Retirement> {self.retirement@}
    pub open spec fn completed(&self,child:&SharedChild)->bool {
        super::released(self.observation()) && self.retirement().is_some()
            && self.retirement().unwrap().belongs_to(child)
            && self.retirement().unwrap().matches_unload(&self.observation().1@.unwrap())
    }
}

/// Constructed by the real successful retirement call. The persistent decision
/// names its exact shared request, while the receipt names the actual host.
#[allow(dead_code)]
pub tracked struct Retirement {
    decision:Decision,
    receipt:joint::Receipt,
    ghost native:nat,
    ghost domain:u64,
    ghost parent:usize,
    ghost parent_episode:Option<u64>,
}
impl Retirement {
    pub proof fn facts(&self) requires self.wf(),
        ensures self.checkpoint().wf(),self.checkpoint().event().key==self.native(),self.checkpoint().event().after is Native,
    {}

    pub open spec fn same_source(&self,other:&Self)->bool {
        self.wf() && other.wf() && self.source()==other.source() && self.decision()==other.decision()
            && self.checkpoint().same(&other.checkpoint()) && self.native()==other.native() && self.domain()==other.domain()
            && self.parent()==other.parent() && self.parent_episode()==other.parent_episode()
    }

    pub(crate) proof fn decision_witness(tracked &self)->(tracked out:&Decision)
        requires self.wf(),ensures out.wf(),out.state()==self.decision(),out.source()==self.source(),
    {&self.decision}

    pub proof fn duplicate(tracked &self)->(tracked out:Self)
        requires self.wf(),
        ensures out.same_source(self),out.wf(),out.source()==self.source(),out.decision()==self.decision(),out.checkpoint().same(&self.checkpoint()),
            out.native()==self.native(),out.domain()==self.domain(),out.parent()==self.parent(),out.parent_episode()==self.parent_episode(),
    {Self {decision:self.decision.duplicate(),receipt:self.receipt.duplicate(),native:self.native,domain:self.domain,parent:self.parent,parent_episode:self.parent_episode}}

    pub closed spec fn decision(&self)->ChildStatus<()> {self.decision.state()}
    pub closed spec fn source(&self)->Loc {self.decision.source()}
    pub closed spec fn checkpoint(&self)->joint::Receipt {self.receipt}
    pub closed spec fn native(&self)->nat {self.native}
    pub closed spec fn domain(&self)->u64 {self.domain}
    pub closed spec fn parent(&self)->usize {self.parent}
    pub closed spec fn parent_episode(&self)->Option<u64> {self.parent_episode}
    pub open spec fn state(&self)->native::State {self.checkpoint().event().after->Native_state}
    pub open spec fn belongs_to(&self,child:&SharedChild)->bool {
        self.wf() && child.wf() && self.source()==child.source() && self.domain()==child.domain_id()
            && self.parent()==child.owner() && self.parent_episode()==child.episode()
    }
    pub open spec fn assigned(&self)->bool {self.decision() is Assigned}
    pub open spec fn child(&self)->usize {self.decision()->Assigned_0.child()}
    pub open spec fn outstanding(&self)->Option<EpisodeOwner> {
        if self.assigned() && self.state().owners.contains_key(self.child()) {Some(self.state().owners[self.child()])} else {None}
    }
    pub open spec fn quiescent(&self)->bool {
        !self.assigned() || !self.state().owners.contains_key(self.child()) && !self.state().publications.contains_key(self.child())
    }
    pub closed spec fn wf(&self)->bool {
        &&& self.decision.wf() && self.checkpoint().wf()
        &&& self.checkpoint().event().key==self.native() && self.checkpoint().event().after is Native
        &&& self.assigned() ==> {
            let id=self.child();let state=self.state();let identity=self.decision()->Assigned_0;
            &&& identity.domain_id()==self.domain() && identity.owner()==self.parent()
            &&& crate::refinement::registered(state.control,id) ==> state.control.fibers[id].retired && state.control.fibers[id].parent==Some(self.parent())
            &&& state.owners.contains_key(id)==(crate::refinement::registered(state.control,id) && state.control.fibers[id].phase!=Phase::Inactive)
            &&& state.owners.contains_key(id) ==> state.owners[id].origin.id==id && state.owners[id].origin.domain==self.domain()
            &&& state.publications.contains_key(id) ==> state.owners.contains_key(id)
                && state.publications[id].origin==state.owners[id].origin && state.publications[id].work_domain==state.owners[id].work_domain
        }
    }
    /// Pending cancellation and prior rejection cannot later turn into an
    /// assignment of this same shared request, including competing dispatch.
    pub proof fn unassigned_stays_unassigned(tracked &self,tracked later:&ChildSnapshot)
        requires self.wf(),!self.assigned(),later.wf(),later.source()==self.source(),
        ensures !(later.state() is Assigned),
    {
        if later.state() is Assigned {self.decision.agrees(later);}
    }
    /// An already inactive or absent assigned Child has no outstanding episode
    /// or retained publication at this actual retirement observation.
    pub proof fn no_episode_is_quiescent(&self)
        requires self.wf(),self.outstanding().is_none(),
        ensures self.quiescent(),self.assigned() && crate::refinement::registered(self.state().control,self.child()) ==>
            self.state().control.fibers[self.child()].phase==Phase::Inactive && self.state().control.fibers[self.child()].retired,
    {}
    /// All fields refer to actual source receipts. In particular, equal numeric
    /// plugin IDs in another host, a parent's Unload, or another episode do not
    /// meet this relation. Order is explicit; retirement is not termination.
    pub open spec fn matches_unload(&self,end:&Unload)->bool {
        &&& self.wf() && self.outstanding().is_some() && end.wf()
        &&& end.native()==self.native() && end.checkpoint().follows(&self.checkpoint())
        &&& end.owner()==self.outstanding().unwrap()
        &&& crate::refinement::registered(end.before().control,self.child())
        &&& end.before().control.fibers[self.child()].parent==Some(self.parent()) && end.before().control.fibers[self.child()].retired
    }
    pub proof fn unload_releases_assigned_episode(&self,end:&Unload)
        requires self.matches_unload(end),
        ensures end.owner().origin.id==self.child(),end.owner().origin.domain==self.domain(),
            crate::refinement::registered(end.after().control,self.child()),end.after().control.fibers[self.child()].phase==Phase::Inactive,
            end.after().control.fibers[self.child()].parent==Some(self.parent()),end.after().control.fibers[self.child()].retired,
            !end.after().owners.contains_key(self.child()),!end.after().publications.contains_key(self.child()),
            !crate::refinement::relied(end.before().control,self.child()),
            end.cleanup_source(),
    {end.facts();}
    pub proof fn released_child_cannot_begin(&self,end:&Unload,next:crate::refinement::State)
        requires self.matches_unload(end),
        ensures !crate::refinement::step(end.after().control,next,self.child(),crate::refinement::Rule::Begin),
    {self.unload_releases_assigned_episode(end);}
    /// Apply the source relation to the exact successful production return,
    /// rather than accepting a caller-assembled terminal state.
    pub proof fn from_release<V,I>(&self,out:ReleaseObservation<V,I>)
        requires super::released(out),self.matches_unload(&out.1@.unwrap()),
        ensures !out.1@.unwrap().after().owners.contains_key(self.child())
            && !out.1@.unwrap().after().publications.contains_key(self.child())
            && out.1@.unwrap().after().control.fibers[self.child()].phase==Phase::Inactive
            && out.2@.unwrap().all_drained() && out.2@.unwrap().link()==out.1@.unwrap().cleanup_link(),
    {self.unload_releases_assigned_episode(&out.1@.unwrap());}
}
/// Choose an authentic prefix covering both local causes. The two witnesses
/// come from actual operations; comparison acquires no runtime lock.
pub(crate) proof fn release_cause(tracked groups:&Option<joint::Receipt>,tracked preceding:&Option<joint::Receipt>,journal:joint::Journal)->(tracked out:Option<joint::Receipt>)
    requires groups.is_some() ==> groups.unwrap().wf(),preceding.is_some() ==> preceding.unwrap().wf(),
    ensures out.is_some() ==> out.unwrap().wf() && out.unwrap().journal()==journal,
        groups.is_some() && groups.unwrap().journal()==journal ==> out.is_some() && out.unwrap().covers(&groups.unwrap()),
        preceding.is_some() && preceding.unwrap().journal()==journal ==> out.is_some() && out.unwrap().covers(&preceding.unwrap()),
{
    match (groups,preceding) {
        (Some(group),Some(prior))=>{
            if group.journal()==journal {
                if prior.journal()==journal {
                    group.compare(prior);
                    if group.covers(prior) {Some(group.duplicate())} else {Some(prior.duplicate())}
                } else {Some(group.duplicate())}
            } else if prior.journal()==journal {Some(prior.duplicate())} else {None}
        },
        (Some(group),None)=>if group.journal()==journal {Some(group.duplicate())} else {None},
        (None,Some(prior))=>if prior.journal()==journal {Some(prior.duplicate())} else {None},
        (None,None)=>None,
    }
}
impl<R,H,V> NativeRuntime<R,H,V> {
    /// An executable client composes the actual retirement and release calls.
    /// It checks episode ownership at runtime; callers supply no proof history.
    /// Cleanup/consumer guards may still reject release after successful Retire.
    pub fn retire_and_release_child<C,G,I>(&mut self,child:&SharedChild,execution:&mut crate::execution::Execution<V,C,G,I>)->(out:ChildRelease<V,I>)
        requires old(self).wf(),child.wf(),old(execution).wf(),
        ensures out.observation().0.is_ok() && old(self).child_records().has_birth(child) ==> final(self).child_records().resolved(child),
            out.retirement().is_some() && !out.retirement().unwrap().assigned() ==> final(self).child_records().resolved(child),
            final(self).child_records().extends(&old(self).child_records()),final(self).wf(),final(execution).wf(),final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.retirement().is_some() ==> out.retirement().unwrap().belongs_to(child),
            out.observation().0.is_err() ==> out.observation().1@.is_none() && out.observation().2@.is_none()
                && *final(execution)==*old(execution) && final(self).publications()==old(self).publications(),
            out.observation().0.is_ok() ==> out.completed(child)
                && out.observation().1@.unwrap().owner().origin.id==out.retirement().unwrap().child()
                && !out.observation().1@.unwrap().after().owners.contains_key(out.retirement().unwrap().child())
                && !out.observation().1@.unwrap().after().publications.contains_key(out.retirement().unwrap().child())
                && crate::refinement::registered(out.observation().1@.unwrap().after().control,out.retirement().unwrap().child())
                && out.observation().1@.unwrap().after().control.fibers[out.retirement().unwrap().child()].phase==Phase::Inactive
                && out.observation().1@.unwrap().after().control.fibers[out.retirement().unwrap().child()].retired,
    {
        let ghost original=self.child_records();
        let (transition,Tracked(retirement))=self.retire_shared_child_observed(child);
        let ghost retired=self.child_records();
        let identity=match transition.result {
            Ok(Some(identity))=>identity,
            Ok(None)=>return ChildRelease {release:(Err(Error::InvalidState),Tracked(None),Ghost(None)),retirement:Tracked(retirement)},
            Err(error)=>return ChildRelease {release:(Err(error),Tracked(None),Ghost(None)),retirement:Tracked(retirement)},
        };
        let id=identity.id();
        if !self.matches_execution(id,execution) {
            return ChildRelease {release:(Err(Error::InvalidState),Tracked(None),Ghost(None)),retirement:Tracked(retirement)};
        }
        proof {reveal(NativeRuntime::observation);reveal(crate::Kernel::registered);reveal(crate::Kernel::paper);
            assert(self.linked(id));assert(self.episode_owners().contains_key(id));
            assert(crate::refinement::registered(self.state().control().paper(),id));
            assert(self.registry().wf());assert(self.registry().entries().contains_key(id));
            assert(self.registry().recipe_matches(id));}
        let tracked source=match &retirement {Some(source)=>source,None=>{assert(false);proof_from_false()}};
        let release=self.release_retired_child(id,execution,Tracked(source));
        proof {
            self.child_records().transitive(&retired,&original);
            if release.0.is_ok() && original.has_birth(child) {
                self.children.borrow().finish_release(child,original.retirements().len() as int,retired.unloads().len() as int,
                    source,&release.1@.unwrap());
            }
        }
        ChildRelease {release,retirement:Tracked(retirement)}
    }
    /// Release the actual assigned episode against its retained retirement
    /// source. The real Unload commit follows both retirement and cleanup seal.
    /// No host callback's success or caller-supplied terminal state is accepted.
    pub fn release_retired_child<C,G,I>(&mut self,id:usize,execution:&mut crate::execution::Execution<V,C,G,I>,Tracked(retirement):Tracked<&Retirement>)->(out:ReleaseObservation<V,I>)
        requires old(self).wf(),old(execution).wf(),retirement.wf(),retirement.outstanding().is_some(),
            retirement.native()==old(self).joint_key(),retirement.checkpoint().journal()==old(self).journal_spec(),
            id==retirement.child(),old(self).episode_owners().contains_pair(id,retirement.outstanding().unwrap()),
            old(self).registry().entries().contains_key(id),old(self).registry().entries()[id].recipe().parent_id()==Some(retirement.parent()),
        ensures final(self).child_records().births()==old(self).child_records().births(),
            final(self).child_records().retirements()==old(self).child_records().retirements(),
            out.0.is_err() ==> final(self).child_records()==old(self).child_records(),
            out.0.is_ok() ==> final(self).child_records().unloads().len()==old(self).child_records().unloads().len()+1
                && final(self).child_records().unloads().last().same_source(&out.1@.unwrap()),
            final(self).child_records().extends(&old(self).child_records()),final(self).wf(),final(execution).wf(),final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.0.is_err() ==> out.1@.is_none() && out.2@.is_none() && *final(execution)==*old(execution)
                && final(self).publications()==old(self).publications(),
            out.0.is_ok() ==> super::released(out) && retirement.matches_unload(&out.1@.unwrap())
                && final(self).episode_owners()==old(self).episode_owners().remove(id)
                && final(self).publications().entries()==old(self).publications().entries().remove(id)
                && !out.1@.unwrap().after().owners.contains_key(id) && !out.1@.unwrap().after().publications.contains_key(id)
                && crate::refinement::registered(out.1@.unwrap().after().control,id)
                && out.1@.unwrap().after().control.fibers[id].phase==Phase::Inactive && out.1@.unwrap().after().control.fibers[id].retired
                && !crate::refinement::relied(out.1@.unwrap().before().control,id),
    {
        if !self.host.kernel().retired(id) {return (Err(Error::InvalidState),Tracked(None),Ghost(None));}
        proof {reveal(crate::Kernel::is_retired);reveal(crate::Kernel::paper);}
        let tracked cause=retirement.receipt.duplicate();
        let out=self.release_managed_execution_following(Tracked(Some(cause)),id,execution);
        proof {if out.0.is_ok() {retirement.from_release(out);}}
        out
    }
    pub(crate) proof fn child_retirement(tracked &self,child:&SharedChild,tracked snapshot:&ChildSnapshot)->(tracked out:Retirement)
        requires self.wf(),child.wf(),snapshot.wf(),snapshot.source()==child.source(),!(snapshot.state() is Pending),
            child.domain_id()==self.state().protocol().domain_id(),
            snapshot.state() is Assigned ==> {
                let identity=snapshot.state()->Assigned_0;
                &&& identity.domain_id()==child.domain_id() && identity.owner()==child.owner()
                &&& self.state().control().registered(identity.child()) ==> self.state().control().paper().fibers[identity.child()].retired
                    && self.state().control().paper().fibers[identity.child()].parent==Some(child.owner())
            },
        ensures out.wf(),out.source()==child.source(),out.decision()==snapshot.state(),
            out.parent()==child.owner(),out.parent_episode()==child.episode(),out.domain()==child.domain_id(),
            out.native()==self.joint_key(),out.checkpoint().journal()==self.journal_spec(),out.checkpoint().events()==self.joint_events(),
            out.state()==self.observation().project(self.execution_history().labels.len()),
    {
        reveal(NativeRuntime::joint_valid);reveal(NativeRuntime::observation);
        reveal(crate::Kernel::registered);reveal(crate::Kernel::paper);
        if snapshot.state() is Assigned {assert(self.linked(snapshot.state()->Assigned_0.child()));}
        let tracked decision=snapshot.retain_decision();let tracked receipt=self.joint.receipt();
        Retirement {decision,receipt,native:self.joint_key(),domain:child.domain_id(),parent:child.owner(),parent_episode:child.episode()}
    }
}
}
