//! Actual non-scalar payload owners in publication and captured Episode maps.
//! Collection acquires each payload lock before the common Journal read epoch.
//! This is identity/version correspondence; arbitrary interior state is opaque.
use super::{NativeEpisode, NativePublication, NativeServices};
use crate::reversible_value::joint;
use crate::reversible_value::payload::{Evidence, SharedPayload};
use crate::reversible_value::slot::ServiceSlot;
use std::collections::BTreeMap;
use std::sync::Arc;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn observed<K,T:?Sized,M>(values:Map<K,Arc<ServiceSlot<SharedPayload<T>,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {
    forall|k:K| values.contains_key(k) && #[trigger] values[k].opaque_spec().is_some() ==>
        values[k].opaque_spec().unwrap().observed_state(journal,state)
}
/// The complete production service map distinguishes scalar resolution from
/// typed payload identity/version. Foreign owners retain their own domain.
pub enum ServiceObservation {
    Reversible {resolution:joint::references::Resolution},
    ForeignSlot {domain:vstd::resource::Loc,key:nat},
    Payload {source:vstd::resource::Loc,key:nat,revision:u64},
    RetiredPayload {source:vstd::resource::Loc,key:nat,revision:u64},
    ForeignPayload {domain:vstd::resource::Loc,key:nat},
}
pub open spec fn service<T:?Sized,M>(value:Arc<ServiceSlot<SharedPayload<T>,M>>,journal:joint::Journal,state:Map<nat,joint::Record>)->Option<ServiceObservation> {
    if value.opaque_spec().is_some() {
        let owner=value.opaque_spec().unwrap();
        if owner.journal_spec()!=journal {Some(ServiceObservation::ForeignPayload {domain:owner.journal_spec().source(),key:owner.key()})}
        else if state.contains_key(owner.key()) && state[owner.key()] is Payload {
            Some(ServiceObservation::Payload {source:state[owner.key()]->Payload_source,key:owner.key(),revision:state[owner.key()]->Payload_revision})
        } else if state.contains_key(owner.key()) && state[owner.key()] is RetiredPayload {
            Some(ServiceObservation::RetiredPayload {source:state[owner.key()]->RetiredPayload_source,key:owner.key(),revision:state[owner.key()]->RetiredPayload_revision})
        } else {None}
    } else {match super::slots::service(value,journal,state) {
        Some(super::slots::ServiceObservation::Managed {resolution})=>Some(ServiceObservation::Reversible {resolution}),
        Some(super::slots::ServiceObservation::ForeignSlot {domain,key})=>Some(ServiceObservation::ForeignSlot {domain,key}),
        _=>None,
    }}
}
pub open spec fn projection<K,T:?Sized,M>(values:Map<K,Arc<ServiceSlot<SharedPayload<T>,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>)->Map<K,Option<ServiceObservation>> {
    Map::new(values.dom(),|key:K|service(values[key],journal,state))
}
pub open spec fn complete<K,T:?Sized,M>(values:Map<K,Arc<ServiceSlot<SharedPayload<T>,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {
    forall|key:K| values.contains_key(key) ==> #[trigger] projection(values,journal,state)[key].is_some()
}
pub proof fn project_observed<K,T:?Sized,M>(values:Map<K,Arc<ServiceSlot<SharedPayload<T>,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>)
    requires observed(values,journal,state),super::slots::observed(values,journal,state),
    ensures complete(values,journal,state),projection(values,journal,state).dom()==values.dom(),
{
    assert forall|key:K| values.contains_key(key) implies #[trigger] projection(values,journal,state)[key].is_some() by {
        values[key].payload_partition();
        if values[key].opaque_spec().is_some() {assert(values[key].opaque_spec().unwrap().observed_state(journal,state));}
        else {assert(values[key].managed().unwrap().observed_state(journal,state));}
    }
}
pub open spec fn affected<K,T:?Sized,M>(values:Map<K,Arc<ServiceSlot<SharedPayload<T>,M>>>,journal:joint::Journal,key:nat)->Set<K> {
    values.dom().filter(|k:K| values[k].opaque_spec().is_some()
        && values[k].opaque_spec().unwrap().journal_spec()==journal && values[k].opaque_spec().unwrap().key()==key)
}
/// Every current alias of the replaced payload changes version; all other
/// scalar and typed service observations are framed. Port names alone do not
/// prove independence, and equal payload contents do not erase a replacement.
pub proof fn project_replacement<K,T:?Sized,M>(values:Map<K,Arc<ServiceSlot<SharedPayload<T>,M>>>,journal:joint::Journal,before:Map<nat,joint::Record>,after:Map<nat,joint::Record>,event:joint::Step)
    requires joint::step(before,after,event),joint::payload::mutation(event.change),
    ensures forall|k:K| values.contains_key(k) && !affected(values,journal,event.key).contains(k) ==>
        #[trigger] projection(values,journal,after)[k]==projection(values,journal,before)[k],
        forall|k:K| affected(values,journal,event.key).contains(k) ==> #[trigger] projection(values,journal,after)[k]==Some(ServiceObservation::Payload {
            source:event.after->Payload_source,key:event.key,revision:event.after->Payload_revision}),
{
    reveal(joint::changes);
    assert forall|k:K| values.contains_key(k) && !affected(values,journal,event.key).contains(k) implies
        #[trigger] projection(values,journal,after)[k]==projection(values,journal,before)[k] by {}
}
pub(crate) open spec fn covered<K,T:?Sized,M>(values:Map<K,Arc<ServiceSlot<SharedPayload<T>,M>>>,evidence:Evidence<T>)->bool {
    forall|k:K| values.contains_key(k) && #[trigger] values[k].opaque_spec().is_some() ==> evidence.contains(values[k].opaque_spec().unwrap())
}
fn collect<K:Ord,T:?Sized,M>(values:&BTreeMap<K,Arc<ServiceSlot<SharedPayload<T>,M>>>,evidence:&mut Evidence<T>)
    requires old(evidence).wf(),vstd::std_specs::btree::key_obeys_cmp_spec::<K>(),
    ensures final(evidence).wf(),covered(values@,*final(evidence)),
        forall|s:SharedPayload<T>| old(evidence).contains(s) ==> final(evidence).contains(s),
{
    let iterator=values.values();let ghost sequence=iterator.remaining();
    for value in iter: iterator
        invariant evidence.wf(),iter.seq()==sequence,
            forall|s:SharedPayload<T>| old(evidence).contains(s) ==> evidence.contains(s),
            forall|j:int| 0<=j<iter.index() && #[trigger] sequence[j].opaque_spec().is_some() ==> evidence.contains(sequence[j].opaque_spec().unwrap()),
    {
        if let Some(slot)=value.opaque() {evidence.add(slot);}
    }
    proof {
        assert forall|k:K| values@.contains_key(k) && #[trigger] values@[k].opaque_spec().is_some() implies evidence.contains(values@[k].opaque_spec().unwrap()) by {
            assert(values@.values().contains(values@[k]));
            assert(sequence.unref().to_set().contains(values@[k]));
            let i=choose|i:int| 0<=i<sequence.len() && sequence.unref()[i]==values@[k];
            assert(sequence[i].opaque_spec()==values@[k].opaque_spec());
        }
    }
}
proof fn covered_extends<K,T:?Sized,M>(values:Map<K,Arc<ServiceSlot<SharedPayload<T>,M>>>,prior:Evidence<T>,later:Evidence<T>)
    requires covered(values,prior),forall|s:SharedPayload<T>| prior.contains(s) ==> later.contains(s),
    ensures covered(values,later),
{
    assert forall|k:K| values.contains_key(k) && #[trigger] values[k].opaque_spec().is_some() implies later.contains(values[k].opaque_spec().unwrap()) by {
        assert(prior.contains(values[k].opaque_spec().unwrap()));
    }
}
proof fn covered_observed<K,T:?Sized,M>(values:Map<K,Arc<ServiceSlot<SharedPayload<T>,M>>>,evidence:Evidence<T>,journal:joint::Journal,state:Map<nat,joint::Record>)
    requires covered(values,evidence),forall|s:SharedPayload<T>| evidence.contains(s) ==> #[trigger] s.observed_state(journal,state),
    ensures observed(values,journal,state),
{
    assert forall|k:K| values.contains_key(k) && #[trigger] values[k].opaque_spec().is_some() implies values[k].opaque_spec().unwrap().observed_state(journal,state) by {
        assert(evidence.contains(values[k].opaque_spec().unwrap()));
    }
}

impl<T:?Sized,M> NativePublication<ServiceSlot<SharedPayload<T>,M>> {
    pub open spec fn payloads_observed(&self,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {observed(self.values(),journal,state)}
    pub open spec fn payload_observation(&self,snapshot:&joint::Snapshot)->Map<(u64,u64),Option<ServiceObservation>> {
        projection(self.values(),snapshot.journal_spec(),snapshot.last())
    }
    pub proof fn project_payloads(&self,snapshot:&joint::Snapshot)
        requires snapshot.certified(),self.payloads_observed(snapshot.journal_spec(),snapshot.last()),self.slots_observed(snapshot.journal_spec(),snapshot.last()),
        ensures complete(self.values(),snapshot.journal_spec(),snapshot.last()),self.payload_observation(snapshot).dom()==self.values().dom(),
    {project_observed(self.values(),snapshot.journal_spec(),snapshot.last());}
    pub(crate) open spec fn payloads_covered(&self,evidence:Evidence<T>)->bool {covered(self.values(),evidence)}
    fn collect_payloads(&self,evidence:&mut Evidence<T>)
        requires old(evidence).wf(),
        ensures final(evidence).wf(),self.payloads_covered(*final(evidence)),
            forall|s:SharedPayload<T>| old(evidence).contains(s) ==> final(evidence).contains(s),
    {collect(&self.values,evidence);}
}
impl<T:?Sized,M> NativeServices<ServiceSlot<SharedPayload<T>,M>> {
    pub open spec fn payload_projections_complete(&self,snapshot:&joint::Snapshot)->bool {
        forall|id:usize| self.entries().contains_key(id) ==> complete(#[trigger] self.entries()[id].values(),snapshot.journal_spec(),snapshot.last())
    }
    pub proof fn project_payloads(&self,snapshot:&joint::Snapshot)
        requires snapshot.certified(),self.payloads_observed(snapshot.journal_spec(),snapshot.last()),self.slots_observed(snapshot.journal_spec(),snapshot.last()),
        ensures self.payload_projections_complete(snapshot),
    {
        assert forall|id:usize| self.entries().contains_key(id) implies complete(#[trigger] self.entries()[id].values(),snapshot.journal_spec(),snapshot.last()) by {
            assert(self.entries()[id].payloads_observed(snapshot.journal_spec(),snapshot.last()));
            assert(self.entries()[id].slots_observed(snapshot.journal_spec(),snapshot.last()));
            self.entries()[id].project_payloads(snapshot);
        }
    }
    pub open spec fn payloads_observed(&self,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {
        forall|id:usize| self.entries().contains_key(id) ==> #[trigger] self.entries()[id].payloads_observed(journal,state)
    }
    pub(crate) open spec fn payloads_covered(&self,evidence:Evidence<T>)->bool {
        forall|id:usize| self.entries().contains_key(id) ==> #[trigger] self.entries()[id].payloads_covered(evidence)
    }
    pub(crate) fn collect_payloads(&self,evidence:&mut Evidence<T>)
        requires old(evidence).wf(),
        ensures final(evidence).wf(),self.payloads_covered(*final(evidence)),
            forall|s:SharedPayload<T>| old(evidence).contains(s) ==> final(evidence).contains(s),
    {
        let iterator=self.entries.values();let ghost sequence=iterator.remaining();
        for publication in iter: iterator
            invariant evidence.wf(),iter.seq()==sequence,
                forall|s:SharedPayload<T>| old(evidence).contains(s) ==> evidence.contains(s),
                forall|j:int| 0<=j<iter.index() ==> #[trigger] sequence[j].payloads_covered(*evidence),
        {
            let ghost prior=*evidence;publication.collect_payloads(evidence);
            proof {
                assert forall|j:int| 0<=j<iter.index() implies #[trigger] sequence[j].payloads_covered(*evidence) by {
                    assert(sequence[j].payloads_covered(prior));
                    covered_extends(sequence[j].values(),prior,*evidence);
                }
            }
        }
        proof {
            assert forall|id:usize| self.entries().contains_key(id) implies #[trigger] self.entries()[id].payloads_covered(*evidence) by {
                assert(self.entries@.values().contains(self.entries()[id]));
                assert(sequence.unref().to_set().contains(self.entries()[id]));
                let i=choose|i:int| 0<=i<sequence.len() && sequence.unref()[i]==self.entries()[id];
                assert(sequence[i].payloads_covered(*evidence));
            }
        }
    }
    pub(crate) proof fn payloads_coverage_extends(&self,prior:Evidence<T>,later:Evidence<T>)
        requires self.payloads_covered(prior),forall|s:SharedPayload<T>| prior.contains(s) ==> later.contains(s),
        ensures self.payloads_covered(later),
    {
        assert forall|id:usize| self.entries().contains_key(id) implies #[trigger] self.entries()[id].payloads_covered(later) by {
            assert(self.entries()[id].payloads_covered(prior));
            covered_extends(self.entries()[id].values(),prior,later);
        }
    }
    pub(crate) proof fn payloads_certified(&self,evidence:Evidence<T>,journal:joint::Journal,state:Map<nat,joint::Record>)
        requires self.payloads_covered(evidence),forall|s:SharedPayload<T>| evidence.contains(s) ==> #[trigger] s.observed_state(journal,state),
        ensures self.payloads_observed(journal,state),
    {
        assert forall|id:usize| self.entries().contains_key(id) implies #[trigger] self.entries()[id].payloads_observed(journal,state) by {
            assert(self.entries()[id].payloads_covered(evidence));
            covered_observed(self.entries()[id].values(),evidence,journal,state);
        }
    }
}
impl<T:?Sized,M> NativeEpisode<ServiceSlot<SharedPayload<T>,M>> {
    pub open spec fn owned_payload_observation(&self,snapshot:&joint::Snapshot)->Map<(u64,u64),Option<ServiceObservation>> {
        projection(self.owned(),snapshot.journal_spec(),snapshot.last())
    }
    pub open spec fn imported_payload_observation(&self,snapshot:&joint::Snapshot)->Map<(usize,u64,u64),Option<ServiceObservation>> {
        projection(self.imports(),snapshot.journal_spec(),snapshot.last())
    }
    pub open spec fn payload_projections_complete(&self,snapshot:&joint::Snapshot)->bool {
        complete(self.owned(),snapshot.journal_spec(),snapshot.last()) && complete(self.imports(),snapshot.journal_spec(),snapshot.last())
    }
    pub proof fn project_payloads(&self,snapshot:&joint::Snapshot)
        requires snapshot.certified(),self.payloads_observed(snapshot.journal_spec(),snapshot.last()),self.slots_observed(snapshot.journal_spec(),snapshot.last()),
        ensures self.payload_projections_complete(snapshot),self.owned_payload_observation(snapshot).dom()==self.owned().dom(),
            self.imported_payload_observation(snapshot).dom()==self.imports().dom(),
    {project_observed(self.owned(),snapshot.journal_spec(),snapshot.last());project_observed(self.imports(),snapshot.journal_spec(),snapshot.last());}
    pub open spec fn payloads_observed(&self,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {
        observed(self.owned(),journal,state) && observed(self.imports(),journal,state)
    }
    pub(crate) open spec fn payloads_covered(&self,evidence:Evidence<T>)->bool {
        covered(self.owned(),evidence) && covered(self.imports(),evidence)
    }
    pub(crate) fn collect_payloads(&self,evidence:&mut Evidence<T>)
        requires old(evidence).wf(),
        ensures final(evidence).wf(),covered(self.owned(),*final(evidence)) && covered(self.imports(),*final(evidence)),
            forall|s:SharedPayload<T>| old(evidence).contains(s) ==> final(evidence).contains(s),
    {
        collect(&self.owned,evidence);let ghost prior=*evidence;collect(&self.imports,evidence);
        proof {covered_extends(self.owned(),prior,*evidence);}
    }
    pub(crate) proof fn payloads_certified(&self,evidence:Evidence<T>,journal:joint::Journal,state:Map<nat,joint::Record>)
        requires self.payloads_covered(evidence),forall|s:SharedPayload<T>| evidence.contains(s) ==> #[trigger] s.observed_state(journal,state),
        ensures self.payloads_observed(journal,state),
    {covered_observed(self.owned(),evidence,journal,state);covered_observed(self.imports(),evidence,journal,state);}
}
}
