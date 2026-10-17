//! Join the actual published and Begin-captured service slots to a Journal
//! checkpoint. Collection takes slot locks first; certification takes only the
//! Journal read lock. Opaque payloads are never cloned, dropped or called here.
use super::{NativeEpisode, NativePublication, NativeServices};
use crate::reversible_value::joint;
use crate::reversible_value::slot::{Evidence, ServiceSlot};
use std::collections::BTreeMap;
use std::sync::Arc;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn observed<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {
    forall|k:K| values.contains_key(k) && #[trigger] values[k].managed().is_some() ==>
        values[k].managed().unwrap().observed_state(journal,state)
}
/// Explicit boundary of the production service interpretation. Opaque host
/// payloads and foreign slots remain present without acquiring scalar meaning.
pub enum ServiceObservation {
    Opaque,
    ForeignSlot {domain:vstd::resource::Loc,key:nat},
    Managed {resolution:joint::references::Resolution},
}
pub open spec fn service<T,M>(value:Arc<ServiceSlot<T,M>>,journal:joint::Journal,state:Map<nat,joint::Record>)->Option<ServiceObservation> {
    match value.managed() {
        None=>Some(ServiceObservation::Opaque),
        Some(slot)=>if slot.journal_spec()!=journal {
            Some(ServiceObservation::ForeignSlot {domain:slot.journal_spec().source(),key:slot.key()})
        } else {match joint::references::resolve(state,journal.source(),slot.key()) {
            Some(resolution)=>Some(ServiceObservation::Managed {resolution}),None=>None,
        }},
    }
}
/// The domain is exactly the actual service map, including retained imports.
pub open spec fn projection<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>)->Map<K,Option<ServiceObservation>> {
    Map::new(values.dom(),|key:K|service(values[key],journal,state))
}
pub open spec fn complete<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {
    forall|key:K| values.contains_key(key) ==> #[trigger] projection(values,journal,state)[key].is_some()
}
pub proof fn project_observed<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>)
    requires observed(values,journal,state),
    ensures complete(values,journal,state),projection(values,journal,state).dom()==values.dom(),
{
    assert forall|key:K| values.contains_key(key) implies #[trigger] projection(values,journal,state)[key].is_some() by {
        if values[key].managed().is_some() {
            let slot=values[key].managed().unwrap();assert(slot.observed_state(journal,state));
        }
    }
}
/// Alias closure is calculated at the actual write position, after any slot
/// replacement that preceded it. A retained write can affect no current port.
pub open spec fn affected<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>,object:nat)->Set<K> {
    values.dom().filter(|key:K| match service(values[key],journal,state) {
        Some(ServiceObservation::Managed {resolution:joint::references::Resolution::Local {selection,..}})=>selection.object.key==object,
        _=>false,
    })
}
pub open spec fn value_frame<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,journal:joint::Journal,before:Map<nat,joint::Record>,after:Map<nat,joint::Record>,object:nat)->bool {
    projection(values,journal,after).dom()==projection(values,journal,before).dom()
        && forall|key:K| values.contains_key(key) && !affected(values,journal,before,object).contains(key) ==>
            #[trigger] projection(values,journal,after)[key]==projection(values,journal,before)[key]
}
/// Lift an actual object event to all current service observations, without a
/// caller-provided coherent heap or an assumption that port names do not alias.
pub proof fn project_value_step<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,journal:joint::Journal,before:Map<nat,joint::Record>,after:Map<nat,joint::Record>,event:joint::Step)
    requires joint::step(before,after,event),event.change is Value,
    ensures value_frame(values,journal,before,after,event.key),
        forall|key:K| affected(values,journal,before,event.key).contains(key) ==> {
            let old=projection(values,journal,before)[key].unwrap()->Managed_resolution;
            #[trigger] projection(values,journal,after)[key]==Some(ServiceObservation::Managed {resolution:joint::references::Resolution::Local {
                selection:old->Local_selection,source:old->Local_source,state:event.change->Value_event.after()}})
        },
{
    reveal(joint::changes);
    assert forall|key:K| values.contains_key(key) && !affected(values,journal,before,event.key).contains(key) implies
        #[trigger] projection(values,journal,after)[key]==projection(values,journal,before)[key] by {
        if values[key].managed().is_some() {
            let slot=values[key].managed().unwrap();
            if slot.journal_spec()==journal {
                if slot.key()==event.key {assert(!(before[slot.key()] is Slot));}
                else if before.contains_key(slot.key()) && before[slot.key()] is Slot {
                    assert(after[slot.key()]==before[slot.key()]);
                }
            }
        }
    }
    assert forall|key:K| affected(values,journal,before,event.key).contains(key) implies {
        let old=projection(values,journal,before)[key].unwrap()->Managed_resolution;
        #[trigger] projection(values,journal,after)[key]==Some(ServiceObservation::Managed {resolution:joint::references::Resolution::Local {
            selection:old->Local_selection,source:old->Local_source,state:event.change->Value_event.after()}})
    } by {
        let slot=values[key].managed().unwrap();assert(slot.key()!=event.key);
    }
}
/// A port-level frame requires this explicit alias-closure condition. The
/// theorem does not promote a declaration on one alias into another declaration.
pub proof fn declared_frame<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,journal:joint::Journal,before:Map<nat,joint::Record>,after:Map<nat,joint::Record>,event:joint::Step,writes:Set<K>)
    requires joint::step(before,after,event),event.change is Value,affected(values,journal,before,event.key).subset_of(writes),
    ensures forall|key:K| values.contains_key(key) && !writes.contains(key) ==>
        #[trigger] projection(values,journal,after)[key]==projection(values,journal,before)[key],
{project_value_step(values,journal,before,after,event);}
pub(crate) open spec fn covered<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,evidence:Evidence)->bool {
    forall|k:K| values.contains_key(k) && #[trigger] values[k].managed().is_some() ==> evidence.contains(values[k].managed().unwrap())
}
fn collect<K:Ord,T,M>(values:&BTreeMap<K,Arc<ServiceSlot<T,M>>>,evidence:&mut Evidence)
    requires old(evidence).wf(),vstd::std_specs::btree::key_obeys_cmp_spec::<K>(),
    ensures final(evidence).wf(),covered(values@,*final(evidence)),
        forall|s:crate::reversible_value::slot::Slot| old(evidence).contains(s) ==> final(evidence).contains(s),
{
    let iterator=values.values();let ghost sequence=iterator.remaining();
    for value in iter: iterator
        invariant evidence.wf(),iter.seq()==sequence,
            forall|s:crate::reversible_value::slot::Slot| old(evidence).contains(s) ==> evidence.contains(s),
            forall|j:int| 0<=j<iter.index() && #[trigger] sequence[j].managed().is_some() ==> evidence.contains(sequence[j].managed().unwrap()),
    {
        if let Some(slot)=value.reversible() {evidence.add(slot);}
    }
    proof {
        assert forall|k:K| values@.contains_key(k) && #[trigger] values@[k].managed().is_some() implies evidence.contains(values@[k].managed().unwrap()) by {
            assert(values@.values().contains(values@[k]));
            assert(sequence.unref().to_set().contains(values@[k]));
            let i=choose|i:int| 0<=i<sequence.len() && sequence.unref()[i]==values@[k];
            assert(sequence[i].managed()==values@[k].managed());
        }
    }
}
proof fn covered_extends<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,prior:Evidence,later:Evidence)
    requires covered(values,prior),forall|s:crate::reversible_value::slot::Slot| prior.contains(s) ==> later.contains(s),
    ensures covered(values,later),
{
    assert forall|k:K| values.contains_key(k) && #[trigger] values[k].managed().is_some() implies later.contains(values[k].managed().unwrap()) by {
        assert(prior.contains(values[k].managed().unwrap()));
    }
}
proof fn covered_observed<K,T,M>(values:Map<K,Arc<ServiceSlot<T,M>>>,evidence:Evidence,journal:joint::Journal,state:Map<nat,joint::Record>)
    requires covered(values,evidence),forall|s:crate::reversible_value::slot::Slot| evidence.contains(s) ==> #[trigger] s.observed_state(journal,state),
    ensures observed(values,journal,state),
{
    assert forall|k:K| values.contains_key(k) && #[trigger] values[k].managed().is_some() implies values[k].managed().unwrap().observed_state(journal,state) by {
        assert(evidence.contains(values[k].managed().unwrap()));
    }
}

impl<T,M> NativePublication<ServiceSlot<T,M>> {
    pub open spec fn slots_observed(&self,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {observed(self.values(),journal,state)}
    pub open spec fn observation(&self,snapshot:&joint::Snapshot)->Map<(u64,u64),Option<ServiceObservation>> {
        projection(self.values(),snapshot.journal_spec(),snapshot.last())
    }
    pub proof fn observation_complete(&self,snapshot:&joint::Snapshot)
        requires snapshot.certified(),self.slots_observed(snapshot.journal_spec(),snapshot.last()),
        ensures self.observation(snapshot).dom()==self.values().dom(),complete(self.values(),snapshot.journal_spec(),snapshot.last()),
    {project_observed(self.values(),snapshot.journal_spec(),snapshot.last());}
    pub(crate) open spec fn slots_covered(&self,evidence:Evidence)->bool {covered(self.values(),evidence)}
    fn collect_slots(&self,evidence:&mut Evidence)
        requires old(evidence).wf(),
        ensures final(evidence).wf(),self.slots_covered(*final(evidence)),
            forall|s:crate::reversible_value::slot::Slot| old(evidence).contains(s) ==> final(evidence).contains(s),
    {collect(&self.values,evidence);}
}
impl<T,M> NativeServices<ServiceSlot<T,M>> {
    pub open spec fn slots_observed(&self,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {
        forall|id:usize| self.entries().contains_key(id) ==> #[trigger] self.entries()[id].slots_observed(journal,state)
    }
    pub open spec fn observations_complete(&self,snapshot:&joint::Snapshot)->bool {
        forall|id:usize| self.entries().contains_key(id) ==> complete(#[trigger] self.entries()[id].values(),snapshot.journal_spec(),snapshot.last())
    }
    pub proof fn project_observations(&self,snapshot:&joint::Snapshot)
        requires snapshot.certified(),self.slots_observed(snapshot.journal_spec(),snapshot.last()),
        ensures self.observations_complete(snapshot),
    {
        assert forall|id:usize| self.entries().contains_key(id) implies complete(#[trigger] self.entries()[id].values(),snapshot.journal_spec(),snapshot.last()) by {
            assert(self.entries()[id].slots_observed(snapshot.journal_spec(),snapshot.last()));
            self.entries()[id].observation_complete(snapshot);
        }
    }
    pub(crate) open spec fn slots_covered(&self,evidence:Evidence)->bool {
        forall|id:usize| self.entries().contains_key(id) ==> #[trigger] self.entries()[id].slots_covered(evidence)
    }
    pub(crate) fn collect_slots(&self,evidence:&mut Evidence)
        requires old(evidence).wf(),
        ensures final(evidence).wf(),self.slots_covered(*final(evidence)),
            forall|s:crate::reversible_value::slot::Slot| old(evidence).contains(s) ==> final(evidence).contains(s),
    {
        let iterator=self.entries.values();let ghost sequence=iterator.remaining();
        for publication in iter: iterator
            invariant evidence.wf(),iter.seq()==sequence,
                forall|s:crate::reversible_value::slot::Slot| old(evidence).contains(s) ==> evidence.contains(s),
                forall|j:int| 0<=j<iter.index() ==> #[trigger] sequence[j].slots_covered(*evidence),
        {
            let ghost prior=*evidence;publication.collect_slots(evidence);
            proof {
                assert forall|j:int| 0<=j<iter.index() implies #[trigger] sequence[j].slots_covered(*evidence) by {
                    assert(sequence[j].slots_covered(prior));
                    covered_extends(sequence[j].values(),prior,*evidence);
                }
            }
        }
        proof {
            assert forall|id:usize| self.entries().contains_key(id) implies #[trigger] self.entries()[id].slots_covered(*evidence) by {
                assert(self.entries@.values().contains(self.entries()[id]));
                assert(sequence.unref().to_set().contains(self.entries()[id]));
                let i=choose|i:int| 0<=i<sequence.len() && sequence.unref()[i]==self.entries()[id];
                assert(sequence[i].slots_covered(*evidence));
            }
        }
    }
    pub(crate) proof fn slots_coverage_extends(&self,prior:Evidence,later:Evidence)
        requires self.slots_covered(prior),forall|s:crate::reversible_value::slot::Slot| prior.contains(s) ==> later.contains(s),
        ensures self.slots_covered(later),
    {
        assert forall|id:usize| self.entries().contains_key(id) implies #[trigger] self.entries()[id].slots_covered(later) by {
            assert(self.entries()[id].slots_covered(prior));
            covered_extends(self.entries()[id].values(),prior,later);
        }
    }
    pub(crate) proof fn slots_certified(&self,evidence:Evidence,journal:joint::Journal,state:Map<nat,joint::Record>)
        requires self.slots_covered(evidence),forall|s:crate::reversible_value::slot::Slot| evidence.contains(s) ==> #[trigger] s.observed_state(journal,state),
        ensures self.slots_observed(journal,state),
    {
        assert forall|id:usize| self.entries().contains_key(id) implies #[trigger] self.entries()[id].slots_observed(journal,state) by {
            assert(self.entries()[id].slots_covered(evidence));
            covered_observed(self.entries()[id].values(),evidence,journal,state);
        }
    }
}
impl<T,M> NativeEpisode<ServiceSlot<T,M>> {
    pub open spec fn slots_observed(&self,journal:joint::Journal,state:Map<nat,joint::Record>)->bool {
        observed(self.owned(),journal,state) && observed(self.imports(),journal,state)
    }
    pub open spec fn owned_observation(&self,snapshot:&joint::Snapshot)->Map<(u64,u64),Option<ServiceObservation>> {
        projection(self.owned(),snapshot.journal_spec(),snapshot.last())
    }
    pub open spec fn imported_observation(&self,snapshot:&joint::Snapshot)->Map<(usize,u64,u64),Option<ServiceObservation>> {
        projection(self.imports(),snapshot.journal_spec(),snapshot.last())
    }
    pub open spec fn observations_complete(&self,snapshot:&joint::Snapshot)->bool {
        complete(self.owned(),snapshot.journal_spec(),snapshot.last()) && complete(self.imports(),snapshot.journal_spec(),snapshot.last())
    }
    pub proof fn project_observations(&self,snapshot:&joint::Snapshot)
        requires snapshot.certified(),self.slots_observed(snapshot.journal_spec(),snapshot.last()),
        ensures self.observations_complete(snapshot),self.owned_observation(snapshot).dom()==self.owned().dom(),
            self.imported_observation(snapshot).dom()==self.imports().dom(),
    {project_observed(self.owned(),snapshot.journal_spec(),snapshot.last());project_observed(self.imports(),snapshot.journal_spec(),snapshot.last());}
    pub(crate) open spec fn slots_covered(&self,evidence:Evidence)->bool {
        covered(self.owned(),evidence) && covered(self.imports(),evidence)
    }
    pub(crate) fn collect_slots(&self,evidence:&mut Evidence)
        requires old(evidence).wf(),
        ensures final(evidence).wf(),covered(self.owned(),*final(evidence)) && covered(self.imports(),*final(evidence)),
            forall|s:crate::reversible_value::slot::Slot| old(evidence).contains(s) ==> final(evidence).contains(s),
    {
        collect(&self.owned,evidence);let ghost prior=*evidence;collect(&self.imports,evidence);
        proof {covered_extends(self.owned(),prior,*evidence);}
    }
    pub(crate) proof fn slots_certified(&self,evidence:Evidence,journal:joint::Journal,state:Map<nat,joint::Record>)
        requires self.slots_covered(evidence),forall|s:crate::reversible_value::slot::Slot| evidence.contains(s) ==> #[trigger] s.observed_state(journal,state),
        ensures self.slots_observed(journal,state),
    {covered_observed(self.owned(),evidence,journal,state);covered_observed(self.imports(),evidence,journal,state);}
}
}
