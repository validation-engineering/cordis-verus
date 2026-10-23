//! Publication routes are data, not cleanup ownership. A call may publish many
//! services while its single original cleanup owner remains with the caller.
use super::super::Slot;
use super::batch::Provider;
#[cfg(verus_keep_ghost)]
use super::{bank::Bank, slots::Slots};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::services::{NativeEpisode, NativePublication};
use crate::Port;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub struct Service<T:?Sized> {pub id:usize,pub port:Port,pub index:usize,pub slot:Option<usize>,pub source_origin:Option<crate::action_ledger::ActionTicket>,pub service:Arc<Slot<T,()>>}
impl<T:?Sized> Service<T> {
    pub open spec fn mapped(&self,bank:&Bank<T>,slots:&Slots<T>)->bool {
        self.index<bank.len_spec() && match self.slot {
            Some(i)=>i<slots.len_spec() && self.service==slots.service(i as int) && self.index==slots.initial(i as int),
            None=>self.service==bank.service(self.index as int),
        }
    }
    pub fn duplicate(&self)->(out:Self) ensures out==*self,
    {Self {id:self.id,port:self.port,index:self.index,slot:self.slot,source_origin:self.source_origin,service:self.service.clone()}}
    pub fn from_provider<E>(p:&Provider<E,T>)->(out:Self)
        ensures out.id==p.id,out.port==p.port,out.index==p.index,out.slot==p.slot,out.service==p.service,out.source_origin==p.source_origin,
    {Self {id:p.id,port:p.port,index:p.index,slot:p.slot,source_origin:p.source_origin,service:p.service.clone()}}
}
pub open spec fn published<T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,services:Seq<Service<T>>,sources:Map<usize,crate::lifecycle_state::services::capture::Source<Slot<T,()>>>)->bool {
    forall|i:int|0<=i<services.len() ==> {
        let s=#[trigger] services[i];
        &&& s.mapped(bank,slots) && sources.contains_key(s.id) && sources[s.id].values.contains_pair((s.port.key,s.port.realm),s.service)
    }
}
pub open spec fn owned<T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,services:Seq<Service<T>>,episode:NativeEpisode<Slot<T,()>>)->bool {
    forall|i:int|0<=i<services.len() ==> {
        let s=#[trigger] services[i];
        &&& s.mapped(bank,slots) && s.id==episode.origin().id && episode.provisions().contains(s.port)
        &&& episode.owned().contains_pair((s.port.key,s.port.realm),s.service)
    }
}
pub proof fn preserve<T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,services:Seq<Service<T>>,before:Map<usize,NativePublication<Slot<T,()>>>,after:Map<usize,NativePublication<Slot<T,()>>>)
    requires published(bank,slots,services,crate::lifecycle_state::services::capture::sources(before)),before.submap_of(after),
    ensures published(bank,slots,services,crate::lifecycle_state::services::capture::sources(after)),
{
    assert forall|i:int|0<=i<services.len() implies {
        let s=#[trigger] services[i];
        &&& s.mapped(bank,slots) && crate::lifecycle_state::services::capture::sources(after).contains_key(s.id)
        &&& crate::lifecycle_state::services::capture::sources(after)[s.id].values.contains_pair((s.port.key,s.port.realm),s.service)
    } by {
        let s=services[i];assert(before.dom().contains(s.id));
        assert(after.dom().contains(s.id) && before[s.id]==after[s.id]) by {reveal(Map::submap_of);}
    }
}
pub proof fn extend<T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,prior:&Slots<T>,services:Seq<Service<T>>,sources:Map<usize,crate::lifecycle_state::services::capture::Source<Slot<T,()>>>)
    requires slots.len_spec()>=prior.len_spec(),
        forall|i:int|0<=i<prior.len_spec() ==> slots.service(i)==prior.service(i) && slots.initial(i)==prior.initial(i),
        published(bank,prior,services,sources),
    ensures published(bank,slots,services,sources),
{
    assert forall|i:int|0<=i<services.len() implies {
        let s=#[trigger] services[i];
        &&& s.mapped(bank,slots) && sources.contains_key(s.id) && sources[s.id].values.contains_pair((s.port.key,s.port.realm),s.service)
    } by {let s=services[i];if s.slot.is_some() {let n=s.slot.unwrap() as int;assert(slots.service(n)==prior.service(n));assert(slots.initial(n)==prior.initial(n));}}
}
pub fn remove<T:?Sized>(services:&mut Vec<Service<T>>,id:usize)
    ensures forall|i:int|0<=i<final(services).len() ==> (#[trigger] final(services)@[i]).id!=id && old(services)@.contains(final(services)@[i]),
{
    let mut i=0;
    while i<services.len()
        invariant i<=services.len(),forall|j:int|0<=j<services.len() ==> old(services)@.contains(#[trigger] services@[j]),
            forall|j:int|0<=j<i ==> (#[trigger] services@[j]).id!=id,
        decreases services.len()-i,
    {if services[i].id==id {services.remove(i);}else {i+=1;}}
}
pub proof fn subset<T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,before:Seq<Service<T>>,after:Seq<Service<T>>,sources:Map<usize,crate::lifecycle_state::services::capture::Source<Slot<T,()>>>)
    requires published(bank,slots,before,sources),forall|i:int|0<=i<after.len() ==> before.contains(#[trigger] after[i]),
    ensures published(bank,slots,after,sources),
{
    assert forall|i:int|0<=i<after.len() implies {
        let s=#[trigger] after[i];
        &&& s.mapped(bank,slots) && sources.contains_key(s.id) && sources[s.id].values.contains_pair((s.port.key,s.port.realm),s.service)
    } by {let j=choose|j:int|0<=j<before.len() && before[j]==after[i];assert(before[j].mapped(bank,slots));}
}
pub proof fn remove_publication<T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,services:Seq<Service<T>>,before:Map<usize,NativePublication<Slot<T,()>>>,after:Map<usize,NativePublication<Slot<T,()>>>,id:usize)
    requires published(bank,slots,services,crate::lifecycle_state::services::capture::sources(before)),after==before || after==before.remove(id),
        forall|i:int|0<=i<services.len() ==> (#[trigger] services[i]).id!=id,
    ensures published(bank,slots,services,crate::lifecycle_state::services::capture::sources(after)),
{
    assert forall|i:int|0<=i<services.len() implies {
        let s=#[trigger] services[i];
        &&& s.mapped(bank,slots) && crate::lifecycle_state::services::capture::sources(after).contains_key(s.id)
        &&& crate::lifecycle_state::services::capture::sources(after)[s.id].values.contains_pair((s.port.key,s.port.realm),s.service)
    } by {let s=services[i];assert(s.id!=id);assert(before[s.id]==after[s.id]);}
}
}

verus! {
/// A retained own-service value before the source body. Unvisited values may
/// live only in the complete closed object table, outside the operand Bank.
pub struct Preload<T:?Sized> {pub port:Port,pub service:Arc<Slot<T,()>>,pub route:Option<Service<T>>}
impl<T:?Sized> Preload<T> {
    pub open spec fn wf(&self,bank:&Bank<T>,slots:&Slots<T>)->bool {
        self.route.is_some() ==> self.route.unwrap().mapped(bank,slots) && self.route.unwrap().port==self.port && self.route.unwrap().service==self.service
    }
    pub fn origin(&self)->(out:Option<crate::action_ledger::ActionTicket>) ensures self.route.is_some() ==> out==self.route.unwrap().source_origin,
    {match &self.route {Some(s)=>s.source_origin,None=>None}}
    pub fn relabel(&self,port:Port,origin:Option<crate::action_ledger::ActionTicket>)->(out:Self)
        ensures out.port==port,out.service==self.service,forall|bank:&Bank<T>,slots:&Slots<T>|self.wf(bank,slots) ==> out.wf(bank,slots),
    {
        let route=match &self.route {Some(s)=>Some(Service {id:s.id,port,index:s.index,slot:s.slot,source_origin:origin,service:s.service.clone()}),None=>None};
        Self {port,service:self.service.clone(),route}
    }
    // Explicit branches preserve the erased receipt and owner relations.
    #[allow(clippy::manual_map)]
    pub fn duplicate(&self)->(out:Self) ensures out==*self,
    {Self {port:self.port,service:self.service.clone(),route:match &self.route {Some(s)=>Some(s.duplicate()),None=>None}}}
}
pub open spec fn preloaded<T:?Sized>(entries:Seq<Preload<T>>,episode:NativeEpisode<Slot<T,()>>)->bool {
    forall|i:int|0<=i<entries.len() ==> episode.owned().contains_pair(((#[trigger] entries[i]).port.key,entries[i].port.realm),entries[i].service)
}
pub fn routes<T:?Sized>(entries:&[Preload<T>],id:usize)->(out:Vec<Service<T>>)
    ensures forall|i:int|0<=i<out.len() ==> (#[trigger] out@[i]).id==id && exists|j:int|0<=j<entries.len()
        && entries@[j].route.is_some() && out@[i].port==entries@[j].port && out@[i].service==entries@[j].service
        && out@[i].index==entries@[j].route.unwrap().index && out@[i].slot==entries@[j].route.unwrap().slot && out@[i].source_origin==entries@[j].route.unwrap().source_origin,
{
    let mut out:Vec<Service<T>>=Vec::new();let mut i=0;
    while i<entries.len()
        invariant i<=entries.len(),forall|k:int|0<=k<out.len() ==> (#[trigger] out@[k]).id==id && exists|j:int|0<=j<i
            && entries@[j].route.is_some() && out@[k].port==entries@[j].port && out@[k].service==entries@[j].service
            && out@[k].index==entries@[j].route.unwrap().index && out@[k].slot==entries@[j].route.unwrap().slot && out@[k].source_origin==entries@[j].route.unwrap().source_origin,
        decreases entries.len()-i,
    {
        if let Some(s)=&entries[i].route {out.push(Service {id,port:entries[i].port,index:s.index,slot:s.slot,source_origin:s.source_origin,service:entries[i].service.clone()});}
        i+=1;
    }out
}
pub proof fn routes_owned<T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,entries:Seq<Preload<T>>,routes:Seq<Service<T>>,episode:NativeEpisode<Slot<T,()>>)
    requires episode.wf(),preloaded(entries,episode),forall|i:int|0<=i<entries.len() ==> (#[trigger] entries[i]).wf(bank,slots),
        forall|i:int|0<=i<routes.len() ==> (#[trigger] routes[i]).id==episode.origin().id && exists|j:int|0<=j<entries.len()
            && entries[j].route.is_some() && routes[i].port==entries[j].port && routes[i].service==entries[j].service
            && routes[i].index==entries[j].route.unwrap().index && routes[i].slot==entries[j].route.unwrap().slot,
    ensures owned(bank,slots,routes,episode),
{
    assert forall|i:int|0<=i<routes.len() implies {
        let s=#[trigger] routes[i];
        &&& s.mapped(bank,slots) && s.id==episode.origin().id && episode.provisions().contains(s.port)
        &&& episode.owned().contains_pair((s.port.key,s.port.realm),s.service)
    } by {let j=choose|j:int|0<=j<entries.len() && entries[j].route.is_some() && routes[i].port==entries[j].port && routes[i].service==entries[j].service && routes[i].index==entries[j].route.unwrap().index && routes[i].slot==entries[j].route.unwrap().slot;assert(entries[j].wf(bank,slots));}
}
}

verus! {
/// The ordinary pre-root provide API changes only the owned cache. Keeping this
/// loop separate makes the setup/control/work frame available to its caller.
pub(crate) fn install<C,T:?Sized>(owner:&mut super::super::Owner<C,(),(),(),T,(),()>,entries:&[Preload<T>])->(out:Option<usize>)
    requires old(owner).wf(),old(owner).value_state().is_some(),
    ensures final(owner).wf(),final(owner).value_state().is_some(),
        final(owner).execution_journal()==old(owner).execution_journal(),final(owner).capture()==old(owner).capture(),
        final(owner).work_state()==old(owner).work_state(),final(owner).cleanup_state()==old(owner).cleanup_state(),
        final(owner).phase_spec()==old(owner).phase_spec(),final(owner).status_links()==old(owner).status_links(),
        final(owner).value_state().unwrap().same_identity(&old(owner).value_state().unwrap()),
        final(owner).value_state().unwrap().imports()==old(owner).value_state().unwrap().imports(),
        final(owner).value_state().unwrap().closed()==old(owner).value_state().unwrap().closed(),
        out.is_none() ==> preloaded(entries@,final(owner).value_state().unwrap()),
{
    let mut i=0;
    while i<entries.len()
        invariant owner.wf(),owner.value_state().is_some(),i<=entries.len(),
            owner.execution_journal()==old(owner).execution_journal(),owner.capture()==old(owner).capture(),
            owner.work_state()==old(owner).work_state(),owner.cleanup_state()==old(owner).cleanup_state(),
            owner.phase_spec()==old(owner).phase_spec(),owner.status_links()==old(owner).status_links(),
            owner.value_state().unwrap().same_identity(&old(owner).value_state().unwrap()),
            owner.value_state().unwrap().imports()==old(owner).value_state().unwrap().imports(),owner.value_state().unwrap().closed()==old(owner).value_state().unwrap().closed(),
            forall|j:int|0<=j<i ==> owner.value_state().unwrap().owned().contains_pair(((#[trigger] entries@[j]).port.key,entries@[j].port.realm),entries@[j].service),
        decreases entries.len()-i,
    {if owner.provide(entries[i].port,entries[i].service.clone()).is_err() {return Some(i);}i+=1;}None
}
}

verus! {
pub proof fn retain_preloaded<T:?Sized>(entries:Seq<Preload<T>>,before:NativeEpisode<Slot<T,()>>,after:NativeEpisode<Slot<T,()>>)
    requires preloaded(entries,before),before.owned().submap_of(after.owned()),
    ensures preloaded(entries,after),
{assert forall|i:int|0<=i<entries.len() implies after.owned().contains_pair(((#[trigger] entries[i]).port.key,entries[i].port.realm),entries[i].service) by {reveal(Map::submap_of);}}
pub proof fn combined_loaded<T:?Sized>(a:Seq<Preload<T>>,b:Seq<Preload<T>>,episode:NativeEpisode<Slot<T,()>>)
    requires preloaded(a,episode),preloaded(b,episode),ensures preloaded(a+b,episode),
{assert forall|i:int|0<=i<(a+b).len() implies episode.owned().contains_pair(((#[trigger] (a+b)[i]).port.key,(a+b)[i].port.realm),(a+b)[i].service) by {if i<a.len() {assert((a+b)[i]==a[i]);} else {assert((a+b)[i]==b[i-a.len()]);}}}
pub fn combine<T:?Sized>(a:&[Preload<T>],b:&[Preload<T>])->(out:Vec<Preload<T>>)
    ensures out@==a@+b@,
{
    let mut out=Vec::new();let mut i=0;
    while i<a.len() invariant i<=a.len(),out@==a@.take(i as int),decreases a.len()-i,
    {out.push(a[i].duplicate());i+=1;}
    let mut i=0;
    while i<b.len() invariant i<=b.len(),out@==a@+b@.take(i as int),decreases b.len()-i,
    {out.push(b[i].duplicate());i+=1;}out
}
/// Install only the remaining post-root entries. A failed provide retains the
/// exact successful prefix and its original cleanup owner for a later retry.
pub(crate) fn install_recorded<C,T:?Sized>(owner:&mut super::super::interleaving::history::lifecycle::RecordedExecution<C,(),(),(),T,(),()>,entries:&[Preload<T>],start:usize)->(out:usize)
    requires old(owner).wf(),old(owner).core().value_state().is_some(),start<=entries.len(),preloaded(entries@.take(start as int),old(owner).core().value_state().unwrap()),
    ensures final(owner).wf(),final(owner).same_history(old(owner)),final(owner).core().value_state().is_some(),start<=out<=entries.len(),
        preloaded(entries@.take(out as int),final(owner).core().value_state().unwrap()),
        old(owner).core().value_state().unwrap().owned().submap_of(final(owner).core().value_state().unwrap().owned()),
{
    let mut i=start;
    while i<entries.len()
        invariant owner.wf(),owner.same_history(old(owner)),owner.core().value_state().is_some(),start<=i<=entries.len(),
            preloaded(entries@.take(i as int),owner.core().value_state().unwrap()),
            old(owner).core().value_state().unwrap().owned().submap_of(owner.core().value_state().unwrap().owned()),
        decreases entries.len()-i,
    {
        let ghost before=owner.core().value_state().unwrap();
        let result=owner.provide(entries[i].port,entries[i].service.clone());
        proof {
            retain_preloaded(entries@.take(i as int),before,owner.core().value_state().unwrap());
            assert(old(owner).core().value_state().unwrap().owned().submap_of(owner.core().value_state().unwrap().owned())) by {
                reveal(Map::submap_of);
                assert forall|k:(u64,u64)|old(owner).core().value_state().unwrap().owned().dom().contains(k) implies owner.core().value_state().unwrap().owned().contains_pair(k,old(owner).core().value_state().unwrap().owned()[k]) by {
                    assert(before.owned().contains_pair(k,old(owner).core().value_state().unwrap().owned()[k]));
                    assert(owner.core().value_state().unwrap().owned().contains_pair(k,before.owned()[k]));
                }
            }
        }
        if result.is_err() {return i;}
        proof {assert forall|j:int|0<=j<i+1 implies owner.core().value_state().unwrap().owned().contains_pair(((#[trigger] entries@.take(i+1)[j]).port.key,entries@.take(i+1)[j].port.realm),entries@.take(i+1)[j].service) by {if j<i {assert(entries@.take(i as int)[j]==entries@[j]);}}}
        i+=1;
    }i
}
}
