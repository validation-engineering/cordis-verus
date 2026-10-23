//! Persistent evidence that observations of one shared value extend the same
//! history. All resources in this module are erased; no runtime log is retained.
use vstd::prelude::*;
use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo, GhostPersistentSubmap};
#[cfg(verus_keep_ghost)]
use vstd::resource::Loc;

verus! {
pub open spec fn prefixes_match<T>(prefixes:Map<nat,Seq<T>>,events:Seq<T>)->bool {
    forall|n:nat| n<=events.len() ==> prefixes.contains_key(n) && #[trigger] prefixes[n]==events.take(n as int)
}

proof fn prefix_table_take<T>(prefixes:Map<nat,Seq<T>>,events:Seq<T>,n:nat)
    requires prefixes_match(prefixes,events),n<=events.len(),
    ensures prefixes_match(prefixes,events.take(n as int)),
{
    reveal(prefixes_match);
    let cut=events.take(n as int);
    assert(prefixes_match(prefixes,cut)) by {
        assert forall|k:nat| k<=cut.len() implies #[trigger] prefixes.contains_key(k) by {
            assert(prefixes[k]==events.take(k as int));
        }
        assert forall|k:nat| k<=cut.len() implies {
            &&& prefixes.contains_key(k)
            &&& #[trigger] prefixes[k]==cut.take(k as int)
        } by {
            assert(k<=events.len());assert(prefixes[k]==events.take(k as int));
            assert(cut.take(k as int) =~= events.take(k as int));
        }
    }

}

#[allow(dead_code)] // The authoritative resource exists only in erased proof state.
pub tracked struct Authority<T> {
    auth:GhostMapAuth<nat,Seq<T>>,
    latest:GhostPersistentPointsTo<nat,Seq<T>>,
    prefixes:GhostPersistentSubmap<nat,Seq<T>>,
}
#[allow(dead_code)] // The persistent token exists only in erased proof state.
pub tracked struct Witness<T> {point:GhostPersistentPointsTo<nat,Seq<T>>,prefixes:GhostPersistentSubmap<nat,Seq<T>>}
impl<T> Witness<T> {
    pub proof fn duplicate(tracked &self)->(tracked out:Self)
        ensures out.wf()==self.wf(),out.source()==self.source(),out.events()==self.events(),
    {Self {point:self.point.duplicate(),prefixes:self.prefixes.duplicate()}}

    pub closed spec fn source(&self)->Loc {self.point.id()}
    pub closed spec fn events(&self)->Seq<T> {self.point.value()}
    pub closed spec fn wf(&self)->bool {
        self.point.key()==self.events().len() && self.prefixes.id()==self.source()
            && prefixes_match(self.prefixes@,self.events())
    }
    /// Extract an authentic prefix from retained persistent resources.
    pub proof fn take(tracked &self,n:nat)->(tracked out:Self)
        requires self.wf(),n<=self.events().len(),
        ensures out.wf(),out.source()==self.source(),out.events()==self.events().take(n as int),
    {
        reveal(prefixes_match);
        assert(self.prefixes@[n]==self.events().take(n as int));
        let tracked mut copy=self.prefixes.duplicate();
        let tracked point=copy.split_points_to(n);
        let tracked prefixes=self.prefixes.duplicate();
        assert(point.key()==n);assert(point.value()==self.events().take(n as int));
        assert(point.value().len()==n);assert(point.id()==prefixes.id());
        prefix_table_take(self.prefixes@,self.events(),n);
        assert(prefixes@==self.prefixes@);
        Self {point,prefixes}
    }
    /// Two real observations agree on their shared prefix without acquiring
    /// the live owner again. All retained prefix resources erase at runtime.
    pub proof fn prefix(tracked &self,tracked earlier:&Self)
        requires self.wf(),earlier.wf(),self.source()==earlier.source(),earlier.events().len()<=self.events().len(),
        ensures self.events().take(earlier.events().len() as int)==earlier.events(),
    {
        let tracked mut point=earlier.point.duplicate();
        point.intersection_agrees_submap(&self.prefixes);
        assert(self.prefixes@[earlier.events().len()]==self.events().take(earlier.events().len() as int));
        assert(point.key()==earlier.events().len());
    }
}
impl<T> Authority<T> {
    pub closed spec fn source(&self)->Loc {self.auth.id()}
    pub closed spec fn events(&self)->Seq<T> {self.latest.value()}
    pub closed spec fn wf(&self)->bool {
        &&& self.latest.id()==self.source()
        &&& self.latest.key()==self.events().len()
        &&& self.prefixes.id()==self.source() && self.prefixes@==self.auth@
        &&& forall|n:nat| #[trigger] self.auth@.contains_key(n) <==> n<=self.events().len()
        &&& forall|n:nat| #[trigger] self.auth@.contains_key(n) ==> self.auth@[n]==self.events().take(n as int)
    }
    pub proof fn new()->(tracked out:Self)
        ensures out.wf(),out.events()==Seq::<T>::empty(),
    {
        let tracked (mut auth,_empty)=GhostMapAuth::new(Map::empty());
        let tracked latest=auth.insert(0nat,Seq::empty()).persist();
        assert(Seq::<T>::empty().take(0) =~= Seq::<T>::empty());
        let tracked prefixes=latest.duplicate().submap();
        assert(prefixes@ =~= auth@);
        Authority {auth,latest,prefixes}
    }
    pub proof fn snapshot(tracked &self)->(tracked out:Witness<T>)
        requires self.wf(),
        ensures out.wf(),out.source()==self.source(),out.events()==self.events(),
    {Witness {point:self.latest.duplicate(),prefixes:self.prefixes.duplicate()}}
    pub proof fn append(tracked &mut self,event:T)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).source()==old(self).source(),
            final(self).events()==old(self).events().push(event),
    {
        let prior=self.events();
        let next=prior.push(event);
        self.latest=self.auth.insert(next.len(),next).persist();
        self.prefixes.combine_points_to(self.latest.duplicate());
        assert forall|n:nat| #[trigger] self.auth@.contains_key(n) implies self.auth@[n]==next.take(n as int) by {
            if n<=prior.len() {assert(next.take(n as int) =~= prior.take(n as int));}
            else {assert(next.take(n as int) =~= next);}
        }
    }
    /// A real earlier observation cannot be ahead of, or disagree with, the
    /// authoritative history encountered after acquiring this value's lock.
    pub proof fn extends(tracked &self,tracked earlier:&Witness<T>)
        requires self.wf(),earlier.wf(),earlier.source()==self.source(),
        ensures earlier.events().len()<=self.events().len(),
            self.events().take(earlier.events().len() as int)==earlier.events(),
    {earlier.point.agree(&self.auth);}
}
pub open spec fn agree<K,T>(witnesses:Map<K,Witness<T>>,a:K,b:K)->bool {
    witnesses.contains_key(a) && witnesses.contains_key(b) && witnesses[a].wf() && witnesses[b].wf()
        && witnesses[a].source()==witnesses[b].source() && witnesses[a].events().len()<=witnesses[b].events().len()
        ==> witnesses[b].events().take(witnesses[a].events().len() as int)==witnesses[a].events()
}
pub open spec fn compatible<K,T>(witnesses:Map<K,Witness<T>>)->bool {
    forall|a:K,b:K| #[trigger] agree(witnesses,a,b)
}
proof fn compare_one<K,T>(tracked witnesses:&Map<K,Witness<T>>,a:K,keys:Set<K>)
    requires keys.subset_of(witnesses.dom()),witnesses.contains_key(a),
    ensures forall|b:K| keys.contains(b) ==> #[trigger] agree(*witnesses,a,b),
    decreases keys.len(),
{
    if keys.len()>0 {
        let b=keys.choose();let rest=keys.remove(b);
        compare_one(witnesses,a,rest);
        let tracked left=witnesses.tracked_borrow(a);let tracked right=witnesses.tracked_borrow(b);
        if left.wf() && right.wf() && left.source()==right.source() && left.events().len()<=right.events().len() {right.prefix(left);}
        assert forall|k:K| keys.contains(k) implies #[trigger] agree(*witnesses,a,k) by {
            if k!=b {assert(rest.contains(k));}
        }
    }
}
proof fn compare_keys<K,T>(tracked witnesses:&Map<K,Witness<T>>,keys:Set<K>)
    requires keys.subset_of(witnesses.dom()),
    ensures forall|a:K,b:K| keys.contains(a) ==> #[trigger] agree(*witnesses,a,b),
    decreases keys.len(),
{
    if keys.len()>0 {
        let a=keys.choose();let rest=keys.remove(a);
        compare_keys(witnesses,rest);compare_one(witnesses,a,witnesses.dom());
        assert forall|k:K,b:K|keys.contains(k) implies #[trigger] agree(*witnesses,k,b) by {
            if k!=a {assert(rest.contains(k));}
        }
    }
}
/// Export persistent resource agreement for every pair in one real evidence
/// map. Quantified clients consume these facts without inventing witnesses.
pub proof fn compatible_map<K,T>(tracked witnesses:&Map<K,Witness<T>>)
    ensures compatible(*witnesses),
{compare_keys(witnesses,witnesses.dom());}
}

#[path = "shared_value_sources.rs"]
pub mod sources;
