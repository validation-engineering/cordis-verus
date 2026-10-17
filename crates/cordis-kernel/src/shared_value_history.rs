//! Persistent evidence that observations of one shared value extend the same
//! history. All resources in this module are erased; no runtime log is retained.
use vstd::prelude::*;
use vstd::resource::map::{GhostMapAuth, GhostPersistentPointsTo};
#[cfg(verus_keep_ghost)]
use vstd::resource::Loc;

verus! {
#[allow(dead_code)] // The authoritative resource exists only in erased proof state.
pub tracked struct Authority<T> {
    auth:GhostMapAuth<nat,Seq<T>>,
    latest:GhostPersistentPointsTo<nat,Seq<T>>,
}
#[allow(dead_code)] // The persistent token exists only in erased proof state.
pub tracked struct Witness<T> {point:GhostPersistentPointsTo<nat,Seq<T>>}
impl<T> Witness<T> {
    pub proof fn duplicate(tracked &self)->(tracked out:Self)
        ensures out.wf()==self.wf(),out.source()==self.source(),out.events()==self.events(),
    {Self {point:self.point.duplicate()}}

    pub closed spec fn source(&self)->Loc {self.point.id()}
    pub closed spec fn events(&self)->Seq<T> {self.point.value()}
    pub closed spec fn wf(&self)->bool {self.point.key()==self.events().len()}
}
impl<T> Authority<T> {
    pub closed spec fn source(&self)->Loc {self.auth.id()}
    pub closed spec fn events(&self)->Seq<T> {self.latest.value()}
    pub closed spec fn wf(&self)->bool {
        &&& self.latest.id()==self.source()
        &&& self.latest.key()==self.events().len()
        &&& forall|n:nat| #[trigger] self.auth@.contains_key(n) <==> n<=self.events().len()
        &&& forall|n:nat| #[trigger] self.auth@.contains_key(n) ==> self.auth@[n]==self.events().take(n as int)
    }
    pub proof fn new()->(tracked out:Self)
        ensures out.wf(),out.events()==Seq::<T>::empty(),
    {
        let tracked (mut auth,_empty)=GhostMapAuth::new(Map::empty());
        let tracked latest=auth.insert(0nat,Seq::empty()).persist();
        assert(Seq::<T>::empty().take(0) =~= Seq::<T>::empty());
        Authority {auth,latest}
    }
    pub proof fn snapshot(tracked &self)->(tracked out:Witness<T>)
        requires self.wf(),
        ensures out.wf(),out.source()==self.source(),out.events()==self.events(),
    {Witness {point:self.latest.duplicate()}}
    pub proof fn append(tracked &mut self,event:T)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).source()==old(self).source(),
            final(self).events()==old(self).events().push(event),
    {
        let prior=self.events();
        let next=prior.push(event);
        self.latest=self.auth.insert(next.len(),next).persist();
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
}
