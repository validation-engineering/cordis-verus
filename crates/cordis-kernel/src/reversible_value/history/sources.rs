//! Persistent, erased agreement between observations from actual value owners.
//! Keeping the longest authenticated prefix never requires a runtime history.
use super::Witness;
use vstd::prelude::*;
use vstd::resource::Loc;

verus! {
#[allow(dead_code)]
pub tracked struct Sources<T> {witnesses:Map<Loc,Witness<T>>}
impl<T> Sources<T> {
    pub closed spec fn wf(&self)->bool {
        forall|source:Loc|#[trigger] self.witnesses.contains_key(source) ==>
            self.witnesses[source].wf() && self.witnesses[source].source()==source
    }
    pub closed spec fn covers(&self,source:Loc,events:Seq<T>)->bool {
        self.witnesses.contains_key(source) && events.len()<=self.witnesses[source].events().len()
            && self.witnesses[source].events().take(events.len() as int)==events
    }
    pub open spec fn extends(&self,prior:Self)->bool {
        forall|source:Loc,events:Seq<T>|#[trigger] prior.covers(source,events) ==> self.covers(source,events)
    }
    pub proof fn new()->(tracked out:Self)
        ensures out.wf(),
    {Self {witnesses:Map::tracked_empty()}}
    pub proof fn retain(tracked &mut self,tracked witness:Witness<T>)
        requires old(self).wf(),witness.wf(),
        ensures final(self).wf(),final(self).extends(*old(self)),final(self).covers(witness.source(),witness.events()),
    {
        let prior=*self;let source=witness.source();
        if self.witnesses.contains_key(source) {
            let tracked old=self.witnesses.tracked_remove(source);
            if old.events().len()<=witness.events().len() {
                witness.prefix(&old);self.witnesses.tracked_insert(source,witness);
            } else {
                old.prefix(&witness);self.witnesses.tracked_insert(source,old);
            }
        } else {self.witnesses.tracked_insert(source,witness);}
        assert(self.witnesses[source].events().take(witness.events().len() as int) =~= witness.events());
        assert forall|key:Loc,events:Seq<T>|#[trigger] prior.covers(key,events) implies self.covers(key,events) by {
            if key==source {assert(self.witnesses[source].events().take(events.len() as int) =~= events);}
        }
    }
    pub proof fn agreement(&self,source:Loc,left:Seq<T>,right:Seq<T>)
        requires self.wf(),self.covers(source,left),self.covers(source,right),left.len()<=right.len(),
        ensures right.take(left.len() as int)==left,
    {assert(right.take(left.len() as int) =~= left);}
    proof fn merge_keys(tracked &mut self,tracked other:&Self,keys:Set<Loc>)
        requires old(self).wf(),other.wf(),keys.subset_of(other.witnesses.dom()),
        ensures final(self).wf(),final(self).extends(*old(self)),
            forall|source:Loc,events:Seq<T>|keys.contains(source) && #[trigger] other.covers(source,events) ==> final(self).covers(source,events),
        decreases keys.len(),
    {
        if keys.len()>0 {
            let source=keys.choose();let rest=keys.remove(source);let prior=*self;
            self.merge_keys(other,rest);let middle=*self;
            self.retain(other.witnesses.tracked_borrow(source).duplicate());
            assert forall|key:Loc,events:Seq<T>|#[trigger] prior.covers(key,events) implies self.covers(key,events) by {assert(middle.covers(key,events));}
            assert forall|key:Loc,events:Seq<T>|keys.contains(key) && #[trigger] other.covers(key,events) implies self.covers(key,events) by {
                if key==source {assert(self.witnesses[source].events().take(events.len() as int) =~= events);}
                else {assert(rest.contains(key));assert(middle.covers(key,events));}
            }
        }
    }
    /// Observing another execution copies only persistent proof resources.
    pub proof fn merge(tracked &mut self,tracked other:&Self)
        requires old(self).wf(),other.wf(),
        ensures final(self).wf(),final(self).extends(*old(self)),final(self).extends(*other),
    {self.merge_keys(other,other.witnesses.dom());}
}
}
