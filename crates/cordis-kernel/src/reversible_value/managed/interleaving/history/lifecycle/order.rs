//! Source order exported by production calls, not restated by their clients.
use super::RecordedExecution;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    joint,
    managed::interleaving::{
        sources::{link, order},
        Event,
    },
};
use vstd::prelude::*;

verus! {
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    pub open spec fn source_order(&self,id:usize,start:joint::Receipt)->bool {
        self.histories().contains_key(id) && self.recovery_boundary().is_some()
            && link::ordered(self.histories()[id].events(),start)
            && order::bounded(self.histories()[id].events(),self.recovery_boundary().unwrap())
            && self.recovery_boundary().unwrap().covers(&start)
    }
    /// Independently owned Journals keep independent clocks. The continuation
    /// guarantee applies when the appended sources belong to the original one.
    #[verifier::opaque]
    pub open spec fn source_order_extends(&self,prior:&Self)->bool {
        forall|id:usize,start:joint::Receipt|#[trigger] prior.source_order(id,start)
            && (forall|i:int|prior.histories()[id].events().len()<=i<self.histories()[id].events().len() ==>
                (#[trigger] self.histories()[id].events()[i]).checkpoint().journal()==start.journal()) ==>
                    self.source_order(id,start)
    }
    pub(super) proof fn extend_source_order(&self,prior:&Self,suffix:Seq<Event<A,R,T,M,X>>)
        requires self.histories().dom()==prior.histories().dom(),
            forall|id:usize|#[trigger] prior.histories().contains_key(id) ==> self.histories()[id].events()==prior.histories()[id].events()+suffix,
            prior.recovery_boundary().is_some() ==> self.recovery_boundary().is_some()
                && self.recovery_boundary().unwrap().covers(&prior.recovery_boundary().unwrap()),
            prior.recovery_boundary().is_some() && order::local(suffix,prior.recovery_boundary().unwrap().journal()) ==>
                link::ordered(suffix,prior.recovery_boundary().unwrap()) && order::bounded(suffix,self.recovery_boundary().unwrap()),
        ensures self.source_order_extends(prior),
    {
        reveal(RecordedExecution::source_order_extends);
        assert forall|id:usize,start:joint::Receipt|#[trigger] prior.source_order(id,start)
            && (forall|i:int|prior.histories()[id].events().len()<=i<self.histories()[id].events().len() ==>
                (#[trigger] self.histories()[id].events()[i]).checkpoint().journal()==start.journal()) implies
                    self.source_order(id,start) by {
            let events=prior.histories()[id].events();
            assert(order::local(suffix,start.journal())) by {
                assert forall|i:int|0<=i<suffix.len() implies (#[trigger] suffix[i]).checkpoint().journal()==start.journal() by {
                    assert(self.histories()[id].events()[events.len()+i]==suffix[i]);
                }
            }
            order::append(events,suffix,start,prior.recovery_boundary().unwrap(),self.recovery_boundary().unwrap());
        }
    }
    pub(super) proof fn rebase_source_order(&self,prior:&Self,middle:&Self)
        requires self.source_order_extends(middle),prior.histories()==middle.histories(),prior.recovery_boundary()==middle.recovery_boundary(),
        ensures self.source_order_extends(prior),
    {
        reveal(RecordedExecution::source_order_extends);
        assert forall|id:usize,start:joint::Receipt|#[trigger] prior.source_order(id,start)
            && (forall|i:int|prior.histories()[id].events().len()<=i<self.histories()[id].events().len() ==>
                (#[trigger] self.histories()[id].events()[i]).checkpoint().journal()==start.journal()) implies
                    self.source_order(id,start) by {assert(middle.source_order(id,start));}
    }

}
}
