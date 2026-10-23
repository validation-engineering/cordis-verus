//! Deterministic recovery projection of actual producers at one common cut.
//! Allocation/Journal identity de-duplicates aliases. Initial obligations and
//! successful-consumption uniqueness are derived, never supplied as premises.
#[cfg(verus_keep_ghost)]
use super::super::contains;
use super::super::{obligations::Inverse, Event};
#[cfg(verus_keep_ghost)]
use super::produced::Produced;
use super::producer::Producer;
#[cfg(verus_keep_ghost)]
use super::{coverage, link, origins};
use crate::reversible_value::{joint, service_composition::Address};
use vstd::prelude::*;

verus! {
pub open spec fn captured<T:?Sized>(producers:Map<Address,Producer<T>>,end:joint::Receipt)->bool {
    end.wf() && forall|key:Address|#[trigger] producers.contains_key(key) ==> {
        let p=producers[key];
        &&& p.wf() && p.address()==key && key.journal==end.journal()
        &&& end.events().len()<=p.frames().len() && p.frames().take(end.events().len() as int)==end.events()
    }
}
pub open spec fn index<T:?Sized>(p:Producer<T>,at:nat)->int {choose|i:int|0<=i<p.positions().len() && p.positions()[i]==at}
pub proof fn located<T:?Sized>(p:Producer<T>,at:nat)
    requires p.wf(),at<p.frames().len(),p.frames()[at as int].event.key==p.address().key,
    ensures 0<=index(p,at)<p.positions().len(),p.positions()[index(p,at)]==at,
{
    let i=p.complete_at(at);assert(p.positions()[i]==at);
}
pub open spec fn selected<T:?Sized>(producers:Map<Address,Producer<T>>,end:joint::Receipt,at:nat)->bool {
    let key=Address {journal:end.journal(),key:end.events()[at as int].event.key};
    producers.contains_key(key) && {let p=producers[key];let i=index(p,at);p.creates(i) || p.consumes(i)}
}
/// One event per actual reversible mutation, globally ordered by commit.
/// No-op rejected attempts may stutter; non-invertible changes are diagnosed.
pub open spec fn projection<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,producers:Map<Address,Producer<T>>,start:joint::Receipt,end:joint::Receipt,until:nat)->bool {
    &&& forall|i:int|0<=i<events.len() ==> {
        let e=#[trigger] events[i];let at=e.checkpoint().at();let key=e.inverse().address;
        &&& e is Produced && e.source() && producers.contains_key(key)
        &&& e->Produced_0.producer==producers[key] && e->Produced_0.index==index(producers[key],at)
        &&& start.events().len()<=at<until && end.covers(&e.checkpoint())
        &&& forall|j:int|0<=j<i ==> (#[trigger] events[j]).checkpoint().at()<at
    }
    &&& forall|at:nat|start.events().len()<=at<until && #[trigger] selected(producers,end,at) ==>
        exists|i:int|0<=i<events.len() && (#[trigger] events[i]).checkpoint().at()==at
}
proof fn collect<A,R,T:?Sized,M,X>(producers:Map<Address,Producer<T>>,start:joint::Receipt,tracked end:&joint::Receipt,until:nat)->(events:Seq<Event<A,R,T,M,X>>)
    requires captured(producers,*end),start.wf(),end.covers(&start),start.events().len()<=until<=end.events().len(),
    ensures projection(events,producers,start,*end,until),
    decreases until-start.events().len(),
{
    hide(joint::valid);hide(joint::step);
    if until==start.events().len() {Seq::empty()} else {
        let at=(until-1) as nat;let prior=collect(producers,start,end,at);
        if selected(producers,*end,at) {
            let key=Address {journal:end.journal(),key:end.events()[at as int].event.key};let p=producers[key];
            assert(p.frames()[at as int]==end.events()[at as int]);located(p,at);
            let produced=Produced::new(p,index(p,at),end);let event=Event::Produced(produced);let events=prior.push(event);
            assert forall|i:int|0<=i<events.len() implies {
                let e=#[trigger] events[i];let pos=e.checkpoint().at();let k=e.inverse().address;
                &&& e is Produced && e.source() && producers.contains_key(k)
                &&& e->Produced_0.producer==producers[k] && e->Produced_0.index==index(producers[k],pos)
                &&& start.events().len()<=pos<until && end.covers(&e.checkpoint())
                &&& forall|j:int|0<=j<i ==> (#[trigger] events[j]).checkpoint().at()<pos
            } by {if i<prior.len() {assert(prior[i]==events[i]);} else {assert(events[i]==event);}}
            assert forall|pos:nat|start.events().len()<=pos<until && #[trigger] selected(producers,*end,pos) implies
                exists|i:int|0<=i<events.len() && (#[trigger] events[i]).checkpoint().at()==pos by {
                if pos==at {assert(events[prior.len() as int].checkpoint().at()==pos);}
                else {let i=choose|i:int|0<=i<prior.len() && (#[trigger] prior[i]).checkpoint().at()==pos;assert(events[i]==prior[i]);}
            }
            events
        } else {prior}
    }
}
/// Actual creating writes not consumed before the cut. These descriptors do
/// not claim custody of a callback/inverse or that a destructive replacement
/// left the entire word executable. The interval admission checks that boundary.
pub open spec fn initial<T:?Sized>(producers:Map<Address,Producer<T>>,start:joint::Receipt)->Seq<Option<Inverse<T>>> {
    Seq::new(start.events().len(),|at:int|{
        let key=Address {journal:start.journal(),key:start.events()[at].event.key};
        if producers.contains_key(key) {
            let p=producers[key];let i=index(p,at as nat);
            if p.creates(i) && !(exists|j:int|0<=j<p.positions().len() && p.positions()[j]<start.events().len()
                && p.consumes(j) && p.inverse(j)==p.inverse(i)) {Some(p.inverse(i))} else {None}
        } else {None}
    })
}
pub ghost struct Interval<A,R,T:?Sized,M,X> {
    pub start:joint::Receipt,pub end:joint::Receipt,pub producers:Map<Address,Producer<T>>,pub events:Seq<Event<A,R,T,M,X>>,
}
pub ghost struct Census<A,R,T:?Sized,M,X> {pub interval:Interval<A,R,T,M,X>,pub issue:Option<Issue<T>>}
pub ghost enum Issue<T:?Sized> {
    /// A concrete changed frame which has no reversible producer projection.
    Change {address:Address,at:nat},
    /// A real restore crosses the invocation's retained inverse boundary.
    Earlier {inverse:Inverse<T>,at:nat},
}
impl<A,R,T:?Sized,M,X> Interval<A,R,T,M,X> {
    pub open spec fn wf(&self)->bool {self.start.wf() && self.end.covers(&self.start) && captured(self.producers,self.end)
        && projection(self.events,self.producers,self.start,self.end,self.end.events().len())}
    pub open spec fn initial(&self)->Seq<Option<Inverse<T>>> {initial(self.producers,self.start)}
    /// Source boundary of this invocation, checked from actual commits. No
    /// destructive frame or successful restore from an unrelated earlier word.
    pub open spec fn clear(&self,slots:Seq<Option<Inverse<T>>>)->bool {
        (forall|key:Address,at:int|self.producers.contains_key(key) && self.start.events().len()<=at<self.end.events().len()
            && #[trigger] coverage::changes_at(self.end.events(),at,key.key) ==> selected(self.producers,self.end,at as nat))
        && (forall|i:int|0<=i<self.events.len() && !(#[trigger] self.events[i]).forward() && self.events[i].inverse().origin<self.start.events().len() ==>
            contains(slots,self.events[i].inverse()))
    }
    pub open spec fn diagnosed(&self,issue:Issue<T>,slots:Seq<Option<Inverse<T>>>)->bool {
        match issue {
            Issue::Change {address,at}=>self.producers.contains_key(address) && self.start.events().len()<=at<self.end.events().len()
                && coverage::changes_at(self.end.events(),at as int,address.key) && !selected(self.producers,self.end,at),
            Issue::Earlier {inverse,at}=>inverse.origin<self.start.events().len() && contains(self.initial(),inverse) && !contains(slots,inverse)
                && exists|i:int|0<=i<self.events.len() && (#[trigger] self.events[i]).checkpoint().at()==at
                    && !self.events[i].forward() && self.events[i].inverse()==inverse,
        }
    }
    pub proof fn new(producers:Map<Address,Producer<T>>,start:joint::Receipt,tracked end:&joint::Receipt)->(out:Self)
        requires captured(producers,*end),start.wf(),end.covers(&start),
        ensures out.wf(),out.producers==producers,out.start==start,out.end==*end,
            link::ordered(out.events,start),origins::admitted(out.events,out.initial(),producers.dom()),
    {
        let events=collect(producers,start,end,end.events().len());
        let out=Self {start,end:*end,producers,events};out.ordered();out.origins();out
    }
    pub proof fn ordered(&self)
        requires self.wf(),ensures link::ordered(self.events,self.start),
    {
        hide(joint::valid);hide(joint::step);
        assert forall|i:int|0<=i<self.events.len() implies {
            let e=#[trigger] self.events[i];
            &&& e.source() && e.checkpoint().covers(&self.start) && self.start.events().len()<=e.read_cut()
            &&& forall|j:int|0<=j<i ==> e.checkpoint().covers(&self.events[j].checkpoint()) && self.events[j].checkpoint().events().len()<=e.read_cut()
        } by {
            let e=self.events[i];assert(e.checkpoint().events().take(self.start.events().len() as int) =~= self.start.events());
            assert forall|j:int|0<=j<i implies e.checkpoint().covers(&self.events[j].checkpoint()) && self.events[j].checkpoint().events().len()<=e.read_cut() by {
                assert(e.checkpoint().events().take(self.events[j].checkpoint().events().len() as int) =~= self.events[j].checkpoint().events());
            }
        }
    }
    #[verifier::spinoff_prover]
    pub proof fn origin(&self,i:int)->(created:int)
        requires self.wf(),0<=i<self.events.len(),!self.events[i].forward(),
        ensures {
            let e=self.events[i];let p=e->Produced_0.producer;
            &&& 0<=created<e->Produced_0.index && p.creates(created) && p.inverse(created)==e.inverse()
            &&& p.positions()[created]==e.inverse().origin
            &&& if e.inverse().origin<self.start.events().len() {self.initial()[e.inverse().origin as int]==Some(e.inverse())}
                else {exists|j:int|0<=j<i && (#[trigger] self.events[j]).forward() && self.events[j].inverse()==e.inverse()}
            &&& origins::unconsumed(self.events,e.inverse(),i as nat)
        },
    {
        hide(joint::valid);hide(joint::step);
        let e=self.events[i];let p=e->Produced_0.producer;let n=e->Produced_0.index;let key=e.inverse().address;
        let c=p.consumption_source(n);p.mutation(c);p.ordered();let pos=p.positions()[c];
        assert(p.inverse(c).origin==pos);
        if pos<self.start.events().len() {
            assert(self.start.events()[pos as int]==self.end.events()[pos as int]);assert(self.end.events()[pos as int]==p.frames()[pos as int]);
            located(p,pos);let other=index(p,pos);if c<other {assert(p.positions()[c]<p.positions()[other]);}if other<c {assert(p.positions()[other]<p.positions()[c]);}assert(other==c);
            assert(!(exists|j:int|0<=j<p.positions().len() && p.positions()[j]<self.start.events().len() && p.consumes(j) && p.inverse(j)==p.inverse(c))) by {
                assert forall|j:int|0<=j<p.positions().len() && p.positions()[j]<self.start.events().len() && p.consumes(j) implies p.inverse(j)!=p.inverse(c) by {if p.inverse(j)==p.inverse(c) {assert(j==n);}}
            }
        } else {
            located(p,pos);let other=index(p,pos);if c<other {assert(p.positions()[c]<p.positions()[other]);}if other<c {assert(p.positions()[other]<p.positions()[c]);}assert(other==c);
            assert(selected(self.producers,self.end,pos));
            let j=choose|j:int|0<=j<self.events.len() && (#[trigger] self.events[j]).checkpoint().at()==pos;
            let found=self.events[j];assert(found.inverse().address==key);assert(found->Produced_0.index==c);assert(j<i);
            assert(found.forward() && found.inverse()==e.inverse());
        }
        assert forall|j:int|0<=j<i && !(#[trigger] self.events[j]).forward() && self.events[j].succeeded() implies self.events[j].inverse()!=e.inverse() by {
            let other=self.events[j];
            if !other.forward() && other.inverse()==e.inverse() {
                assert(other->Produced_0.producer==p);let m=other->Produced_0.index;assert(p.consumes(m));assert(m==n);assert(false);
            }
        }
        c
    }
    pub proof fn origins(&self)
        requires self.wf(),ensures origins::admitted(self.events,self.initial(),self.producers.dom()),
    {
        assert forall|i:int|0<=i<self.events.len() && self.producers.dom().contains((#[trigger] self.events[i]).inverse().address) && !self.events[i].forward() && self.events[i].succeeded() implies
            origins::created(self.events,self.initial(),self.events[i].inverse(),i as nat) && origins::unconsumed(self.events,self.events[i].inverse(),i as nat) by {
            let created=self.origin(i);let e=self.events[i];if e.inverse().origin<self.start.events().len() {assert(self.initial()[e.inverse().origin as int]==Some(e.inverse()));}
        }
    }
    /// No census or inverse-membership precondition: return either a derived
    /// census or a concrete boundary which prevents this recovery claim.
    pub proof fn check(&self,slots:Seq<Option<Inverse<T>>>)->(issue:Option<Issue<T>>)
        requires self.wf(),
        ensures issue.is_none()==self.clear(slots),issue.is_some() ==> self.diagnosed(issue.unwrap(),slots),
            issue.is_none() ==> coverage::complete(self.events,self.start,self.end,self.producers.dom())
                && origins::admitted(self.events,slots,self.producers.dom()),
    {
        hide(joint::valid);hide(joint::step);
        if exists|key:Address,at:int|self.producers.contains_key(key) && self.start.events().len()<=at<self.end.events().len()
            && coverage::changes_at(self.end.events(),at,key.key) && !selected(self.producers,self.end,at as nat) {
            let (address,at)=choose|key:Address,at:int|self.producers.contains_key(key) && self.start.events().len()<=at<self.end.events().len()
                && coverage::changes_at(self.end.events(),at,key.key) && !selected(self.producers,self.end,at as nat);
            Some(Issue::Change {address,at:at as nat})
        } else {
            assert forall|key:Address,at:int|self.producers.dom().contains(key) && self.start.events().len()<=at<self.end.events().len()
                && #[trigger] coverage::changes_at(self.end.events(),at,key.key) implies
                exists|i:int|0<=i<self.events.len() && #[trigger] coverage::names(self.events[i],self.end.journal(),key.key,at) by {
                assert(selected(self.producers,self.end,at as nat));let i=choose|i:int|0<=i<self.events.len() && (#[trigger] self.events[i]).checkpoint().at()==at;
                assert(self.events[i].inverse().address==key);
                let e=self.events[i];assert(e is Produced);assert(e.read_cut()==at);assert(e.succeeded());
                assert(coverage::names(e,self.end.journal(),key.key,at));
            }
            assert(coverage::complete(self.events,self.start,self.end,self.producers.dom()));
            if exists|i:int|0<=i<self.events.len() && !(#[trigger] self.events[i]).forward() && self.events[i].inverse().origin<self.start.events().len() && !contains(slots,self.events[i].inverse()) {
                let i=choose|i:int|0<=i<self.events.len() && !(#[trigger] self.events[i]).forward() && self.events[i].inverse().origin<self.start.events().len() && !contains(slots,self.events[i].inverse());
                let c=self.origin(i);let e=self.events[i];assert(self.initial()[e.inverse().origin as int]==Some(e.inverse()));
                Some(Issue::Earlier {inverse:e.inverse(),at:e.checkpoint().at()})
            } else {
                assert forall|i:int|0<=i<self.events.len() && self.producers.dom().contains((#[trigger] self.events[i]).inverse().address) && !self.events[i].forward() && self.events[i].succeeded() implies
                    origins::created(self.events,slots,self.events[i].inverse(),i as nat) && origins::unconsumed(self.events,self.events[i].inverse(),i as nat) by {
                    let c=self.origin(i);let e=self.events[i];if e.inverse().origin<self.start.events().len() {assert(contains(slots,e.inverse()));}
                }
                None
            }
        }
    }
}
}
