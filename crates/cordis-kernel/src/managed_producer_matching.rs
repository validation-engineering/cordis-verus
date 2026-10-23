//! Connect an actual cleanup attempt to the independently captured producer.
//! Mutation identities, typed source agreement and the original creating write
//! determine the inverse; equal visible values alone do not identify it.
use super::super::{Attempt, Event};
#[cfg(verus_keep_ghost)]
use super::interval;
#[cfg(verus_keep_ghost)]
use super::Sources;
use super::{interval::Interval, producer::Producer};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, managed::semantics::Value, payload};
use vstd::prelude::*;

verus! {
impl<A,R,T:?Sized,M,X> Event<A,R,T,M,X> {
    pub open spec fn attempt(&self)->Attempt<T> {
        match self {
            Self::Restore(a)=>*a,
            Self::Managed(crate::cleanup_groups::payload::Dispatch::Payload(c))=>Attempt::Payload(c.evidence().attempt()),
            Self::Managed(crate::cleanup_groups::payload::Dispatch::Other(crate::cleanup_queue::completion::CleanupDispatch::Value {completion,..}))=>
                Attempt::Scalar {inverse:completion.evidence().inverse(),receipt:completion.evidence().attempt()},
            _=>arbitrary(),
        }
    }
    pub proof fn actual_attempt(&self)
        requires self.source(),self is Managed || self is Restore,
        ensures self.attempt().source(),self.attempt().succeeded()==self.succeeded(),
            self.attempt().forward().inverse()==self.inverse(),self.attempt().checkpoint()==self.checkpoint(),
            self.attempt().carrier()==self.carrier(),self.attempt().read_cut()==self.read_cut(),
    {
        match self {
            Self::Managed(d)=>{
                reveal(crate::cleanup_groups::payload::Dispatch::recovery);
                if let crate::cleanup_groups::payload::Dispatch::Payload(c)=d {
                    reveal(payload::restoration::attempt::protocol::Evidence::certified);
                }
            },_=>{},
        }
    }
}
impl<T:?Sized> Attempt<T> {
    pub proof fn mutation_record(&self)
        requires self.source(),self.succeeded(),
        ensures self.checkpoint().wf(),self.read_cut()<=self.checkpoint().at(),self.checkpoint().event().key==self.forward().inverse().address.key,
            self.checkpoint().journal()==self.forward().inverse().address.journal,
            self.checkpoint().event().change is Value ==> self.checkpoint().event().change->Value_event is Restore
                && self.checkpoint().event().change->Value_event->Restore_origin==self.forward().inverse().origin,
            self.checkpoint().event().change==joint::Change::PayloadRestore || self.checkpoint().event().change is Value,
            {let r=self.checkpoint();let key=self.forward().inverse().address.key;let input=joint::state_at(r.events(),r.at());
                &&& input.contains_key(key) && self.carrier().describes(input[key])
                &&& self.carrier().decode(input[key])==Some(self.forward().inverse().after)},
    {
        hide(joint::valid);hide(joint::step);self.facts();let r=self.checkpoint();r.transition();
        crate::reversible_value::managed::recovery::frame_update(r.events(),r.at());
        match self {
            Self::Scalar {..}=>{reveal(joint::step);reveal(joint::changes);},
            Self::Payload(a)=>{
                a.facts();a.boundaries();a.classified();a.result()->Ok_0.source_history();
                reveal(joint::step);reveal(joint::changes);
            },
        }
    }
}
impl<T:?Sized> Producer<T> {
    #[verifier::spinoff_prover]
    pub proof fn matches_restore(&self,a:Attempt<T>,sources:Sources<payload::State<T>>)->(i:int)
        requires self.wf(),a.source(),a.succeeded(),self.address()==a.forward().inverse().address,
            a.checkpoint().events().len()<=self.frames().len(),self.frames().take(a.checkpoint().events().len() as int)==a.checkpoint().events(),
            sources.wf(),self.carrier().covered(sources),a.carrier().covered(sources),
        ensures 0<=i<self.positions().len(),self.positions()[i]==a.checkpoint().at(),self.consumes(i),self.inverse(i)==a.forward().inverse(),
    {
        hide(joint::valid);hide(joint::step);a.mutation_record();let r=a.checkpoint();let inv=a.forward().inverse();
        let i=self.complete_at(r.at());self.ordered();assert(self.frames()[r.at() as int]==r.events()[r.at() as int]);
        assert(self.consumes(i));self.mutation(i);
        let input=joint::state_at(r.events(),r.at());let key=self.address().key;
        assert(input==joint::state_at(self.frames(),r.at()));
        self.carrier().agreement(a.carrier(),input[key],sources);
        assert(self.inverse(i).after==inv.after);
        match (self,a) {
            (Self::Scalar(_),Attempt::Scalar {..})=>{},
            (Self::Payload(s),Attempt::Payload(attempt))=>{
                s.facts();attempt.facts();let original=attempt.inverse();original.source_history();original.provenance();
                let v=s.observation();let origin=original.after().commit;let head=original.after().state().head as int;
                attempt.boundaries();r.cover_through(&attempt.read().checkpoint(),&origin);
                assert(origin.events().len()<=self.frames().len());
                assert(self.frames()[origin.at() as int]==origin.events()[origin.at() as int]);
                let created=self.complete_at(origin.at());
                reveal(joint::payload::indexed);
                assert(0<=created<v.states.len());
                assert(self.frames()[self.positions()[created] as int].event.after==(joint::Record::Payload {source:v.owner.source(),revision:created as u64}));
                assert(created==head);
                let c=self.consumption_source(i);self.mutation(c);
                reveal(payload::semantic_history::valid);reveal(payload::semantic_history::entry);reveal(payload::semantic_history::change);
                assert(0<c<v.states.len());
                assert(payload::semantic_history::entry(v.states,v.positions,v.commit.events(),c));
                assert(self.frames()[self.positions()[c] as int]==v.commit.events()[v.positions[c] as int]);
                assert(v.states[c].head==c);
                assert(c==head);
                assert(self.inverse(i).origin==origin.at());
                // The retained attempt extends the actual creating predecessor.
                attempt.result()->Ok_0.source_history();
                let before=original.before().state();let states=attempt.states();
                assert(head>0);assert(states.take(original.after().states.len() as int) =~= original.after().states);
                assert(original.before().states.len()==head);
                assert(original.before().states[head-1]==before);
                assert(original.after().states[head-1]==before);
                assert(states[head-1]==original.after().states[head-1]);
                let record=joint::Record::Payload {source:v.owner.source(),revision:(head-1) as u64};
                self.carrier().agreement(Attempt::Payload(attempt).carrier(),record,sources);
                assert(self.inverse(i).before==inv.before);
            },_=>{assert(false);},
        }
        i
    }
}
impl<A,R,T:?Sized,M,X> Interval<A,R,T,M,X> {
    /// Include a successful actual managed/raw restore in the automatic census.
    /// The caller supplies its real receipt, never an expected projected event.
    pub proof fn includes_restore(&self,event:Event<A,R,T,M,X>,sources:Sources<payload::State<T>>)->(j:int)
        requires self.wf(),event.source(),event is Managed || event is Restore,event.succeeded(),
            self.producers.contains_key(event.inverse().address),self.end.covers(&event.checkpoint()),
            self.start.events().len()<=event.checkpoint().at(),
            sources.wf(),event.carrier().covered(sources),self.producers[event.inverse().address].carrier().covered(sources),
        ensures 0<=j<self.events.len(),!self.events[j].forward(),self.events[j].succeeded(),self.events[j].inverse()==event.inverse(),
            self.events[j].checkpoint().at()==event.checkpoint().at(),
    {
        hide(joint::valid);hide(joint::step);event.actual_attempt();event.attempt().mutation_record();let r=event.checkpoint();let key=event.inverse().address;let p=self.producers[key];
        assert(p.frames().take(r.events().len() as int) =~= r.events());
        let i=p.matches_restore(event.attempt(),sources);
        assert(p.frames()[r.at() as int]==r.events()[r.at() as int]);
        assert(self.end.events()[r.at() as int]==r.events()[r.at() as int]);
        interval::located(p,r.at());p.ordered();let index=interval::index(p,r.at());
        if i<index {assert(p.positions()[i]<p.positions()[index]);}
        if index<i {assert(p.positions()[index]<p.positions()[i]);}assert(index==i);
        assert(interval::selected(self.producers,self.end,r.at()));
        let j=choose|j:int|0<=j<self.events.len() && (#[trigger] self.events[j]).checkpoint().at()==r.at();
        assert(self.events[j].inverse().address==key);assert(self.events[j]->Produced_0.index==i);j
    }
}
}
