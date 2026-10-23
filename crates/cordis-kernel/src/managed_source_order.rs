//! Chronology composes from real call/dispatch predecessors and checkpoints.
#[cfg(verus_keep_ghost)]
use super::super::Event;
#[cfg(verus_keep_ghost)]
use super::link;
use crate::reversible_value::managed::Report;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    joint, managed::interleaving::history::lifecycle::function::forwards,
};
use vstd::prelude::*;

verus! {
pub open spec fn bounded<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,end:joint::Receipt)->bool {
    end.wf() && forall|i:int|0<=i<events.len() ==> (#[trigger] events[i]).source() && end.covers(&events[i].checkpoint())
}
pub open spec fn local<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,journal:joint::Journal)->bool {
    forall|i:int|0<=i<events.len() ==> (#[trigger] events[i]).checkpoint().journal()==journal
}
pub proof fn append<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,suffix:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,middle:joint::Receipt,end:joint::Receipt)
    requires link::ordered(events,start),bounded(events,middle),middle.covers(&start),
        link::ordered(suffix,middle),bounded(suffix,end),end.covers(&middle),
    ensures link::ordered(events+suffix,start),bounded(events+suffix,end),end.covers(&start),
{
    hide(joint::valid);hide(joint::step);
    end.cover_through(&middle,&start);
    assert forall|i:int|0<=i<(events+suffix).len() implies {
        let event=#[trigger] (events+suffix)[i];
        &&& event.source() && event.checkpoint().covers(&start) && start.events().len()<=event.read_cut()
        &&& forall|j:int|0<=j<i ==> event.checkpoint().covers(&(events+suffix)[j].checkpoint())
            && (events+suffix)[j].checkpoint().events().len()<=event.read_cut()
    } by {
        if i>=events.len() {
            let k=i-events.len();assert((events+suffix)[i]==suffix[k]);let event=suffix[k];
            event.checkpoint().cover_through(&middle,&start);
            assert forall|j:int|0<=j<i implies event.checkpoint().covers(&(events+suffix)[j].checkpoint())
                && (events+suffix)[j].checkpoint().events().len()<=event.read_cut() by {
                if j<events.len() {event.checkpoint().cover_through(&middle,&events[j].checkpoint());}
                else {assert((events+suffix)[j]==suffix[j-events.len()]);}
            }
        }
    }
    assert forall|i:int|0<=i<(events+suffix).len() implies (#[trigger] (events+suffix)[i]).source()
        && end.covers(&(events+suffix)[i].checkpoint()) by {
        if i<events.len() {end.cover_through(&middle,&events[i].checkpoint());}
        else {assert((events+suffix)[i]==suffix[i-events.len()]);}
    }
}
pub proof fn through<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,earlier:joint::Receipt,start:joint::Receipt,end:joint::Receipt,later:joint::Receipt)
    requires link::ordered(events,start),bounded(events,end),earlier.wf(),start.covers(&earlier),later.wf(),later.covers(&end),
    ensures link::ordered(events,earlier),bounded(events,later),
{
    assert forall|i:int|0<=i<events.len() implies {
        let event=#[trigger] events[i];
        &&& event.source() && event.checkpoint().covers(&earlier) && earlier.events().len()<=event.read_cut()
        &&& forall|j:int|0<=j<i ==> event.checkpoint().covers(&events[j].checkpoint()) && events[j].checkpoint().events().len()<=event.read_cut()
    } by {events[i].checkpoint().cover_through(&start,&earlier);}
    assert forall|i:int|0<=i<events.len() implies (#[trigger] events[i]).source() && later.covers(&events[i].checkpoint()) by {
        later.cover_through(&end,&events[i].checkpoint());
    }
}
impl<T:?Sized> Report<T> {
    pub proof fn source_order<A,R,M,X>(&self,start:joint::Receipt,end:joint::Receipt)
        requires self.witnessed(),self.recovery_history(),self.ordered(),self.after(Some(start)),self.covered_by(end),
            start.wf(),end.covers(&start),local(forwards::<A,R,T,M,X>(self.steps@),start.journal()),
        ensures link::ordered(forwards::<A,R,T,M,X>(self.steps@),start),bounded(forwards::<A,R,T,M,X>(self.steps@),end),
    {
        hide(joint::valid);hide(joint::step);
        reveal(Report::recovery_history);reveal(Report::after);reveal(crate::reversible_value::managed::episode::writes_after);reveal(Report::covered_by);
        let events=forwards::<A,R,T,M,X>(self.steps@);
        assert forall|i:int|0<=i<events.len() implies {
            let event=#[trigger] events[i];
            &&& event.source() && event.checkpoint().covers(&start) && start.events().len()<=event.read_cut()
            &&& forall|j:int|0<=j<i ==> event.checkpoint().covers(&events[j].checkpoint()) && events[j].checkpoint().events().len()<=event.read_cut()
        } by {
            let event=events[i];let step=self.steps@[i];assert(event==Event::Forward(step.forward_inverse()));
            assert(events[i].checkpoint().journal()==start.journal());
            assert(step.write().journal()==start.journal());
            assert(step.write().follows(&start));
            assert forall|j:int|0<=j<i implies event.checkpoint().covers(&events[j].checkpoint()) && events[j].checkpoint().events().len()<=event.read_cut() by {
                assert(events[j]==Event::Forward(self.steps@[j].forward_inverse()));
                assert(events[j].checkpoint().journal()==start.journal());
                assert(step.write().follows(&self.steps@[j].write()));
            }
        }
        assert forall|i:int|0<=i<events.len() implies (#[trigger] events[i]).source() && end.covers(&events[i].checkpoint()) by {
            assert(events[i].checkpoint().same(&self.steps@[i].write()));
            assert(self.steps@[i].write().journal()==start.journal());
            assert(self.steps@[i].witnessed(self.receipts(),i));
            assert(self.receipts()[(i,false)].journal()==end.journal());
            assert(end.covers(&self.receipts()[(i,false)]));
        }
    }
}
impl<A,R,T:?Sized,M,X> crate::reversible_value::managed::cleanup_path::Turn<A,R,T,M,X> {
    pub proof fn source_order(&self,start:joint::Receipt,end:joint::Receipt)
        requires self.authentic(),self.managed(),self.follows_boundary(Some(start)),start.wf(),end.wf(),
            self.queue_link().is_some(),self.queue_link().unwrap().0==start.journal(),
            self.checkpoint().journal()==start.journal(),end.same(&self.acknowledgement().unwrap()),
        ensures link::ordered(seq![Event::Managed(*self)],start),bounded(seq![Event::Managed(*self)],end),
    {
        self.acknowledgement_records();
        match self {
            crate::cleanup_groups::payload::Dispatch::Payload(c)=>{
                reveal(crate::reversible_value::payload::restoration::attempt::protocol::Evidence::certified);
                c.evidence().attempt().boundaries();
                assert(c.evidence().same_domain());
            },
            crate::cleanup_groups::payload::Dispatch::Other(crate::cleanup_queue::completion::CleanupDispatch::Value {completion,..})=>{assert(completion.evidence().same_domain());},
            _=>{},
        }
    }
}

}
