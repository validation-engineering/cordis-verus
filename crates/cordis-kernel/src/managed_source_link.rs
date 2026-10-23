//! The observation part of recovery linkage follows from real Journal gaps
//! and authenticated typed sources, rather than a supplied expected heap.
use super::{Attempt, Event, Forward};
#[cfg(verus_keep_ghost)]
use super::{Carrier, Sources};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    joint,
    managed::{
        episode::endpoint as function_endpoint,
        interleaving::{self as trajectory, endpoint, obligations},
        recovery,
        semantics::Value,
        Step,
    },
    payload,
    service_composition::Address,
};
use vstd::prelude::*;

verus! {
impl<T:?Sized> Forward<T> {
    pub proof fn source_records(&self)
        requires self.source(),
        ensures {
            let r=self.write();let input=joint::state_at(r.events(),r.at());let output=joint::state_at(r.events(),r.events().len());let key=self.inverse().address.key;
            &&& input.contains_key(key) && output.contains_key(key)
            &&& self.carrier().describes(input[key]) && self.carrier().describes(output[key])
            &&& self.carrier().decode(input[key])==Some(self.inverse().before)
            &&& self.carrier().decode(output[key])==Some(self.inverse().after)
        },
    {
        hide(joint::valid);hide(joint::step);
        self.facts();let r=self.write();r.transition();recovery::frame_update(r.events(),r.at());
        match self {
            Self::Scalar(_)=>{reveal(joint::step);reveal(joint::changes);},
            Self::Payload(i)=>{i.provenance();i.source_history();reveal(joint::step);reveal(joint::changes);},
        }
    }
}
impl<T:?Sized> Attempt<T> {
    pub proof fn source_records(&self)
        requires self.source(),
        ensures {
            let r=self.checkpoint();let input=joint::state_at(r.events(),self.read_cut());let output=joint::state_at(r.events(),r.events().len());let key=self.forward().inverse().address.key;
            &&& input.contains_key(key) && output.contains_key(key)
            &&& self.carrier().describes(input[key]) && self.carrier().describes(output[key])
            &&& self.carrier().decode(input[key])==self.observed()
            &&& self.carrier().decode(output[key])==self.landed()
        },
    {
        hide(joint::valid);hide(joint::step);
        self.facts();let r=self.checkpoint();recovery::frame_update(r.events(),r.at());
        match self {
            Self::Scalar {..}=>{r.transition();reveal(joint::step);reveal(joint::changes);},
            Self::Payload(a)=>{
                a.facts();a.boundaries();
                assert(joint::state_at(r.events(),a.read().checkpoint().events().len())==a.read().state());
                if a.result().is_ok() {a.result()->Ok_0.source_history();}
            },
        }
    }
}
impl<A,R,T:?Sized,M,X> Event<A,R,T,M,X> {
    pub proof fn source_records(&self)
        requires self.source(),
        ensures {
            let r=self.checkpoint();let input=joint::state_at(r.events(),self.read_cut());let output=joint::state_at(r.events(),r.events().len());let key=self.inverse().address.key;
            &&& r.wf() && self.read_cut()<=r.events().len()
            &&& input.contains_key(key) && output.contains_key(key)
            &&& self.carrier().describes(input[key]) && self.carrier().describes(output[key])
            &&& self.carrier().decode(input[key])==self.observed()
            &&& self.carrier().decode(output[key])==self.landed()
        },
    {
        hide(joint::valid);hide(joint::step);
        self.facts();
        match self {
            Self::Forward(f)=>f.source_records(),Self::Restore(a)=>a.source_records(),Self::Produced(e)=>e.facts(),
            Self::Managed(d)=>{
                match d {
                    crate::cleanup_groups::payload::Dispatch::Payload(c)=>{
                        reveal(payload::restoration::attempt::protocol::Evidence::certified);
                        let a=Attempt::Payload(c.evidence().attempt());a.source_records();
                    },
                    crate::cleanup_groups::payload::Dispatch::Other(crate::cleanup_queue::completion::CleanupDispatch::Value {completion,..})=>{
                        let a=Attempt::<T>::Scalar {inverse:completion.evidence().inverse(),receipt:completion.evidence().attempt()};a.source_records();
                    },_=>{},
                }
            },
        }
    }
}
/// Inspect actual chronological receipt prefixes, including each real read cut.
pub open spec fn ordered<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt)->bool {
    start.wf() && forall|i:int|0<=i<events.len() ==> {
        let event=#[trigger] events[i];
        &&& event.source() && event.checkpoint().covers(&start) && start.events().len()<=event.read_cut()
        &&& forall|j:int|0<=j<i ==> event.checkpoint().covers(&events[j].checkpoint()) && events[j].checkpoint().events().len()<=event.read_cut()
    }
}
pub open spec fn covered<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,sources:Sources<payload::State<T>>)->bool {
    sources.wf() && (forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).carrier().covered(sources))
        && forall|i:int|0<=i<events.len() ==> (#[trigger] events[i]).carrier().covered(sources)
}
/// No unobserved change to the allocation between its last included event and
/// this read. Other allocations and no-op failed attempts may still advance.
pub open spec fn gaps<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,keys:Set<Address>)->bool {
    forall|i:int|0<=i<events.len() && keys.contains((#[trigger] events[i]).inverse().address) ==> {
        let event=events[i];let earlier=endpoint::latest(events,event.inverse().address,i as nat);
        recovery::quiet(event.checkpoint().events(),match earlier {Some(j)=>events[j as int].checkpoint().events().len(),None=>start.events().len()},event.read_cut(),event.inverse().address.key)
    }
}
proof fn observed<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,initial:Map<Address,Value<T>>,sources:Sources<payload::State<T>>,i:int)
    requires ordered(events,start),covered(steps,events,sources),gaps(events,start,initial.dom()),
        initial.dom()==function_endpoint::keys(steps),initial==function_endpoint::observe(steps,start.events(),start.events().len(),start.journal(),true),
        0<=i<events.len(),initial.contains_key(events[i].inverse().address),
    ensures events[i].observes(trajectory::values(events,initial,i as nat)),
{
    hide(joint::valid);hide(joint::step);
    let event=events[i];let key=event.inverse().address;let r=event.checkpoint();event.source_records();
    endpoint::latest_bound(events,key,i as nat);endpoint::last_value(events,initial,key,i as nat);
    match endpoint::latest(events,key,i as nat) {
        Some(j)=>{
            let prior=events[j as int];prior.source_records();let cut=prior.checkpoint().events().len();
            assert(joint::state_at(r.events(),cut)==joint::state_at(prior.checkpoint().events(),cut));
            function_endpoint::quiet_domain(r.events(),cut,event.read_cut(),key.key);
            prior.carrier().agreement(event.carrier(),joint::state_at(r.events(),cut)[key.key],sources);
        },
        None=>{
            function_endpoint::basis_exists(steps,key,true);let step=steps[function_endpoint::basis(steps,key,true)];
            let cut=start.events().len();let record=joint::state_at(start.events(),cut)[key.key];
            assert(joint::state_at(r.events(),cut)==joint::state_at(start.events(),cut));
            assert(function_endpoint::value_at(step,start.events(),cut)==Some(initial[key]));
            step.decoded_carrier(record);assert(step.carrier().describes(record));
            function_endpoint::quiet_domain(r.events(),cut,event.read_cut(),key.key);
            step.carrier().agreement(event.carrier(),record,sources);
        },
    }
}
/// Availability of successful inverse identities is a separate ownership
/// obligation. The value observation equality is derived, not a precondition.
pub proof fn linked_from_sources<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,initial:Map<Address,Value<T>>,slots:Seq<Option<obligations::Inverse<T>>>,sources:Sources<payload::State<T>>)
    requires ordered(events,start),covered(steps,events,sources),gaps(events,start,initial.dom()),
        initial.dom()==function_endpoint::keys(steps),initial==function_endpoint::observe(steps,start.events(),start.events().len(),start.journal(),true),
        forall|i:int|0<=i<events.len() && initial.contains_key((#[trigger] events[i]).inverse().address) && !events[i].forward() && events[i].succeeded() ==>
            trajectory::contains(trajectory::outstanding(events,slots,initial.dom(),i as nat),events[i].inverse()),
    ensures trajectory::linked(events,start,initial,slots),
{
    assert forall|i:int|0<=i<events.len() implies {
        let event=#[trigger] events[i];let checkpoint=event.checkpoint();let previous=if i==0 {start} else {events[i-1].checkpoint()};
        &&& event.source() && checkpoint.journal()==start.journal() && checkpoint.covers(&previous)
        &&& previous.events().len()<=event.read_cut()
        &&& initial.contains_key(event.inverse().address) ==> event.observes(trajectory::values(events,initial,i as nat))
        &&& initial.contains_key(event.inverse().address) && !event.forward() && event.succeeded() ==>
            trajectory::contains(trajectory::outstanding(events,slots,initial.dom(),i as nat),event.inverse())
    } by {if initial.contains_key(events[i].inverse().address) {observed(steps,events,start,initial,sources,i);}}
}
}
