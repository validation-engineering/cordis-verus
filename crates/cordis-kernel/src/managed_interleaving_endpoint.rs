//! Decode the common native Unload cut from the last actual source for each
//! touched allocation. A quiet tail excludes post-restoration interference.
#[cfg(verus_keep_ghost)]
use super::{completion, linked, values};
use super::{Attempt, Event, Forward};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::native::runtime::episode::Unload;
use crate::reversible_value::effect::ScalarEffect;
use crate::reversible_value::managed::root::RegisteredReport;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::Step;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    joint,
    managed::{episode::endpoint as function_endpoint, recovery, semantics::Value, Owner},
    service_composition::Address,
};
use vstd::prelude::*;

verus! {
impl<T:?Sized> Forward<T> {
    pub open spec fn decode(&self,record:joint::Record)->Option<Value<T>> {
        match (self,record) {
            (Self::Scalar(_),joint::Record::Object {state,..})=>Some(Value::Scalar(state)),
            (Self::Payload(i),joint::Record::Payload {source,revision})=>
                if source==i.owner().source() && revision<i.after().states.len() {Some(Value::Payload(i.after().states[revision as int]))} else {None},
            _=>None,
        }
    }
    pub proof fn recorded_output(&self)
        requires self.source(),
        ensures self.write().wf(),self.write().journal()==self.inverse().address.journal,
            joint::state_at(self.write().events(),self.write().events().len()).contains_key(self.inverse().address.key),
            self.decode(joint::state_at(self.write().events(),self.write().events().len())[self.inverse().address.key])==Some(self.inverse().after),
    {
        self.facts();recovery::frame_update(self.write().events(),self.write().at());
        match self {
            Self::Scalar(_)=>{reveal(joint::step);reveal(joint::changes);},
            Self::Payload(i)=>{i.provenance();i.source_history();},
        }
    }
}
impl<T:?Sized> Attempt<T> {
    pub open spec fn decode(&self,record:joint::Record)->Option<Value<T>> {
        match self {
            Self::Scalar {..}=>match record {joint::Record::Object {state,..}=>Some(Value::Scalar(state)),_=>None},
            Self::Payload(a)=>{
                let states=if a.result().is_ok() {a.result()->Ok_0.after().states}
                    else if a.read().value().is_some() {a.read().value().unwrap().states} else {Seq::empty()};
                match record {joint::Record::Payload {source,revision}=>
                    if source==a.inverse().owner().source() && revision<states.len() {Some(Value::Payload(states[revision as int]))} else {None},_=>None}
            },
        }
    }
    #[verifier::spinoff_prover]
    pub proof fn recorded_output(&self)
        requires self.source(),
        ensures self.checkpoint().wf(),self.checkpoint().journal()==self.forward().inverse().address.journal,
            joint::state_at(self.checkpoint().events(),self.checkpoint().events().len()).contains_key(self.forward().inverse().address.key),
            self.decode(joint::state_at(self.checkpoint().events(),self.checkpoint().events().len())[self.forward().inverse().address.key])==self.landed(),
    {
        self.facts();let end=self.checkpoint();recovery::frame_update(end.events(),end.at());
        match self {
            Self::Scalar {..}=>{reveal(joint::step);reveal(joint::changes);},
            Self::Payload(a)=>{
                a.facts();a.boundaries();
                if a.result().is_ok() {a.result()->Ok_0.source_history();}
            },
        }
    }
}
impl<A,R,T:?Sized,M,X> Event<A,R,T,M,X> {
    pub open spec fn decode(&self,record:joint::Record)->Option<Value<T>> {
        match self {Self::Forward(f)=>f.decode(record),Self::Managed(d)=>d.decode(record),Self::Restore(a)=>a.decode(record),Self::Produced(e)=>e.producer.carrier().decode(record)}
    }
    pub open spec fn value_at(&self,frames:Seq<joint::Frame>,cut:nat)->Option<Value<T>> {
        let state=joint::state_at(frames,cut);let key=self.inverse().address.key;
        if state.contains_key(key) {self.decode(state[key])} else {None}
    }
    pub proof fn recorded_output(&self)
        requires self.source(),
        ensures self.checkpoint().wf(),self.checkpoint().journal()==self.inverse().address.journal,
            self.value_at(self.checkpoint().events(),self.checkpoint().events().len())==self.landed(),
    {
        match self {
            Self::Forward(f)=>f.recorded_output(),Self::Restore(a)=>a.recorded_output(),Self::Produced(e)=>e.facts(),
            Self::Managed(d)=>{
                reveal(crate::cleanup_groups::payload::Dispatch::recovery);
                let action=d.before_queue().slots()[d.ticket().token as int].unwrap();
                assert(d.recorded(action));
                assert(self.inverse().address==crate::cleanup_groups::payload::recovery::address(action));
            },
        }
    }
}
pub open spec fn latest<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,key:Address,n:nat)->Option<nat>
    decreases n,
{if n==0 {None} else if events[n-1].inverse().address==key {Some((n-1) as nat)} else {latest(events,key,(n-1) as nat)}}
pub(crate) proof fn latest_bound<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,key:Address,n:nat)
    requires n<=events.len(),
    ensures latest(events,key,n).is_some() ==> latest(events,key,n).unwrap()<n && events[latest(events,key,n).unwrap() as int].inverse().address==key,
    decreases n,
{if n>0 {latest_bound(events,key,(n-1) as nat);}}
pub open spec fn lookup<T:?Sized>(heap:Map<Address,Value<T>>,key:Address)->Option<Value<T>> {if heap.contains_key(key) {Some(heap[key])} else {None}}
pub(crate) proof fn last_value<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,initial:Map<Address,Value<T>>,key:Address,n:nat)
    requires n<=events.len(),initial.contains_key(key),
    ensures lookup(values(events,initial,n),key)==match latest(events,key,n) {Some(i)=>events[i as int].landed(),None=>Some(initial[key])},
    decreases n,
{
    if n>0 {
        last_value(events,initial,key,(n-1) as nat);
        let event=events[n-1];
        if event.inverse().address!=key {assert(lookup(event.apply(values(events,initial,(n-1) as nat),initial.dom()),key)==lookup(values(events,initial,(n-1) as nat),key));}
    }
}
proof fn domain<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,initial:Map<Address,Value<T>>,n:nat)
    requires n<=events.len(),ensures values(events,initial,n).dom().subset_of(initial.dom()),
    decreases n,
{if n>0 {domain(events,initial,(n-1) as nat);}}
pub open spec fn output<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,end:joint::Receipt,key:Address)->Option<Value<T>> {
    match latest(events,key,events.len()) {
        Some(i)=>events[i as int].value_at(end.events(),end.events().len()),
        None=>function_endpoint::value_at(steps[function_endpoint::basis(steps,key,true)],end.events(),end.events().len()),
    }
}
/// The map is decoded at one actual checkpoint, not assembled from values
/// read at different times or supplied as the desired restoration result.
pub open spec fn observe<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,end:joint::Receipt)->Map<Address,Value<T>> {
    Map::new(function_endpoint::keys(steps).filter(|key:Address|key.journal==end.journal() && output(steps,events,end,key).is_some()),
        |key:Address|output(steps,events,end,key).unwrap())
}
pub open spec fn quiet_tail<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,end:joint::Receipt)->bool {
    forall|key:Address|function_endpoint::keys(steps).contains(key) ==> recovery::quiet(end.events(),
        match latest(events,key,events.len()) {Some(i)=>events[i as int].checkpoint().events().len(),None=>start.events().len()},end.events().len(),key.key)
}
pub open spec fn bounded<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,end:joint::Receipt)->bool {
    start.wf() && end.wf() && end.covers(&start)
        && forall|i:int|0<=i<events.len() ==> (#[trigger] events[i]).source() && end.covers(&events[i].checkpoint())
}
proof fn output_matches<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,end:joint::Receipt,initial:Map<Address,Value<T>>,key:Address)
    requires bounded(events,start,end),quiet_tail(steps,events,start,end),initial.dom()==function_endpoint::keys(steps),
        initial==function_endpoint::observe(steps,start.events(),start.events().len(),start.journal(),true),initial.contains_key(key),
    ensures key.journal==end.journal(),output(steps,events,end,key)==lookup(values(events,initial,events.len()),key),
{
    hide(joint::valid);hide(joint::step);
    latest_bound(events,key,events.len());last_value(events,initial,key,events.len());
    match latest(events,key,events.len()) {
        Some(i)=>{
            let event=events[i as int];event.recorded_output();let cut=event.checkpoint().events().len();
            assert(joint::state_at(end.events(),cut)==joint::state_at(event.checkpoint().events(),cut));
            function_endpoint::quiet_domain(end.events(),cut,end.events().len(),key.key);
        },
        None=>{
            function_endpoint::basis_exists(steps,key,true);
            assert(joint::state_at(end.events(),start.events().len())==joint::state_at(start.events(),start.events().len()));
            function_endpoint::quiet_domain(end.events(),start.events().len(),end.events().len(),key.key);
        },
    }
}
pub proof fn observe_matches<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,end:joint::Receipt,initial:Map<Address,Value<T>>)
    requires bounded(events,start,end),quiet_tail(steps,events,start,end),initial.dom()==function_endpoint::keys(steps),
        initial==function_endpoint::observe(steps,start.events(),start.events().len(),start.journal(),true),
    ensures observe(steps,events,end)==values(events,initial,events.len()),
{
    hide(output);hide(Event::decode);hide(function_endpoint::value_at);hide(Step::decode);
    domain(events,initial,events.len());
    assert forall|key:Address|initial.contains_key(key) implies key.journal==end.journal()
        && output(steps,events,end,key)==lookup(values(events,initial,events.len()),key) by {output_matches(steps,events,start,end,initial,key);}
    assert(observe(steps,events,end) =~= values(events,initial,events.len()));
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    pub open spec fn unload_source<A,R,M,X>(&self,events:Seq<Event<A,R,T,M,X>>,end:&Unload)->bool {
        end.wf() && end.owner()==self.start().owner() && end.native()==self.start().native()
            && bounded(events,self.completion(),end.checkpoint())
            && quiet_tail(self.result->Ok_0.steps@,events,self.completion(),end.checkpoint())
    }
    pub open spec fn unload_values<A,R,M,X>(&self,events:Seq<Event<A,R,T,M,X>>,end:&Unload)->Map<Address,Value<T>> {
        observe(self.result->Ok_0.steps@,events,end.checkpoint())
    }
    /// The endpoint is created by real successful native release. The source
    /// conditions check identities, actual prefixes and unchanged tail gaps;
    /// neither the final heap nor inverse success is assumed.
    pub proof fn unload_recovers_begin<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,events:Seq<Event<A,R,T,M,X>>,end:&Unload)
        requires owner.wf(),owner.cleanup_state().live(id),self.start().owner().owns(&owner),
            self.completed(),self.effects_before_return(),self.episode_interval(),self.endpoint_source(),
            self.result->Ok_0.witnessed(),self.result->Ok_0.recovery_history(),
            self.retained_recovery(owner,id,offset),super::super::retained(self.result->Ok_0.steps@,owner,id,offset),
            linked(events,self.completion(),self.return_values(),self.obligations(owner,id,offset)),self.unload_source(events,end),
            completion::settled(events,self.obligations(owner,id,offset),self.return_values().dom()),
        ensures self.unload_values(events,end)==self.begin_values(),
            self.start().recorded(end.checkpoint().events()),end.recorded(end.checkpoint().events()),self.start().at()<end.at(),
    {
        hide(joint::valid);hide(joint::step);
        self.source_bounds();let steps=self.result->Ok_0.steps@;
        function_endpoint::final_observation(steps,self.completion());
        function_endpoint::landed_domain(steps,super::super::recovery::word::initial(steps));
        assert(self.return_values().dom()==function_endpoint::keys(steps));
        observe_matches(steps,events,self.completion(),end.checkpoint(),self.return_values());
        self.settled_recovers_begin(owner,id,offset,events);
        end.facts();self.start().facts();end.checkpoint().cover_through(&self.completion(),&self.start().checkpoint());
        self.start().extend(&end.checkpoint());
    }
}
}
