//! Decode interleaved values from authenticated, persistent payload histories.
//! Equal allocation/revision numbers alone are deliberately insufficient.
use super::{Attempt, Event, Forward};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::Report;
use crate::reversible_value::{history::sources::Sources, managed::Step, payload};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    joint,
    managed::{self, semantics::Value},
};
use vstd::prelude::*;
use vstd::resource::Loc;

#[path = "managed_source_coverage.rs"]
pub mod coverage;
#[path = "managed_source_link.rs"]
pub mod link;
#[path = "managed_source_order.rs"]
pub mod order;
#[path = "managed_source_obligations.rs"]
pub mod origins;

#[path = "managed_producer_interval.rs"]
pub mod interval;
#[path = "managed_producer_matching.rs"]
pub mod matching;
#[path = "managed_producer_event.rs"]
pub mod produced;
#[path = "managed_producer_sources.rs"]
pub mod producer;

verus! {
pub ghost enum Carrier<T:?Sized> {Scalar,Payload {source:Loc,states:Seq<payload::State<T>>}}
impl<T:?Sized> Carrier<T> {
    pub open spec fn covered(&self,sources:Sources<payload::State<T>>)->bool {
        match self {Self::Scalar=>true,Self::Payload {source,states}=>states.len()==0 || sources.covers(*source,*states)}
    }
    pub open spec fn decode(&self,record:joint::Record)->Option<Value<T>> {
        match (self,record) {
            (Self::Scalar,joint::Record::Object {state,..})=>Some(Value::Scalar(state)),
            (Self::Payload {source,states},joint::Record::Payload {source:actual,revision})=>
                if *source==actual && revision<states.len() {Some(Value::Payload(states[revision as int]))} else {None},
            _=>None,
        }
    }
    /// A source explains this actual record, including typed retirement.
    pub open spec fn describes(&self,record:joint::Record)->bool {
        match (self,record) {
            (Self::Scalar,joint::Record::Object {..})=>true,
            (Self::Payload {source,states},joint::Record::Payload {source:actual,revision})=>*source==actual && revision<states.len(),
            (Self::Payload {source,..},joint::Record::RetiredPayload {source:actual,..})=>*source==actual,
            _=>false,
        }
    }
    pub proof fn agreement(&self,other:Self,record:joint::Record,sources:Sources<payload::State<T>>)
        requires sources.wf(),self.covered(sources),other.covered(sources),self.describes(record),other.describes(record),
        ensures self.decode(record)==other.decode(record),
    {
        match (self,other,record) {
            (Self::Payload {source,states:left},Self::Payload {states:right,..},joint::Record::Payload {revision,..})=>{
                if left.len()<=right.len() {sources.agreement(*source,*left,right);assert(right[revision as int]==left[revision as int]);}
                else {sources.agreement(*source,right,*left);assert(left[revision as int]==right[revision as int]);}
            },_=>{},
        }
    }
}
impl<T:?Sized> Forward<T> {
    pub open spec fn carrier(&self)->Carrier<T> {
        match self {Self::Scalar(_)=>Carrier::Scalar,Self::Payload(i)=>Carrier::Payload {source:i.owner().source(),states:i.after().states}}
    }
}
impl<T:?Sized> Attempt<T> {
    pub open spec fn carrier(&self)->Carrier<T> {
        match self {Self::Scalar {..}=>Carrier::Scalar,Self::Payload(a)=>Carrier::Payload {source:a.inverse().owner().source(),states:a.states()}}
    }
}
impl<A,R,T:?Sized,M,X> Event<A,R,T,M,X> {
    pub open spec fn carrier(&self)->Carrier<T> {
        match self {Self::Forward(f)=>f.carrier(),Self::Restore(a)=>a.carrier(),Self::Managed(d)=>d.carrier(),Self::Produced(e)=>e.producer.carrier()}
    }
    pub proof fn decoded_carrier(&self,record:joint::Record)
        requires self.source(),
        ensures self.decode(record)==self.carrier().decode(record),
    {}
}
impl<T:?Sized> Step<T> {
    pub open spec fn carrier(&self)->Carrier<T> {self.forward_inverse().carrier()}
    pub proof fn decoded_carrier(&self,record:joint::Record)
        ensures self.decode(record)==self.carrier().decode(record),
    {}
}
impl<T:?Sized> Sources<payload::State<T>> {
    proof fn report_prefix(tracked &mut self,tracked report:&Report<T>,count:nat)
        requires old(self).wf(),report.witnessed(),count<=report.steps.len(),
        ensures final(self).wf(),final(self).extends(*old(self)),
            forall|i:int|0<=i<count ==> (#[trigger] report.steps@[i]).carrier().covered(*final(self)),
        decreases count,
    {
        if count>0 {
            let prior=*self;self.report_prefix(report,(count-1) as nat);let middle=*self;
            let i=count-1;let step=report.steps@[i];
            if let managed::ResultStep::Payload(a)=step.result {
                reveal(managed::histories_recorded);
                let tracked witness=report.histories.borrow().tracked_borrow(i).duplicate();
                self.retain(witness);
            }
            assert forall|source:Loc,events:Seq<payload::State<T>>|#[trigger] prior.covers(source,events) implies self.covers(source,events) by {assert(middle.covers(source,events));}
            assert forall|j:int|0<=j<count implies (#[trigger] report.steps@[j]).carrier().covered(*self) by {
                if j<i {assert(report.steps@[j].carrier().covered(middle));}
            }
        }
    }
    /// Called with the actual interpreter result, including failed prefixes.
    pub proof fn retain_report(tracked &mut self,tracked report:&Report<T>)
        requires old(self).wf(),report.witnessed(),
        ensures final(self).wf(),final(self).extends(*old(self)),
            forall|i:int|0<=i<report.steps.len() ==> (#[trigger] report.steps@[i]).carrier().covered(*final(self)),
    {self.report_prefix(report,report.steps.len() as nat);}
    pub proof fn retain_dispatch<A,R,M,X>(tracked &mut self,tracked dispatch:&managed::cleanup_path::Turn<A,R,T,M,X>)
        requires old(self).wf(),dispatch.authentic(),dispatch.managed(),
        ensures final(self).wf(),final(self).extends(*old(self)),dispatch.carrier().covered(*final(self)),
    {
        let tracked witness=dispatch.payload_history_witness();
        if let Some(witness)=witness {self.retain(witness);}
    }
}
}
