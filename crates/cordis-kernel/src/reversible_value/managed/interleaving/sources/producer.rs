//! Complete producer census from actual storage ownership. This is a read
//! certificate, not a second executable log or a caller-provided coverage flag.
#[cfg(verus_keep_ghost)]
use super::super::obligations::Inverse;
use crate::reversible_value::{self as scalar, payload};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, managed::semantics::Value, service_composition::Address};
use vstd::prelude::*;

verus! {
pub ghost enum Producer<T:?Sized> {Scalar(scalar::Snapshot),Payload(payload::source::Source<T>)}
impl<T:?Sized> Producer<T> {
    pub open spec fn wf(&self)->bool {match self {Self::Scalar(s)=>s.certified(),Self::Payload(s)=>s.wf()}}
    pub open spec fn address(&self)->Address {match self {
        Self::Scalar(s)=>Address {journal:s.journal_spec(),key:s.object().key},
        Self::Payload(s)=>Address {journal:s.observation().owner.journal_spec(),key:s.observation().owner.key()},
    }}
    pub open spec fn frames(&self)->Seq<joint::Frame> {match self {Self::Scalar(s)=>s.joint_spec().events(),Self::Payload(s)=>s.observation_cut().events()}}
    pub open spec fn positions(&self)->Seq<nat> {match self {Self::Scalar(s)=>seq![s.birth()]+s.positions(),Self::Payload(s)=>s.positions()}}
    pub open spec fn kind(&self,i:int)->joint::Change {self.frames()[self.positions()[i] as int].event.change}
    pub open spec fn creates(&self,i:int)->bool {self.kind(i)==joint::Change::PayloadApply || self.kind(i) is Value && scalar::ownership::creates(self.kind(i)->Value_event)}
    pub open spec fn consumes(&self,i:int)->bool {self.kind(i)==joint::Change::PayloadRestore || self.kind(i) is Value && self.kind(i)->Value_event is Restore}
    /// All non-invertible writes remain visible to the recovery admission.
    pub open spec fn barrier(&self,i:int)->bool {self.kind(i)==joint::Change::PayloadReplace || self.kind(i)==joint::Change::PayloadRetire}
    pub open spec fn inverse(&self,i:int)->Inverse<T> {
        match self {
            Self::Scalar(_)=>{
                let event=self.kind(i)->Value_event;let state=if self.creates(i) {scalar::ownership::inverse(event)} else {event->Restore_inverse};
                Inverse {address:self.address(),before:Value::Scalar(state.before),after:Value::Scalar(state.after),
                    origin:if self.creates(i) {self.positions()[i]} else {event->Restore_origin}}
            },
            Self::Payload(s)=>{
                let states=s.observation().states;let head=if self.creates(i) {i} else {states[i-1].head as int};
                Inverse {address:self.address(),before:Value::Payload(states[head-1]),after:Value::Payload(states[head]),origin:self.positions()[head]}
            },
        }
    }
    pub open spec fn carrier(&self)->super::Carrier<T> {match self {
        Self::Scalar(_)=>super::Carrier::Scalar,
        Self::Payload(s)=>super::Carrier::Payload {source:s.observation().owner.source(),states:s.observation().states},
    }}
    pub open spec fn before(&self,i:int)->crate::reversible_value::managed::semantics::Value<T> {
        if self.creates(i) {self.inverse(i).before} else {self.inverse(i).after}
    }
    pub open spec fn after(&self,i:int)->crate::reversible_value::managed::semantics::Value<T> {
        if self.creates(i) {self.inverse(i).after} else {self.inverse(i).before}
    }
    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    pub proof fn mutation(&self,i:int)
        requires self.wf(),0<=i<self.positions().len(),self.creates(i) || self.consumes(i),
        ensures self.inverse(i).valid(),self.inverse(i).address==self.address(),
            self.creates(i) ==> self.inverse(i).origin==self.positions()[i],
            {let at=self.positions()[i];let input=joint::state_at(self.frames(),at);let output=joint::state_at(self.frames(),at+1);let key=self.address().key;
                &&& input.contains_key(key) && output.contains_key(key)
                &&& self.carrier().describes(input[key]) && self.carrier().describes(output[key])
                &&& self.carrier().decode(input[key])==Some(self.before(i))
                &&& self.carrier().decode(output[key])==Some(self.after(i))},
        decreases i,
    {
        hide(joint::valid);hide(joint::step);
        self.ordered();let at=self.positions()[i];let f=self.frames();let key=self.address().key;
        match self {
            Self::Scalar(s)=>{s.production_state();s.joint_spec().valid_history();},
            Self::Payload(s)=>{s.facts();},
        }
        assert(joint::step(joint::state_at(f,at),f[at as int].state,f[at as int].event)) by {reveal(joint::valid);}
        if self.consumes(i) {let c=self.consumption_source(i);self.mutation(c);}
        reveal(joint::step);reveal(joint::changes);
        match self {
            Self::Scalar(_)=>{},
            Self::Payload(s)=>{
                let v=s.observation();s.observation_cut().cover_through(&s.checkpoint(),&v.commit);
                assert(0<i<v.states.len());assert(f[at as int]==v.commit.events()[at as int]);
                reveal(payload::semantic_history::valid);
                assert(payload::semantic_history::entry(v.states,v.positions,v.commit.events(),i));
                if self.consumes(i) {let created=s.restore_origin(i);}
            },
        }
    }
    /// Includes every same-allocation frame, not only events previously
    /// observed by a managed caller. Birth, rejection and retirement are kept.
    pub proof fn complete_at(&self,at:nat)->(i:int)
        requires self.wf(),at<self.frames().len(),self.frames()[at as int].event.key==self.address().key,
        ensures 0<=i<self.positions().len(),self.positions()[i]==at,
    {
        match self {
            Self::Scalar(s)=>{if at==s.birth() {0} else {let i=s.source_at(at);i+1}},
            Self::Payload(s)=>s.source_at(at),
        }
    }
    pub proof fn ordered(&self)
        requires self.wf(),
        ensures forall|i:int,j:int|0<=i<j<self.positions().len() ==> #[trigger] self.positions()[i]<#[trigger] self.positions()[j],
            forall|i:int|0<=i<self.positions().len() ==> (#[trigger] self.positions()[i])<self.frames().len()
                && self.frames()[self.positions()[i] as int].event.key==self.address().key,
    {
        match self {
            Self::Scalar(s)=>{},
            Self::Payload(s)=>{
                s.facts();let v=s.observation();
                assert forall|i:int|0<=i<self.positions().len() implies (#[trigger] self.positions()[i])<self.frames().len()
                    && self.frames()[self.positions()[i] as int].event.key==self.address().key by {
                    if i<v.positions.len() {s.observation_cut().cover_through(&s.checkpoint(),&v.commit);assert(self.frames()[self.positions()[i] as int]==v.commit.events()[v.positions[i] as int]);}
                }
                assert forall|i:int,j:int|0<=i<j<self.positions().len() implies #[trigger] self.positions()[i]<#[trigger] self.positions()[j] by {
                    if j==v.positions.len() {assert(v.positions[i]<v.commit.events().len());}
                }
            },
        }
    }
    #[verifier::opaque]
    pub open spec fn certified(&self)->bool {
        self.wf()
            && (forall|at:int|0<=at<self.frames().len() && (#[trigger] self.frames()[at]).event.key==self.address().key ==> self.positions().contains(at as nat))
            && (forall|i:int|0<=i<self.positions().len() && #[trigger] self.consumes(i) ==> {
                &&& exists|created:int|0<=created<i && self.creates(created) && self.inverse(created)==self.inverse(i)
                &&& forall|j:int|0<=j<self.positions().len() && #[trigger] self.consumes(j) && self.inverse(j).origin==self.inverse(i).origin ==> j==i
            })
    }
    /// Called by the real host source-snapshot methods before returning.
    pub proof fn certify(&self)
        requires self.wf(),ensures self.certified(),
    {
        reveal(Producer::certified);
        assert forall|at:int|0<=at<self.frames().len() && (#[trigger] self.frames()[at]).event.key==self.address().key implies self.positions().contains(at as nat) by {
            let i=self.complete_at(at as nat);assert(self.positions()[i]==at);
        }
        assert forall|i:int|0<=i<self.positions().len() && #[trigger] self.consumes(i) implies {
            &&& exists|created:int|0<=created<i && self.creates(created) && self.inverse(created)==self.inverse(i)
            &&& forall|j:int|0<=j<self.positions().len() && #[trigger] self.consumes(j) && self.inverse(j).origin==self.inverse(i).origin ==> j==i
        } by {let created=self.consumption_source(i);assert(self.creates(created));}
    }
    /// Both creation and unique successful consumption follow from the actual
    /// ownership protocol. No `origins::admitted` premise is required here.
    #[verifier::spinoff_prover]
    pub proof fn consumption_source(&self,i:int)->(created:int)
        requires self.wf(),0<=i<self.positions().len(),self.consumes(i),
        ensures 0<=created<i,self.creates(created),self.inverse(created)==self.inverse(i),
            forall|j:int|0<=j<self.positions().len() && #[trigger] self.consumes(j)
                && self.inverse(j).origin==self.inverse(i).origin ==> j==i,
    {
        self.ordered();
        match self {
            Self::Scalar(s)=>{
                assert(i>0);assert(s.history()[i-1] is Restore);let at=s.restore_origin(i-1);
                assert forall|j:int|0<=j<self.positions().len() && #[trigger] self.consumes(j)
                    && self.inverse(j).origin==self.inverse(i).origin implies j==i by {
                    assert(j>0);assert(s.history()[j-1] is Restore);assert(s.history()[j-1]->Restore_origin==s.history()[i-1]->Restore_origin);
                }
                at+1
            },
            Self::Payload(s)=>{
                s.facts();let v=s.observation();assert(0<i<v.states.len());let at=s.restore_origin(i);
                assert forall|j:int|0<=j<self.positions().len() && #[trigger] self.consumes(j)
                    && self.inverse(j).origin==self.inverse(i).origin implies j==i by {
                    assert(0<j<v.states.len());let other=s.restore_origin(j);
                    assert(self.positions()[other]==self.positions()[at]);
                    if other<at {assert(self.positions()[other]<self.positions()[at]);}
                    if at<other {assert(self.positions()[at]<self.positions()[other]);}
                    assert(v.states[j-1].head==v.states[i-1].head);
                }
                at
            },
        }
    }
}
}
