//! Copy a previously unaccessed closed object from an actual checkpoint.
//! Outstanding inverse debt is not invented in a newly allocated target.
use super::{Error, Object};
use crate::reversible_value::{
    self as scalar,
    closed::{Reference, Value},
    joint, payload,
};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
pub ghost enum Origin {Scalar(scalar::Snapshot),Payload(payload::Capture<Value>),Retired(payload::Retirement<Value>)}
pub struct Copy {pub object:Object,pub origin:Ghost<Origin>,pub retired:Tracked<Option<joint::Receipt>>}
impl Copy {
    pub closed spec fn from(&self,source:Object)->bool {
        match (self.origin@,source,self.object) {
            (Origin::Scalar(s),Object::Scalar(a),Object::Scalar(b))=>s.certified() && s.journal_spec()==a.journal_spec() && s.object()==a.object()
                && s.state().depth==0 && b.initial()==s.state() && self.retired@.is_none(),
            (Origin::Payload(s),Object::Payload(a),Object::Payload(b))=>s.wf() && s.owner()==a && s.observation().state().depth==0 && b.initial()==s.value_spec() && self.retired@.is_none(),
            (Origin::Retired(s),Object::Payload(a),Object::Payload(b))=>s.wf() && s.owner()==a && self.retired@.is_some()
                && self.retired@.unwrap().wf() && self.retired@.unwrap().journal()==b.journal_spec() && self.retired@.unwrap().event().key==b.key()
                && self.retired@.unwrap().event().after is RetiredPayload,
            _=>false,
        }
    }
}
impl Object {
    #[allow(unused_variables)] // Runtime arguments also anchor erased provenance contracts.
    pub(super) fn copy_checkpoint(&self,journal:&joint::Journal,schema:&[Reference])->(out:Result<Copy,Error>)
        ensures out.is_ok() ==> out->Ok_0.from(*self) && out->Ok_0.object.address().journal==*journal && out->Ok_0.object.kind()==self.kind(),
    {
        match self {
            Self::Scalar(source)=>{
                let snapshot=source.snapshot();if snapshot.depth()!=0 {return Err(Error::History);}
                let object=scalar::ReversibleValue::new_in(journal,snapshot.value());
                Ok(Copy {object:Object::Scalar(object),origin:Ghost(Origin::Scalar(snapshot)),retired:Tracked(None)})
            },
            Self::Payload(source)=>match source.status() {
                payload::Status::Live(snapshot)=>{
                    if snapshot.depth()!=0 {return Err(Error::History);}
                    let value=snapshot.value();value.representation();if !value.check(schema) {return Err(Error::Reference);}
                    let object=payload::SharedPayload::new_in(journal,value.clone());
                    Ok(Copy {object:Object::Payload(object),origin:Ghost(Origin::Payload(snapshot)),retired:Tracked(None)})
                },
                payload::Status::Retired(snapshot)=>{
                    let object=payload::SharedPayload::new_in(journal,Arc::new(Value::null()));
                    let retired=match object.retire() {Some(r)=>r,None=>return Err(Error::History)};
                    let tracked receipt=retired.receipt();
                    Ok(Copy {object:Object::Payload(object),origin:Ghost(Origin::Retired(snapshot)),retired:Tracked(Some(receipt))})
                },
            },
        }
    }
}
}
