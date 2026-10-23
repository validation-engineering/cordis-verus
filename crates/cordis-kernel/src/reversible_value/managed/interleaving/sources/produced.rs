//! A projected mutation keeps the actual producer and authentic Journal cut.
//! It is not a fabricated executable inverse or a second writer.
use super::producer::Producer;
use crate::reversible_value::joint;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::semantics::Value;
use vstd::prelude::*;

verus! {
pub ghost struct Produced<T:?Sized> {pub producer:Producer<T>,pub index:int,pub receipt:joint::Receipt}
impl<T:?Sized> Produced<T> {
    pub open spec fn wf(&self)->bool {
        let p=self.producer;let i=self.index;let r=self.receipt;
        &&& p.wf() && 0<=i<p.positions().len() && (p.creates(i) || p.consumes(i))
        &&& r.wf() && r.journal()==p.address().journal && r.at()==p.positions()[i]
        &&& r.events().len()<=p.frames().len() && r.event().key==p.address().key
        &&& r.events()==p.frames().take(r.events().len() as int)
    }
    pub open spec fn inverse(&self)->super::super::obligations::Inverse<T> {self.producer.inverse(self.index)}
    pub open spec fn forward(&self)->bool {self.producer.creates(self.index)}
    pub open spec fn before(&self)->Value<T> {self.producer.before(self.index)}
    pub open spec fn after(&self)->Value<T> {self.producer.after(self.index)}
    #[verifier::spinoff_prover]
    pub proof fn facts(&self)
        requires self.wf(),
        ensures self.inverse().valid(),self.inverse().address==self.producer.address(),
            self.forward() ==> self.before()==self.inverse().before && self.after()==self.inverse().after,
            !self.forward() ==> self.before()==self.inverse().after && self.after()==self.inverse().before,
            {let input=joint::state_at(self.receipt.events(),self.receipt.at());let output=joint::state_at(self.receipt.events(),self.receipt.events().len());let key=self.inverse().address.key;
                &&& input.contains_key(key) && output.contains_key(key)
                &&& self.producer.carrier().describes(input[key]) && self.producer.carrier().describes(output[key])
                &&& self.producer.carrier().decode(input[key])==Some(self.before())
                &&& self.producer.carrier().decode(output[key])==Some(self.after())},
    {
        hide(joint::valid);hide(joint::step);
        self.producer.mutation(self.index);
        assert(joint::state_at(self.receipt.events(),self.receipt.at())==joint::state_at(self.producer.frames(),self.receipt.at()));
    }
    pub proof fn new(producer:Producer<T>,index:int,tracked end:&joint::Receipt)->(out:Self)
        requires producer.wf(),0<=index<producer.positions().len(),producer.creates(index) || producer.consumes(index),
            end.wf(),end.journal()==producer.address().journal,producer.positions()[index]<end.events().len(),
            end.events().len()<=producer.frames().len(),producer.frames().take(end.events().len() as int)==end.events(),
        ensures out.wf(),out.producer==producer,out.index==index,end.covers(&out.receipt),
    {
        producer.ordered();
        let tracked receipt=end.prefix(producer.positions()[index]+1);
        assert(receipt.events() =~= producer.frames().take(receipt.events().len() as int));
        Self {producer,index,receipt}
    }
}
}
