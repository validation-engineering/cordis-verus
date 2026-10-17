//! Replacement versions belong to the actual value, not host shadow counters.
//! A retained observation denotes the value at one read; later replacements do
//! not rewrite that observation. The history is erased in ordinary Rust.
use vstd::prelude::*;

verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum ReplaceError {Stale,Capacity,Closed}
pub struct Rejected<T> {pub error:ReplaceError,pub value:T}

#[allow(dead_code)]
pub struct VersionedValue<T> {value:T,revision:u64,history:Ghost<Seq<T>>}
impl<T> VersionedValue<T> {
    pub closed spec fn value(&self)->T {self.value}
    pub closed spec fn revision_spec(&self)->u64 {self.revision}
    pub closed spec fn history(&self)->Seq<T> {self.history@}
    pub closed spec fn wf(&self)->bool {
        self.history().len()==self.revision_spec() as nat+1 && self.history().last()==self.value()
    }
    pub proof fn representation(&self)
        requires self.wf(),
        ensures self.history().len()==self.revision_spec() as nat+1,self.history().last()==self.value(),
    { }
    pub fn new(value:T)->(out:Self)
        ensures out.wf(),out.value()==value,out.revision_spec()==0,out.history()==seq![value],
    {Self {value,revision:0,history:Ghost(Seq::empty().push(value))}}
    pub fn into_inner(self)->(out:T) ensures out==self.value(), {self.value}
    pub fn get(&self)->(out:&T) ensures *out==self.value(), {&self.value}
    pub fn revision(&self)->(out:u64) ensures out==self.revision_spec(), {self.revision}
    pub fn accepts_result(&self,observed:u64,result:bool)->(out:bool)
        ensures out==(observed==self.revision_spec() && result),
    {observed==self.revision && result}
    /// The payload and its version are observed through the same borrow.
    pub fn observe(&self)->(out:(u64,&T))
        requires self.wf(),
        ensures out.0==self.revision_spec(),*out.1==self.value(),self.history()[out.0 as int]==*out.1,
    {(self.revision,&self.value)}
    pub fn replace(&mut self,value:T)->(out:Result<T,Rejected<T>>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_ok()==(old(self).revision_spec()<u64::MAX),
            out.is_ok() ==> out->Ok_0==old(self).value() && final(self).value()==value
                && final(self).revision_spec()==old(self).revision_spec()+1
                && final(self).history()==old(self).history().push(value),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.error==ReplaceError::Capacity && out->Err_0.value==value,
    {
        if self.revision==u64::MAX {return Err(Rejected {error:ReplaceError::Capacity,value});}
        let mut previous=value;core::mem::swap(&mut self.value,&mut previous);
        self.revision+=1;
        proof {self.history=Ghost(self.history().push(value));}
        Ok(previous)
    }
    /// Compare the real cell version, with no separate caller-supplied current
    /// version. Rejection preserves both the cell and the supplied value.
    pub fn replace_if(&mut self,expected:u64,value:T)->(out:Result<T,Rejected<T>>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok()==(expected==old(self).revision_spec() && expected<u64::MAX),
            out.is_ok() ==> out->Ok_0==old(self).value() && final(self).value()==value
                && final(self).revision_spec()==expected+1 && final(self).history()==old(self).history().push(value),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.value==value
                && out->Err_0.error==if expected!=old(self).revision_spec() {ReplaceError::Stale} else {ReplaceError::Capacity},
    {
        if self.revision!=expected {return Err(Rejected {error:ReplaceError::Stale,value});}
        self.replace(value)
    }
    /// A replacement back to an equal payload still advances the version.
    pub proof fn retained_prefix(&self,earlier:Self)
        requires self.wf(),earlier.wf(),earlier.history().len()<=self.history().len(),
            self.history().take(earlier.history().len() as int)==earlier.history(),
        ensures earlier.revision_spec()<=self.revision_spec(),
            self.history()[earlier.revision_spec() as int]==earlier.value(),
    { }
}
}
