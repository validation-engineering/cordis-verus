//! Complete declared service observations at the real invocation boundary.
//! An unvisited declaration has no fabricated Step or inverse: its selection
//! is retained directly from the actual Episode, including failed reads.
use super::super::Slot;
use crate::lifecycle_state::services::{NativeEpisode, NativeReadError};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::service_composition::Address;
use crate::reversible_value::{joint, payload::SharedPayload, slot};
use crate::{action_ledger::ActionTicket, Port};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub enum Selected<T:?Sized> {Scalar(slot::Capture),Payload(SharedPayload<T>)}
impl<T:?Sized> Selected<T> {
    pub open spec fn wf(&self)->bool {match self {Self::Scalar(c)=>c.wf(),Self::Payload(_)=>true}}
    pub open spec fn address(&self)->Address {
        match self {Self::Scalar(c)=>Address {journal:c.value_spec().journal_spec(),key:c.value_spec().object().key},Self::Payload(v)=>Address {journal:v.journal_spec(),key:v.key()}}
    }
    pub open spec fn describes<M>(&self,slot:Arc<Slot<T,M>>)->bool {
        match self {Self::Scalar(c)=>slot.managed()==Some(c.slot()),Self::Payload(v)=>slot.opaque_spec()==Some(*v)}
    }
    pub open spec fn namespace(&self,namespace:vstd::resource::Loc)->bool {
        self.address().journal.identity_namespace()==namespace && match self {
            Self::Scalar(c)=>c.slot().journal_spec().identity_namespace()==namespace,_=>true,
        }
    }
    pub fn scalar_slot(&self)->(out:Option<Arc<joint::identity::AllocationIdentity>>)
        requires self.wf(),ensures out.is_some()==(self is Scalar),out.is_some() ==> out.unwrap().wf()
            && out.unwrap().address()==(Address {journal:self->Scalar_0.slot().journal_spec(),key:self->Scalar_0.slot().key()}),
    {match self {Self::Scalar(c)=>Some(c.slot_ref().identity()),Self::Payload(_)=>None}}
    pub fn identity(&self)->(out:Arc<joint::identity::AllocationIdentity>)
        requires self.wf(),ensures out.wf(),out.address()==self.address(),
    {match self {Self::Scalar(c)=>c.value().identity(),Self::Payload(v)=>v.identity()}}
    fn capture<M>(slot:&Slot<T,M>)->(out:Self)
        ensures out.wf(),match out {Self::Scalar(c)=>slot.managed()==Some(c.slot()),Self::Payload(v)=>slot.opaque_spec()==Some(v)},
    {
        match slot.reversible() {
            Some(value)=>Self::Scalar(value.capture()),
            None=>{proof {slot.payload_partition();}Self::Payload(slot.opaque().unwrap().clone())},
        }
    }
}
pub struct Binding<T:?Sized> {pub provider:usize,pub origin:ActionTicket,pub selected:Selected<T>}
pub struct Entry<T:?Sized> {pub port:Port,pub result:Result<Binding<T>,NativeReadError>}
impl<T:?Sized> Entry<T> {
    pub open spec fn wf(&self)->bool {self.result.is_ok() ==> self.result->Ok_0.selected.wf()}
    pub open spec fn captured<M>(&self,episode:NativeEpisode<Slot<T,M>>)->bool {
        self.wf() && match self.result {
            Ok(binding)=>(if episode.provisions().contains(self.port) {binding.origin==episode.origin()} else {episode.capture().sources.contains_key(binding.provider) && binding.origin==episode.capture().sources[binding.provider].origin})
                && exists|value:Arc<Slot<T,M>>|episode.selects_value(binding.provider,self.port,value) && binding.selected.describes(value),
            Err(error)=>episode.read_failed(self.port,error),
        }
    }
    fn capture<M>(episode:&NativeEpisode<Slot<T,M>>,port:Port)->(out:Self)
        requires episode.wf(),ensures out.port==port,out.captured(*episode),
    {
        let result=match episode.read(port) {
            Ok((provider,value))=>{
                let selected=Selected::capture(value);
                proof {assert(exists|v:Arc<Slot<T,M>>|episode.selects_value(provider,port,v) && selected.describes(v)) by {assert(selected.describes(*value));};}
                proof {assert(exists|v:Arc<Slot<T,M>>|episode.selects_value(provider,port,v)) by {assert(episode.selects_value(provider,port,*value));}}
                let origin=episode.provider_origin(provider,port).unwrap();
                Ok(Binding {provider,origin,selected})
            },
            Err(error)=>Err(error),
        };
        Self {port,result}
    }
}
#[allow(dead_code)] // The authentic context is retained independently of mutable storage.
pub struct Environment<T:?Sized> {origin:ActionTicket,work:u64,entries:Vec<Entry<T>>}
impl<T:?Sized> Environment<T> {
    pub closed spec fn entries(&self)->Seq<Entry<T>> {self.entries@}
    pub closed spec fn origin(&self)->ActionTicket {self.origin}
    pub closed spec fn work(&self)->u64 {self.work}
    pub open spec fn wf(&self)->bool {forall|i:int|0<=i<self.entries().len() ==> (#[trigger] self.entries()[i]).wf()}
    pub open spec fn declarations(&self,ports:Seq<Port>)->bool {
        ports.len()==self.entries().len() && forall|i:int|0<=i<ports.len() ==> (#[trigger] self.entries()[i]).port==ports[i]
    }
    pub open spec fn captured<M>(&self,episode:NativeEpisode<Slot<T,M>>,ports:Seq<Port>)->bool {
        self.wf() && self.origin()==episode.origin() && self.work()==episode.domain_id() && self.declarations(ports)
            && forall|i:int|0<=i<self.entries().len() ==> (#[trigger] self.entries()[i]).captured(episode)
    }
    pub open spec fn namespace(&self,namespace:vstd::resource::Loc)->bool {
        forall|i:int|0<=i<self.entries().len() && self.entries()[i].result.is_ok() ==>
            (#[trigger] self.entries()[i]).result->Ok_0.selected.namespace(namespace)
    }
    pub fn binding(&self,port:Port)->(out:Option<&Binding<T>>)
        requires self.wf(),ensures out.is_some() ==> out.unwrap().selected.wf()
            && exists|i:int|0<=i<self.entries().len() && self.entries()[i].port==port && self.entries()[i].result==Ok(*out.unwrap()),
    {
        let mut i=0;
        while i<self.entries.len() invariant self.wf(),i<=self.entries.len(),decreases self.entries.len()-i,
        {
            if self.entries[i].port==port {
                if let Ok(binding)=&self.entries[i].result {proof {assert(self.entries()[i as int].port==port && self.entries()[i as int].result==Ok(*binding));}return Some(binding);}
            }i+=1;
        }None
    }
    pub fn observations(&self)->(out:&[Entry<T>]) ensures out@==self.entries(), {self.entries.as_slice()}
    pub(crate) fn capture<M>(episode:&NativeEpisode<Slot<T,M>>,ports:&[Port])->(out:Self)
        requires episode.wf(),ensures out.captured(*episode,ports@),
    {
        let mut entries:Vec<Entry<T>>=Vec::new();let mut i=0;
        while i<ports.len()
            invariant episode.wf(),i<=ports.len(),entries.len()==i,
                forall|j:int|0<=j<i ==> (#[trigger] entries@[j]).port==ports@[j] && entries@[j].captured(*episode),
            decreases ports.len()-i,
        {entries.push(Entry::capture(episode,ports[i]));i+=1;}
        let context=episode.setup_context();
        Self {origin:context.ticket(),work:episode.cleanup_domain(),entries}
    }
}
}
