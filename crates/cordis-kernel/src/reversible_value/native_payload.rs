//! Retained typed native targets with checked owner admission and atomic landing.
//! Payload identity is carried by the real selected service handle, not by a
//! comparison of service names or equality on arbitrary user values.
use super::{
    cursor::Owner,
    payload::{Capture as PayloadCapture, SharedPayload},
    slot::ServiceSlot,
};
#[cfg(verus_keep_ghost)]
use crate::cleanup_groups::payload::selected;
use crate::cleanup_groups::payload::Admission;
use crate::execution::Execution;
use crate::lifecycle_state::{registration::shared_child::ChildCleanup, services::NativeEpisode};
use crate::versioned_value::ReplaceError;
use crate::Port;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
#[derive(Debug)]
pub enum CaptureError {Closed,NoNative,Read(crate::lifecycle_state::services::NativeReadError),Scalar,Retired}
pub type Landing<T,M> = Result<(Admission<T>,Capture<T,M>),(ReplaceError,Arc<T>,Ghost<Option<super::payload::restoration::ForwardRejection<T>>>)>;
#[allow(dead_code)]
pub struct Capture<T:?Sized,M> {
    payload:PayloadCapture<T>,retained:Arc<ServiceSlot<SharedPayload<T>,M>>,owner:Owner,port:Port,provider:usize,
    episode:Ghost<NativeEpisode<ServiceSlot<SharedPayload<T>,M>>>,
}
impl<T:?Sized,M> Capture<T,M> {
    pub closed spec fn payload(&self)->PayloadCapture<T> {self.payload}
    pub closed spec fn retained(&self)->Arc<ServiceSlot<SharedPayload<T>,M>> {self.retained}
    pub closed spec fn owner(&self)->Owner {self.owner}
    pub closed spec fn episode(&self)->NativeEpisode<ServiceSlot<SharedPayload<T>,M>> {self.episode@}
    pub closed spec fn provider_spec(&self)->usize {self.provider}
    pub fn provider(&self)->(out:usize) ensures out==self.provider_spec(), {self.provider}
    pub closed spec fn port_spec(&self)->Port {self.port}
    pub closed spec fn wf(&self)->bool {
        self.episode().wf() && self.payload().wf() && self.retained().opaque_spec()==Some(self.payload().owner())
            && selected(self.episode(),self.port_spec(),self.payload().owner())
            && self.episode().selects_value(self.provider_spec(),self.port_spec(),self.retained())
    }
    pub proof fn provenance(&self)
        requires self.wf(),
        ensures self.payload().wf(),self.episode().wf(),self.retained().opaque_spec()==Some(self.payload().owner()),
            self.episode().selects_value(self.provider_spec(),self.port_spec(),self.retained()),
            selected(self.episode(),self.port_spec(),self.payload().owner()),
    {}
    pub fn observation(&self)->(out:&PayloadCapture<T>) requires self.wf(),ensures *out==self.payload(),out.wf(), {&self.payload}
    pub fn port(&self)->(out:Port) ensures out==self.port_spec(), {self.port}
    pub open spec fn admitted<C,G,A,R,X>(&self,execution:&super::managed::Owner<C,G,A,R,T,M,X>,id:usize)->bool {
        execution.work_state().accepts() && execution.cleanup_state().acquisition_open(id) && self.owner().matches(execution,id)
    }
    /// A replaced publication cannot redirect this already selected target.
    /// Each success yields a new checked capture for this same retained object.
    pub fn land<C,G,A,R,X>(&self,execution:&mut super::managed::Owner<C,G,A,R,T,M,X>,id:usize,value:Arc<T>)->(out:Landing<T,M>)
        requires self.wf(),old(execution).wf(),
        ensures self.payload().revision_spec() as int+self.payload().observation().state().depth as int+2<=u64::MAX
                ==> !(out.is_err() && out->Err_0.0==ReplaceError::Capacity),
            final(execution).wf(),final(execution).work_state()==old(execution).work_state(),
            final(execution).value_state()==old(execution).value_state(),final(execution).capture()==old(execution).capture(),
            final(execution).execution_journal()==old(execution).execution_journal(),
            final(execution).cleanup_state().link()==old(execution).cleanup_state().link(),
            final(execution).cleanup_state().frame(&old(execution).cleanup_state(),id),
            out.is_err() ==> *final(execution)==*old(execution) && out->Err_0.1==value,
            !self.admitted(old(execution),id) ==> out.is_err() && out->Err_0.0==ReplaceError::Closed && out->Err_0.2@.is_none(),
            self.admitted(old(execution),id) && out.is_err() ==> out->Err_0.2@.is_some()
                && out->Err_0.2@.unwrap().owner()==self.payload().owner() && out->Err_0.2@.unwrap().explains(out->Err_0.0),
            out.is_ok() ==> self.admitted(old(execution),id) && final(execution).cleanup_state().live(id) && out->Ok_0.1.wf()
                && out->Ok_0.1.owner()==self.owner() && out->Ok_0.1.episode()==self.episode() && out->Ok_0.1.port_spec()==self.port_spec()
                && out->Ok_0.1.provider_spec()==self.provider_spec() && out->Ok_0.1.retained()==self.retained() && out->Ok_0.1.payload().observes(out->Ok_0.0.inverse().after())
                && out->Ok_0.0.inverse().wf() && out->Ok_0.0.witnessed()
                && out->Ok_0.0.inverse().owner()==self.payload().owner() && out->Ok_0.0.inverse().after().value==value
                && out->Ok_0.0.inverse().before().state()==self.payload().observation().state()
                && out->Ok_0.0.inverse().before().revision==self.payload().revision_spec()
                && out->Ok_0.0.token_spec()==old(execution).cleanup_state().queues()[id].slots().len()
                && out->Ok_0.0.queued(final(execution).cleanup_state().queues()[id],self.retained())
                && super::joint::groups::registration(out->Ok_0.0.registration_receipt(),final(execution).cleanup_state().link(),id)
                && final(execution).cleanup_state().queues()[id].slots().take(out->Ok_0.0.token_spec() as int)==old(execution).cleanup_state().queues()[id].slots(),
    {
        if !execution.accepts_acquisition(id) || !self.owner.check(execution,id) {return Err((ReplaceError::Closed,value,Ghost(None)));}
        let tracked empty=Map::tracked_empty();
        match execution.apply_payload_captured_following(id,self.payload.retained_owner(),Some(&self.payload),value,self.retained.clone(),Tracked(&empty)) {
            Ok((admission,payload))=>{
                proof {admission.inverse().provenance();}
                let next=Self {payload,retained:self.retained.clone(),owner:self.owner,port:self.port,provider:self.provider,episode:self.episode};
                assert(next.wf());
                Ok((admission,next))
            },
            Err((error,value,_retained,rejection))=>Err((error,value,rejection)),
        }
    }
}
impl<C,G,A,R,T:?Sized,M,X> Execution<ServiceSlot<SharedPayload<T>,M>,C,G,ChildCleanup<crate::cleanup_groups::payload::Cleanup<A,R,Arc<ServiceSlot<SharedPayload<T>,M>>,T>,X>> {
    pub fn capture_native_payload(&self,id:usize,port:Port)->(out:Result<Capture<T,M>,CaptureError>)
        requires self.wf(),
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.admitted(self,id)
            && self.value_state()==Some(out->Ok_0.episode()) && out->Ok_0.port_spec()==port,
    {
        if !self.accepts_acquisition(id) {return Err(CaptureError::Closed);}
        let native=match self.native() {Some(native)=>native,None=>return Err(CaptureError::NoNative)};
        let (_provider,slot)=match native.read(port) {Ok(pair)=>pair,Err(error)=>return Err(CaptureError::Read(error))};
        let value=match slot.opaque() {Some(value)=>value,None=>return Err(CaptureError::Scalar)};
        let payload=match value.capture() {Some(payload)=>payload,None=>return Err(CaptureError::Retired)};
        proof {assert(selected(*native,port,payload.owner())) by {
            if !native.provisions().contains(port) {assert(native.bindings().contains(crate::Binding {provider:_provider,key:port.key,realm:port.realm}));}
        }}
        let owner=Owner::capture(self,id);
        Ok(Capture {payload,retained:slot.clone(),owner,port,provider:_provider,episode:Ghost(*native)})
    }
}
}
