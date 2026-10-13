//! Real effect requests, poll receipts and cleanup queues share one identity.
//! Calls move the stored iterator payload through the actual adapter, and only
//! its returned result may land. Arbitrary external effect laws remain explicit.
use crate::action_ledger::ActionTicket;
use crate::cleanup_groups::CleanupGroups;
use crate::cleanup_queue::landing::StageReport;
use crate::setup_work::SetupWork;
use crate::Binding;
use vstd::prelude::*;

verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct EffectIdentity {origin:Option<ActionTicket>,group:usize,domain:u64}
impl EffectIdentity {
    pub closed spec fn origin(&self)->Option<ActionTicket> {self.origin}
    pub closed spec fn group_id(&self)->usize {self.group}
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub fn id(&self)->(out:usize) ensures out==self.group_id(), {self.group}
    pub open spec fn matches<T>(&self,groups:&CleanupGroups<T>)->bool {
        groups.origin()==self.origin() && groups.live(self.group_id())
            && groups.domain_ids()[self.group_id()]==self.domain_id()
    }
    pub fn belongs<T>(&self,groups:&CleanupGroups<T>)->(out:bool)
        requires groups.wf(),ensures out==self.matches(groups),
    {
        groups.lifecycle_ticket()==self.origin && match groups.get(self.group) {
            Some(queue)=>queue.domain()==self.domain,None=>false,
        }
    }
}

pub struct EffectRequest<P> {identity:EffectIdentity,payload:P}
impl<P> EffectRequest<P> {
    pub fn id(&self)->(out:usize) ensures out==self.identity().group_id(), {self.identity.id()}

    pub closed spec fn identity(&self)->EffectIdentity {self.identity}
    pub closed spec fn payload(&self)->P {self.payload}
    pub fn activate<T>(self,groups:&CleanupGroups<T>)->(out:Result<EffectRun<P>,Self>)
        requires groups.wf(),
        ensures out.is_ok()==self.identity().matches(groups),
            out.is_err() ==> out->Err_0==self,
            out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.identity()==self.identity()
                && out->Ok_0.payload()==self.payload() && out->Ok_0.current().is_none()
                && out->Ok_0.next()==0 && !out->Ok_0.called(),
    {
        if !self.identity.belongs(groups) {return Err(self);}
        Ok(EffectRun {identity:self.identity,payload:self.payload,next:0,current:None,called:false})
    }
}
impl<C,P> SetupWork<C,EffectRequest<P>> {
    /// Allocate the actual cleanup group and queue its actual iterator together.
    /// Rejecting a request returns its payload without leaving an orphan group.
    pub fn enqueue_effect<T>(&mut self,groups:&mut CleanupGroups<T>,source:usize,domain:u64,committed:Vec<Binding>,payload:P)
        ->(out:Result<usize,(Vec<Binding>,P)>)
        requires old(self).wf(),old(groups).wf(),
        ensures final(self).domain_id()==old(self).domain_id(), final(self).accepts()==old(self).accepts(), final(self).is_closed()==old(self).is_closed(), final(groups).closed()==old(groups).closed(), final(self).wf(),final(groups).wf(),final(self).origin()==old(self).origin(),
            final(groups).origin()==old(groups).origin(),
            out.is_ok()==(old(self).owns(old(groups)) && old(self).origin()==old(groups).origin()
                && old(self).accepts() && old(self).next_id()<u64::MAX && old(groups).acquisition_open(source)
                && !old(groups).closed() && domain>old(groups).last_domain() && old(groups).next_id()<usize::MAX),
            out.is_err() ==> *final(self)==*old(self) && *final(groups)==*old(groups) && out->Err_0==(committed,payload),
            out.is_ok() ==> {
                let id=out->Ok_0;let request=final(self).group_requests().last().value();
                &&& final(self).group_requests().len()==old(self).group_requests().len()+1
                &&& request.payload()==payload && request.identity().group_id()==id
                &&& request.identity().matches(final(groups)) && request.identity().domain_id()==domain
                &&& id==old(groups).next_id() && final(groups).next_id()==old(groups).next_id()+1
                &&& final(groups).queues().remove(id)==old(groups).queues()
                &&& final(groups).queues()[id].protocol().stage().committed_view()==committed@
                &&& final(groups).queues()[id].slots().len()==0
            },
    {
        if !self.matches(groups) || self.lifecycle_ticket()!=groups.lifecycle_ticket()
            || !self.can_enqueue() || !groups.accepts_acquisition(source) || !groups.can_add_iterator(domain) {
            return Err((committed,payload));
        }
        let id=match groups.add_iterator(domain,committed) {Ok(id)=>id,Err(_)=>{assert(false);panic!("preflighted group");}};
        let identity=EffectIdentity {origin:self.lifecycle_ticket(),group:id,domain};
        let _accepted=self.enqueue_group(EffectRequest {identity,payload});assert(_accepted.is_ok());
        Ok(id)
    }
}

pub enum EffectOutput<T,E> {Pending,Ready(Result<Option<T>,E>)}
pub struct EffectReply<T,E> {identity:EffectIdentity,serial:u64,result:EffectOutput<T,E>}
impl<T,E> EffectReply<T,E> {
    pub closed spec fn identity(&self)->EffectIdentity {self.identity}
    pub closed spec fn serial(&self)->u64 {self.serial}
    pub closed spec fn result(&self)->EffectOutput<T,E> {self.result}
}
/// A non-cloneable owner of the actual iterator and its current poll attempt.
/// Cancellation never discards a pending attempt or its eventual inverse.
pub struct EffectRun<P> {identity:EffectIdentity,payload:P,next:u64,current:Option<u64>,called:bool}
impl<P> EffectRun<P> {
    pub closed spec fn identity(&self)->EffectIdentity {self.identity}
    pub closed spec fn payload(&self)->P {self.payload}
    pub closed spec fn next(&self)->u64 {self.next}
    pub closed spec fn current(&self)->Option<u64> {self.current}
    pub closed spec fn called(&self)->bool {self.called}
    pub open spec fn wf(&self)->bool {
        (self.current().is_some() ==> self.current().unwrap()<self.next()) && (self.called() ==> self.current().is_some())
    }
    pub fn id(&self)->(out:usize) ensures out==self.identity().group_id(), {self.identity.group}
    pub fn belongs<T>(&self,groups:&CleanupGroups<T>)->(out:bool)
        requires groups.wf(),ensures out==self.identity().matches(groups),
    {self.identity.belongs(groups)}
    pub fn get(&self)->(out:&P) ensures *out==self.payload(), {&self.payload}
    pub fn into_payload(self)->(out:P) ensures out==self.payload(), {self.payload}
    pub fn get_mut(&mut self)->(out:&mut P)
        ensures *out==old(self).payload(),final(self).payload()==*final(out),
            final(self).identity()==old(self).identity(),final(self).current()==old(self).current(),
            final(self).next()==old(self).next(),final(self).called()==old(self).called(),
            old(self).wf() ==> final(self).wf(),
    {&mut self.payload}
    pub fn admit<T>(&mut self,groups:&mut CleanupGroups<T>,target:Option<&[Binding]>)->(out:bool)
        requires old(self).wf(),old(groups).wf(),
        ensures final(groups).domain_ids()==old(groups).domain_ids(), final(groups).queues().dom()==old(groups).queues().dom(), final(self).wf(),final(groups).wf(),final(self).identity()==old(self).identity(),
            final(self).payload()==old(self).payload(),final(groups).origin()==old(groups).origin(),
            final(groups).frame(old(groups),old(self).identity().group_id()),
            out ==> old(self).identity().matches(old(groups)) && old(self).current().is_none()
                && final(self).current()==Some(old(self).next()) && final(self).next()==old(self).next()+1
                && !final(self).called() && final(groups).queues()[old(self).identity().group_id()].protocol().stage().pending(),
            !out ==> *final(self)==*old(self),
            out==(old(self).current().is_none() && old(self).next()<u64::MAX
                && old(self).identity().matches(old(groups)) && old(groups).poll_enabled(old(self).identity().group_id(),target)),
    {
        if self.current.is_some() || self.next==u64::MAX || !self.identity.belongs(groups) {return false;}
        if !groups.admit(self.identity.group,target) {return false;}
        self.current=Some(self.next);self.next+=1;true
    }
    /// The callback receives the actual stored payload and argument, not an
    /// independently selected iterator. The reply is constructed only here.
    #[allow(clippy::type_complexity)]
    pub fn call<A,T,E,F:FnOnce(P,A)->(P,EffectOutput<T,E>)>(self,argument:A,callback:F)
        ->(out:Result<(Self,EffectReply<T,E>),(Self,A,F)>)
        requires self.wf(),callback.requires((self.payload(),argument)),
        ensures out.is_ok()==(self.current().is_some() && !self.called()),
            out.is_err() ==> out->Err_0==(self,argument,callback),
            out.is_ok() ==> {
                let run=out->Ok_0.0;let reply=out->Ok_0.1;
                &&& run.wf() && run.identity()==self.identity() && run.next()==self.next()
                &&& run.current()==self.current() && run.called()
                &&& reply.identity()==self.identity() && reply.serial()==self.current().unwrap()
                &&& callback.ensures((self.payload(),argument),(run.payload(),reply.result()))
            },
    {
        if self.current.is_none() || self.called {return Err((self,argument,callback));}
        let (payload,result)=callback(self.payload,argument);
        let reply=EffectReply {identity:self.identity,serial:self.current.unwrap(),result};
        Ok((Self {identity:self.identity,payload,next:self.next,current:self.current,called:true},reply))
    }
    pub fn land<T,E>(&mut self,groups:&mut CleanupGroups<T>,reply:EffectReply<T,E>)
        ->(out:Result<Option<StageReport<E>>,EffectReply<T,E>>)
        requires old(self).wf(),old(groups).wf(),
        ensures final(groups).domain_ids()==old(groups).domain_ids(), final(groups).queues().dom()==old(groups).queues().dom(), final(self).wf(),final(groups).wf(),final(self).identity()==old(self).identity(),
            final(self).payload()==old(self).payload(),final(self).next()==old(self).next(),
            final(groups).origin()==old(groups).origin(),final(groups).frame(old(groups),old(self).identity().group_id()),
            out.is_err() ==> *final(self)==*old(self) && *final(groups)==*old(groups) && out->Err_0==reply,
            out.is_ok()==(old(self).called() && old(self).current()==Some(reply.serial())
                && reply.identity()==old(self).identity() && old(self).identity().matches(old(groups))
                && old(groups).queues()[old(self).identity().group_id()].protocol().stage().pending()),
            out.is_ok() ==> final(self).current().is_none() && !final(self).called() && match reply.result() {
                EffectOutput::Pending=>out->Ok_0.is_none() && *final(groups)==*old(groups),
                EffectOutput::Ready(result)=>out->Ok_0.is_some()
                    && !final(groups).queues()[old(self).identity().group_id()].protocol().stage().pending()
                    && out->Ok_0.unwrap().continue_iteration==(result.is_ok() && result->Ok_0.is_some()
                        && !old(groups).queues()[old(self).identity().group_id()].protocol().stage().cancellation())
                    && out->Ok_0.unwrap().error==match result {Err(error)=>Some(error),_=>None}
                    && (result.is_ok() && result->Ok_0.is_some() ==>
                        final(groups).queues()[old(self).identity().group_id()].slots()==old(groups).queues()[old(self).identity().group_id()].slots().push(result->Ok_0)),
            },
    {
        if !self.called || self.current!=Some(reply.serial) || self.identity!=reply.identity || !self.identity.belongs(groups) {
            return Err(reply);
        }
        if !groups.get(self.identity.group).unwrap().is_pending() {return Err(reply);}
        let report=match reply.result {
            EffectOutput::Pending=>None,
            EffectOutput::Ready(result)=>match groups.land_result(self.identity.group,result) {
                Ok(report)=>Some(report),Err(_)=>{assert(false);panic!("admitted stage");},
            },
        };
        self.current=None;self.called=false;Ok(report)
    }
}
}
