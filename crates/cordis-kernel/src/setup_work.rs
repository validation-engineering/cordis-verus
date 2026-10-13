//! Own admitted setup work and the real deferred Child/group requests. Taking
//! a request out for execution does not drain it: a private completion produced
//! by its actual call is required. Dropped or abandoned work remains blocking.
#[cfg(verus_keep_ghost)]
use crate::action_ledger::ActionKind;
use crate::action_ledger::ActionTicket;
use crate::cleanup_groups::CleanupGroups;
use crate::Binding;
use core::future::Future;
use std::collections::{BTreeMap, VecDeque};
#[cfg(verus_keep_ghost)]
use vstd::future::FutureAdditionalSpecFns;
use vstd::prelude::*;

verus! {

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum WorkKind { Root, Child, Group }

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct WorkTicket { domain:u64, id:u64, kind:WorkKind }
impl WorkTicket {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn request_id(&self)->u64 {self.id}
    pub closed spec fn request_kind(&self)->WorkKind {self.kind}
    #[verifier::when_used_as_spec(domain_id)]
    pub fn domain(&self)->(out:u64) ensures out==self.domain_id(), {self.domain}
    #[verifier::when_used_as_spec(request_id)]
    pub fn id(&self)->(out:u64) ensures out==self.request_id(), {self.id}
    #[verifier::when_used_as_spec(request_kind)]
    pub fn kind(&self)->(out:WorkKind) ensures out==self.request_kind(), {self.kind}
}

/// The payload and receipt identity cannot be independently substituted.
pub struct WorkItem<T> { ticket:WorkTicket, payload:T }
pub struct WorkReceipt<R> { ticket:WorkTicket, result:R }
pub struct PendingWork<F:Future> { ticket:WorkTicket, future:F }

/// Actual setup factory output. Both branches retain the issued root identity.
pub enum RootOutput<R,F> { Ready(R), Pending(F) }
pub enum RootDispatch<R,F:Future> { Ready(WorkReceipt<R>), Pending(PendingWork<F>) }
impl<R,F:Future<Output=R>> WorkReceipt<RootOutput<R,F>> {
    pub fn dispatch(self)->(out:RootDispatch<R,F>)
        ensures match self.value() {
            RootOutput::Ready(result)=>out is Ready && out->Ready_0.origin()==self.origin() && out->Ready_0.value()==result,
            RootOutput::Pending(future)=>out is Pending && out->Pending_0.origin()==self.origin() && out->Pending_0.pending()==future,
        },
    {
        match self.result {
            RootOutput::Ready(result)=>RootDispatch::Ready(WorkReceipt {ticket:self.ticket,result}),
            RootOutput::Pending(future)=>RootDispatch::Pending(PendingWork {ticket:self.ticket,future}),
        }
    }
}


impl<T> WorkItem<T> {
    pub closed spec fn origin(&self)->WorkTicket {self.ticket}
    pub closed spec fn value(&self)->T {self.payload}
    pub fn ticket(&self)->(out:WorkTicket) ensures out==self.origin(), {self.ticket}
    pub fn run<C:FnOnce(T)->R,R>(self,callback:C)->(out:WorkReceipt<R>)
        requires callback.requires((self.value(),)),
        ensures out.origin()==self.origin(),callback.ensures((self.value(),),out.value()),
    {
        let result=callback(self.payload);
        WorkReceipt {ticket:self.ticket,result}
    }
    pub fn start<C:FnOnce(T)->F,F:Future>(self,callback:C)->(out:PendingWork<F>)
        requires callback.requires((self.value(),)),
        ensures out.origin()==self.origin(),callback.ensures((self.value(),),out.pending()),
    {
        let future=callback(self.payload);
        PendingWork {ticket:self.ticket,future}
    }
}
impl<R> WorkReceipt<R> {
    pub closed spec fn origin(&self)->WorkTicket {self.ticket}
    pub closed spec fn value(&self)->R {self.result}
}
impl<F:Future> PendingWork<F> {
    pub closed spec fn origin(&self)->WorkTicket {self.ticket}
    pub closed spec fn pending(&self)->F {self.future}
    pub async fn complete(self)->(out:WorkReceipt<F::Output>)
        ensures out.origin()==self.origin(),self.pending().awaited(),out.value()==self.pending()@,
    {
        let result=self.future.await;
        WorkReceipt {ticket:self.ticket,result}
    }
}

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum RootStatus { Unissued, Queued, Running, Settled, Abandoned }

pub struct SetupWork<C,G> {
    domain:u64,
    lifecycle:Option<ActionTicket>,
    next:u64,
    root:RootStatus,
    root_failed:bool,
    children:VecDeque<WorkItem<C>>,
    groups:VecDeque<WorkItem<G>>,
    issued:BTreeMap<u64,WorkKind>,
    accepting:bool,
    closed:bool,
}

impl<C,G> SetupWork<C,G> {
    pub closed spec fn origin(&self)->Option<ActionTicket> {self.lifecycle}
    pub fn lifecycle_ticket(&self)->(out:Option<ActionTicket>) ensures out==self.origin(), {self.lifecycle}
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn next_id(&self)->u64 {self.next}
    pub closed spec fn root_status(&self)->RootStatus {self.root}
    pub closed spec fn failed(&self)->bool {self.root_failed}
    pub closed spec fn child_requests(&self)->Seq<WorkItem<C>> {self.children@}
    pub closed spec fn group_requests(&self)->Seq<WorkItem<G>> {self.groups@}
    pub closed spec fn outstanding(&self)->Map<u64,WorkKind> {self.issued@}
    pub closed spec fn accepts(&self)->bool {self.accepting}
    pub closed spec fn is_closed(&self)->bool {self.closed}
    pub open spec fn idle(&self)->bool {
        self.root_status()==RootStatus::Settled && self.child_requests().len()==0
            && self.group_requests().len()==0 && self.outstanding().len()==0
    }
    pub open spec fn wf(&self)->bool {
        &&& self.next_id()>0
        &&& self.origin().is_some() ==> self.origin().unwrap().kind==ActionKind::Setup
        &&& self.is_closed() ==> self.idle() && !self.accepts()
        &&& forall|id:u64| #[trigger] self.outstanding().contains_key(id) ==> 0<id<self.next_id()
            && self.outstanding()[id]!=WorkKind::Root
        &&& forall|i:int| 0<=i<self.child_requests().len() ==> {
            let ticket=#[trigger] self.child_requests()[i].origin();
            ticket.domain()==self.domain_id() && 0<ticket.id()<self.next_id() && ticket.kind()==WorkKind::Child
        }
        &&& forall|i:int| 0<=i<self.group_requests().len() ==> {
            let ticket=#[trigger] self.group_requests()[i].origin();
            ticket.domain()==self.domain_id() && 0<ticket.id()<self.next_id() && ticket.kind()==WorkKind::Group
        }
    }
    pub open spec fn queued_unchanged(&self,prior:&Self)->bool {
        self.child_requests()==prior.child_requests() && self.group_requests()==prior.group_requests()
            && self.next_id()==prior.next_id() && self.outstanding()==prior.outstanding()
            && self.domain_id()==prior.domain_id() && self.origin()==prior.origin()
    }
    pub fn new(domain:u64)->(out:Self)
        ensures out.wf(),out.origin().is_none(),out.domain_id()==domain,out.root_status()==RootStatus::Unissued,
            !out.failed(),out.child_requests().len()==0,out.group_requests().len()==0,
            out.outstanding().len()==0,out.next_id()==1,out.accepts(),!out.is_closed(),
    {Self {domain,lifecycle:None,next:1,root:RootStatus::Unissued,root_failed:false,children:VecDeque::new(),
        groups:VecDeque::new(),issued:BTreeMap::new(),accepting:true,closed:false}}

    /// Only verified kernel admission constructs a lifecycle-bound work owner.
    pub(crate) fn for_lifecycle(ticket:ActionTicket,domain:u64)->(out:Self)
        requires ticket.kind==ActionKind::Setup,
        ensures out.wf(),out.origin()==Some(ticket),out.domain_id()==domain,
            out.root_status()==RootStatus::Unissued,!out.failed(),out.child_requests().len()==0,out.group_requests().len()==0,
            out.outstanding().len()==0,out.next_id()==1,out.accepts(),!out.is_closed(),
    {
        let mut out=Self::new(domain);out.lifecycle=Some(ticket);out
    }
    pub fn root(&self)->(out:RootStatus) ensures out==self.root_status(), {self.root}
    pub fn child_count(&self)->(out:usize) ensures out==self.child_requests().len(), {self.children.len()}
    pub fn group_count(&self)->(out:usize) ensures out==self.group_requests().len(), {self.groups.len()}
    pub fn pending_count(&self)->(out:usize) ensures out==self.outstanding().len(), {self.issued.len()}

    /// Close acquisition, retaining every already admitted request and inverse.
    pub fn withdraw(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),!final(self).accepts(),final(self).queued_unchanged(old(self)),
            final(self).root_status()==old(self).root_status(),final(self).failed()==old(self).failed(),
            final(self).is_closed()==old(self).is_closed(),
    {self.accepting=false;}

    /// Issue exactly one root invocation, with its actual argument owned by the
    /// item. A callback failure still has to land; it never resets the admission.
    pub fn issue_root<A>(&mut self,argument:A)->(out:Result<WorkItem<A>,A>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),final(self).queued_unchanged(old(self)),
            out.is_ok()==(old(self).root_status()==RootStatus::Unissued && !old(self).is_closed()),
            out.is_ok() ==> out->Ok_0.value()==argument && out->Ok_0.origin().domain()==old(self).domain_id() && out->Ok_0.origin().id()==0 && out->Ok_0.origin().kind()==WorkKind::Root
                && final(self).root_status()==RootStatus::Queued,
            out.is_err() ==> out->Err_0==argument && *final(self)==*old(self),
    {
        if self.root!=RootStatus::Unissued || self.closed {return Err(argument);}
        self.root=RootStatus::Queued;
        Ok(WorkItem {ticket:WorkTicket {domain:self.domain,id:0,kind:WorkKind::Root},payload:argument})
    }
    fn root_ticket(&self,ticket:WorkTicket)->(out:bool)
        ensures out==(ticket.domain()==self.domain_id() && ticket.id()==0 && ticket.kind()==WorkKind::Root),
    {ticket.domain()==self.domain && ticket.id()==0 && ticket.kind()==WorkKind::Root}
    pub fn start_root(&mut self,ticket:WorkTicket)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),final(self).queued_unchanged(old(self)),
            out==(ticket.domain()==old(self).domain_id() && ticket.id()==0 && ticket.kind()==WorkKind::Root
                && (old(self).root_status()==RootStatus::Queued || old(self).root_status()==RootStatus::Running)),
            out ==> final(self).root_status()==RootStatus::Running,
            !out ==> *final(self)==*old(self),
    {
        if !self.root_ticket(ticket) || (self.root!=RootStatus::Queued && self.root!=RootStatus::Running) {return false;}
        self.root=RootStatus::Running;true
    }
    /// Only work whose first poll has not begun may be discarded on withdrawal.
    /// This is cancellation, never successful initialization.
    pub fn cancel_queued_root(&mut self,ticket:WorkTicket)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),final(self).queued_unchanged(old(self)),
            out==(ticket.domain()==old(self).domain_id() && ticket.id()==0 && ticket.kind()==WorkKind::Root
                && old(self).root_status()==RootStatus::Queued && !old(self).accepts()),
            out ==> final(self).root_status()==RootStatus::Settled && final(self).failed(),
            !out ==> *final(self)==*old(self),
    {
        if !self.root_ticket(ticket) || self.root!=RootStatus::Queued || self.accepting {return false;}
        self.root=RootStatus::Settled;self.root_failed=true;true
    }
    pub fn complete_root<E>(&mut self,receipt:WorkReceipt<Result<(),E>>)->(out:Result<Result<(),E>,WorkReceipt<Result<(),E>>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),final(self).queued_unchanged(old(self)),
            out.is_ok()==(receipt.origin().domain()==old(self).domain_id() && receipt.origin().id()==0 && receipt.origin().kind()==WorkKind::Root
                && (old(self).root_status()==RootStatus::Queued || old(self).root_status()==RootStatus::Running)),
            out.is_ok() ==> out->Ok_0==receipt.value() && final(self).root_status()==RootStatus::Settled
                && final(self).failed()==receipt.value().is_err(),
            out.is_err() ==> out->Err_0==receipt && *final(self)==*old(self),
    {
        if !self.root_ticket(receipt.ticket) || (self.root!=RootStatus::Queued && self.root!=RootStatus::Running) {return Err(receipt);}
        self.root=RootStatus::Settled;self.root_failed=receipt.result.is_err();Ok(receipt.result)
    }
    /// A caught panic records failure only. No success receipt can be fabricated
    /// through this path. The ticket still has to match the issued root.
    pub fn fail_root<E>(&mut self,ticket:WorkTicket,error:E)->(out:Result<E,E>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),final(self).queued_unchanged(old(self)),
            out.is_ok() ==> final(self).root_status()==RootStatus::Settled && final(self).failed() && out->Ok_0==error,
            out.is_err() ==> out->Err_0==error && *final(self)==*old(self),
    {
        if !self.root_ticket(ticket) || (self.root!=RootStatus::Queued && self.root!=RootStatus::Running) {return Err(error);}
        self.root=RootStatus::Settled;self.root_failed=true;Ok(error)
    }
    /// Dropping a running root is not completion. It permanently blocks drain.
    pub fn abandon_root(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),final(self).queued_unchanged(old(self)),
            old(self).root_status()!=RootStatus::Settled ==> final(self).root_status()==RootStatus::Abandoned && !final(self).idle(),
    {
        self.accepting=false;
        if self.root!=RootStatus::Settled {self.root=RootStatus::Abandoned;self.root_failed=true;}
    }
    pub fn can_enqueue(&self)->(out:bool)
        ensures out==(self.accepts() && self.next_id()<u64::MAX),
    {self.accepting && self.next<u64::MAX}
    pub open spec fn owns<T>(&self,cleanups:&CleanupGroups<T>)->bool {
        cleanups.live(0) && cleanups.domain_ids()[0]==self.domain_id()
    }
    pub fn matches<T>(&self,cleanups:&CleanupGroups<T>)->(out:bool)
        requires cleanups.wf(),ensures out==self.owns(cleanups),
    {
        match cleanups.get(0) {Some(queue)=>queue.domain()==self.domain,None=>false}
    }
    /// Queue the real child request and retain its actual inverse atomically.
    /// Rejection returns both payloads for disposal outside the host mutex.
    pub fn enqueue_owned_child<T>(&mut self,cleanups:&mut CleanupGroups<T>,group:usize,payload:C,inverse:T)
        ->(out:Result<usize,(C,T)>)
        requires old(self).wf(),old(cleanups).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),final(cleanups).wf(),
            out.is_err() ==> out->Err_0==(payload,inverse) && *final(self)==*old(self) && *final(cleanups)==*old(cleanups),
            out.is_ok() ==> old(self).owns(old(cleanups)) && old(self).accepts()
                && final(self).child_requests().last().value()==payload
                && out->Ok_0==old(cleanups).queues()[group].slots().len()
                && final(cleanups).queues()[group].slots()==old(cleanups).queues()[group].slots().push(Some(inverse)),
    {
        if !self.matches(cleanups) || !self.can_enqueue() || !cleanups.contains(group) {return Err((payload,inverse));}
        let token=match cleanups.register(group,inverse) {Ok(token)=>token,Err(_)=>{assert(false);panic!("live group");}};
        let _accepted=self.enqueue_child(payload);assert(_accepted.is_ok());Ok(token)
    }
    pub fn enqueue_child(&mut self,payload:C)->(out:Result<(),C>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),out.is_ok()==(old(self).accepts() && old(self).next_id()<u64::MAX),
            out.is_ok() ==> final(self).next_id()==old(self).next_id()+1
                && final(self).child_requests().len()==old(self).child_requests().len()+1
                && final(self).child_requests().take(old(self).child_requests().len() as int)==old(self).child_requests()
                && final(self).child_requests().last().value()==payload
                && final(self).child_requests().last().origin().id()==old(self).next_id(),
            out.is_err() ==> out->Err_0==payload && *final(self)==*old(self),
            final(self).group_requests()==old(self).group_requests(),final(self).outstanding()==old(self).outstanding(),
            final(self).root_status()==old(self).root_status(),final(self).domain_id()==old(self).domain_id(),
    {
        if !self.accepting || self.next==u64::MAX {return Err(payload);}
        let ticket=WorkTicket {domain:self.domain,id:self.next,kind:WorkKind::Child};self.next+=1;
        self.children.push_back(WorkItem {ticket,payload});Ok(())
    }
    pub fn enqueue_group(&mut self,payload:G)->(out:Result<(),G>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),out.is_ok()==(old(self).accepts() && old(self).next_id()<u64::MAX),
            out.is_ok() ==> final(self).next_id()==old(self).next_id()+1
                && final(self).group_requests().len()==old(self).group_requests().len()+1
                && final(self).group_requests().take(old(self).group_requests().len() as int)==old(self).group_requests()
                && final(self).group_requests().last().value()==payload
                && final(self).group_requests().last().origin().id()==old(self).next_id(),
            out.is_err() ==> out->Err_0==payload && *final(self)==*old(self),
            final(self).child_requests()==old(self).child_requests(),final(self).outstanding()==old(self).outstanding(),
            final(self).root_status()==old(self).root_status(),final(self).domain_id()==old(self).domain_id(),
    {
        if !self.accepting || self.next==u64::MAX {return Err(payload);}
        let ticket=WorkTicket {domain:self.domain,id:self.next,kind:WorkKind::Group};self.next+=1;
        self.groups.push_back(WorkItem {ticket,payload});Ok(())
    }
    // The pinned Verus VecDeque specification covers len, not is_empty.
    #[allow(clippy::len_zero)]
    pub fn take_child(&mut self)->(out:Option<WorkItem<C>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),out.is_some() ==> out.unwrap()==old(self).child_requests().first()
            && !old(self).outstanding().contains_key(out.unwrap().origin().id())
            && final(self).outstanding()==old(self).outstanding().insert(out.unwrap().origin().id(),WorkKind::Child)
            && final(self).child_requests()==old(self).child_requests().skip(1),
            out.is_none() ==> *final(self)==*old(self),
            final(self).root_status()==old(self).root_status(),final(self).group_requests()==old(self).group_requests(),
            final(self).domain_id()==old(self).domain_id(),
    {
        if self.children.len()==0 {return None;}
        let ticket=self.children[0].ticket;
        if self.issued.contains_key(&ticket.id()) {return None;}
        let item=self.children.pop_front().unwrap();self.issued.insert(ticket.id(),WorkKind::Child);Some(item)
    }
    // The pinned Verus VecDeque specification covers len, not is_empty.
    #[allow(clippy::len_zero)]
    pub fn take_group(&mut self)->(out:Option<WorkItem<G>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),out.is_some() ==> out.unwrap()==old(self).group_requests().first()
            && !old(self).outstanding().contains_key(out.unwrap().origin().id())
            && final(self).outstanding()==old(self).outstanding().insert(out.unwrap().origin().id(),WorkKind::Group)
            && final(self).group_requests()==old(self).group_requests().skip(1),
            out.is_none() ==> *final(self)==*old(self),
            final(self).root_status()==old(self).root_status(),final(self).child_requests()==old(self).child_requests(),
            final(self).domain_id()==old(self).domain_id(),
    {
        if self.groups.len()==0 {return None;}
        let ticket=self.groups[0].ticket;
        if self.issued.contains_key(&ticket.id()) {return None;}
        let item=self.groups.pop_front().unwrap();self.issued.insert(ticket.id(),WorkKind::Group);Some(item)
    }
    pub fn complete_request<R>(&mut self,receipt:WorkReceipt<R>)->(out:Result<R,WorkReceipt<R>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),out.is_ok()==(receipt.origin().domain()==old(self).domain_id()
            && old(self).outstanding().contains_key(receipt.origin().id())
            && old(self).outstanding()[receipt.origin().id()]==receipt.origin().kind()),
            out.is_ok() ==> out->Ok_0==receipt.value()
                && final(self).outstanding()==old(self).outstanding().remove(receipt.origin().id()),
            out.is_err() ==> out->Err_0==receipt && *final(self)==*old(self),
            final(self).child_requests()==old(self).child_requests(),final(self).group_requests()==old(self).group_requests(),
            final(self).root_status()==old(self).root_status(),final(self).domain_id()==old(self).domain_id(),
    {
        let ticket=receipt.ticket;
        if ticket.domain()!=self.domain || self.issued.get(&ticket.id())!=Some(&ticket.kind()) {return Err(receipt);}
        self.issued.remove(&ticket.id());Ok(receipt.result)
    }
    // The pinned Verus VecDeque specification covers len, not is_empty.
    #[allow(clippy::len_zero)]
    pub fn is_idle(&self)->(out:bool) ensures out==self.idle(),
    {self.root==RootStatus::Settled && self.children.len()==0 && self.groups.len()==0 && self.issued.is_empty()}
    pub fn can_finish<T>(&self,cleanups:&CleanupGroups<T>,target:&[Binding])->(out:bool)
        requires self.wf(),cleanups.wf(),
        ensures out ==> self.owns(cleanups) && self.idle() && !self.failed() && self.accepts() && !self.is_closed()
            && !cleanups.any_pending() && !cleanups.any_failed(),
    {
        self.matches(cleanups) && self.is_idle() && !self.root_failed && self.accepting && !self.closed && cleanups.can_finish(target)
    }
    /// The real root/request owner and every cleanup queue participate. An empty
    /// dispatch queue cannot hide work already handed to a host or a Future.
    pub fn seal<T>(&mut self,cleanups:&mut CleanupGroups<T>)->(out:bool)
        requires old(self).wf(),old(cleanups).wf(),
        ensures final(self).wf(),final(self).origin()==old(self).origin(),final(cleanups).wf(),
            out==(old(self).owns(old(cleanups)) && old(self).idle() && old(cleanups).all_drained()),
            final(cleanups).drained_failure()==old(cleanups).drained_failure(),
            out ==> final(self).is_closed() && final(cleanups).closed() && old(self).outstanding().len()==0,
            !out ==> *final(self)==*old(self) && *final(cleanups)==*old(cleanups),
    {
        if !self.matches(cleanups) || !self.is_idle() {return false;}
        if !cleanups.seal() {return false;}
        self.accepting=false;self.closed=true;true
    }
}
}
