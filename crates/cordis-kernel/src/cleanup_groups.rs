//! Own all cleanup queues of an episode. Group removal and final sealing inspect
//! the actual queues, including issued callbacks, failures and pending stages.
//! Sealing accepts no caller-supplied drain flag, and queues cannot be mutably
//! borrowed. Only live queues occupy storage; identities are never reused.
use crate::async_completion::Completion;
use crate::cleanup_journal::{RestoreError, RestoreOutcome, RestoreTicket};
use crate::cleanup_queue::completion::{CleanupPolicy, CleanupReport};
use crate::cleanup_queue::landing::StageReport;
use crate::cleanup_queue::CleanupQueue;
use crate::Binding;
use std::collections::BTreeMap;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

verus! {

pub struct CleanupGroups<T> {
    entries:BTreeMap<usize,CleanupQueue<T>>,
    domains:BTreeMap<usize,u64>,
    next:usize,
    last_domain:u64,
    sealed:bool,
}

pub open spec fn drained<T>(queue:CleanupQueue<T>)->bool {
    queue.protocol().waiting().len()==0 && queue.protocol().selected().is_none()
        && !queue.protocol().stage().pending() && queue.protocol().stage().settled()
}

impl<T> CleanupGroups<T> {
    pub closed spec fn queues(&self)->Map<usize,CleanupQueue<T>> {self.entries@}
    pub closed spec fn domain_ids(&self)->Map<usize,u64> {self.domains@}
    pub closed spec fn next_id(&self)->usize {self.next}
    pub closed spec fn last_domain(&self)->u64 {self.last_domain}
    pub closed spec fn closed(&self)->bool {self.sealed}
    pub open spec fn live(&self,id:usize)->bool {self.queues().contains_key(id)}
    pub open spec fn wf(&self)->bool {
        &&& self.queues().dom().subset_of(self.domain_ids().dom())
        &&& forall|id:usize| #[trigger] self.domain_ids().contains_key(id) ==>
            id<self.next_id() && self.domain_ids()[id]<=self.last_domain()
        &&& forall|a:usize,b:usize| #[trigger] self.domain_ids().contains_key(a)
            && #[trigger] self.domain_ids().contains_key(b) && a!=b ==> self.domain_ids()[a]!=self.domain_ids()[b]
        &&& forall|id:usize| #[trigger] self.queues().contains_key(id) ==> self.queues()[id].wf()
            && self.queues()[id].protocol().domain_id()==self.domain_ids()[id] && !self.closed()
    }
    pub open spec fn frame(&self,prior:&Self,id:usize)->bool {
        self.next_id()==prior.next_id() && self.last_domain()==prior.last_domain() && self.closed()==prior.closed()
            && forall|other:usize| #![trigger self.queues().contains_key(other)] #![trigger self.queues()[other]] other!=id ==>
                self.queues().contains_key(other)==prior.queues().contains_key(other)
                && (self.queues().contains_key(other) ==> self.queues()[other]==prior.queues()[other])
                && self.domain_ids().contains_key(other)==prior.domain_ids().contains_key(other)
                && (self.domain_ids().contains_key(other) ==> self.domain_ids()[other]==prior.domain_ids()[other])
    }
    pub open spec fn all_drained(&self)->bool {
        forall|id:usize| #[trigger] self.queues().contains_key(id) ==> drained(self.queues()[id])
    }
    pub open spec fn any_pending(&self)->bool {
        exists|id:usize| #[trigger] self.queues().contains_key(id) && self.queues()[id].protocol().stage().pending()
    }
    pub open spec fn any_failed(&self)->bool {
        exists|id:usize| #[trigger] self.queues().contains_key(id) && self.queues()[id].protocol().failed_spec()
    }
    pub open spec fn retries_ready(&self)->bool {
        self.any_failed() && forall|id:usize| #[trigger] self.queues().contains_key(id)
            && self.queues()[id].protocol().failed_spec() ==> self.queues()[id].retry_enabled()
    }
    pub fn new(root_domain:u64)->(out:Self)
        ensures out.wf(),!out.closed(),out.queues().dom()==set![0usize],out.next_id()==1,
            out.queues()[0].slots().len()==0,out.domain_ids()==map![0usize=>root_domain],out.last_domain()==root_domain,
    {
        let mut entries=BTreeMap::new();entries.insert(0, CleanupQueue::scope(root_domain));
        let mut domains=BTreeMap::new();domains.insert(0,root_domain);
        Self {entries,domains,next:1,last_domain:root_domain,sealed:false}
    }
    pub fn contains(&self,id:usize)->(out:bool) ensures out==self.live(id),
    {self.entries.contains_key(&id)}
    /// Number of live groups, including the root until removal or sealing.
    pub fn len(&self)->(out:usize) ensures out==self.queues().len(),
    {self.entries.len()}
    /// No live groups remain; empty inverse stacks alone do not imply this.
    pub fn is_empty(&self)->(out:bool) ensures out==self.queues().is_empty(),
    {self.entries.is_empty()}
    pub fn get(&self,id:usize)->(out:Option<&CleanupQueue<T>>)
        ensures out.is_some()==self.live(id),out.is_some() ==> *out.unwrap()==self.queues()[id],
    {self.entries.get(&id)}
    fn active_ids(&self)->(out:Vec<usize>)
        ensures out@.to_set()==self.queues().dom(),out@.no_duplicates(),
    {
        let mut out=Vec::new();
        let keys=self.entries.keys();
        let ghost all=keys.remaining();
        let _count=self.entries.len();
        proof {all.unref().unique_seq_to_set();assert(all.len()==_count);}
        for key in iter: keys
            invariant all==iter.seq(),_count==all.len(),out@==iter.seq().take(iter.index()).unref(),
            decreases _count as int-out.len() as int,
        {out.push(*key);}
        assert(out@==all.unref());out
    }
    fn take(&mut self,id:usize)->(out:CleanupQueue<T>)
        requires old(self).wf(),old(self).live(id),
        ensures final(self).wf(),final(self).frame(old(self),id),
            final(self).domain_ids()==old(self).domain_ids(),final(self).queues()==old(self).queues().remove(id),
            out==old(self).queues()[id],out.wf(),
            out.protocol().domain_id()==final(self).domain_ids()[id],!final(self).closed(),
    {
        let ghost prior=*self;
        let out=self.entries.remove(&id).unwrap();
        assert(self.queues()==prior.queues().remove(id));out
    }
    fn put(&mut self,id:usize,queue:CleanupQueue<T>)
        requires old(self).wf(),!old(self).closed(),old(self).domain_ids().contains_key(id),
            !old(self).live(id),queue.wf(),queue.protocol().domain_id()==old(self).domain_ids()[id],
        ensures final(self).wf(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),
            final(self).queues()==old(self).queues().insert(id,queue),
    {
        let ghost prior=*self;
        self.entries.insert(id,queue);
        assert(self.queues()==prior.queues().insert(id,queue));
    }
    /// Domains increase just as the host's global receipt allocator does. The
    /// high-water mark rejects reuse without retaining each removed queue.
    pub fn add_iterator(&mut self,domain:u64,committed:Vec<Binding>)->(out:Result<usize,RestoreError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok()==(!old(self).closed() && domain>old(self).last_domain() && old(self).next_id()<usize::MAX),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> out->Ok_0==old(self).next_id() && final(self).next_id()==old(self).next_id()+1
                && final(self).live(out->Ok_0) && final(self).queues().remove(out->Ok_0)==old(self).queues()
                && final(self).queues()[out->Ok_0].slots().len()==0
                && final(self).queues()[out->Ok_0].protocol().stage().committed_view()==committed@
                && final(self).domain_ids()==old(self).domain_ids().insert(out->Ok_0,domain)
                && final(self).last_domain()==domain && !final(self).closed(),
    {
        if self.sealed || domain<=self.last_domain {return Err(RestoreError::InvalidState);}
        if self.next==usize::MAX {return Err(RestoreError::Capacity);}
        let id=self.next;self.next+=1;self.last_domain=domain;
        self.entries.insert(id,CleanupQueue::iterator(domain,committed));
        self.domains.insert(id,domain);
        Ok(id)
    }
    pub fn register(&mut self,id:usize,payload:T)->(out:Result<usize,T>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),out.is_ok()==old(self).live(id),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==payload,
            out.is_ok() ==> final(self).live(id)
                && out->Ok_0==old(self).queues()[id].slots().len()
                && final(self).queues()[id].slots()==old(self).queues()[id].slots().push(Some(payload)),
    {
        if !self.contains(id) {return Err(payload);}
        let mut queue=self.take(id);let token=queue.register(payload);self.put(id,queue);Ok(token)
    }
    pub fn admit(&mut self,id:usize,target:Option<&[Binding]>)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),out ==> old(self).live(id),
            final(self).live(id)==old(self).live(id),
    {
        if !self.contains(id) {return false;}
        let mut queue=self.take(id);let out=queue.admit(target);self.put(id,queue);out
    }
    pub fn cancel(&mut self,id:usize)
        requires old(self).wf(),ensures final(self).wf(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),
            final(self).live(id)==old(self).live(id),
    {
        if !self.contains(id) {return;}
        let mut queue=self.take(id);queue.cancel();self.put(id,queue);
    }
    pub fn land_result<E>(&mut self,id:usize,result:Result<Option<T>,E>)
        ->(out:Result<StageReport<E>,Result<Option<T>,E>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            out.is_ok()==(old(self).live(id) && old(self).queues()[id].protocol().stage().pending()),
            out.is_err() ==> out->Err_0==result,
            out.is_ok() && result.is_ok() && result->Ok_0.is_some() ==>
                final(self).queues()[id].slots()==old(self).queues()[id].slots().push(result->Ok_0),
            out.is_ok() ==> !final(self).queues()[id].protocol().stage().pending()
                && out->Ok_0.continue_iteration==(result.is_ok() && result->Ok_0.is_some()
                    && !old(self).queues()[id].protocol().stage().cancellation()),
    {
        if !self.contains(id) {return Err(result);}
        let mut queue=self.take(id);let out=queue.land_result(result);self.put(id,queue);out
    }
    pub fn pop(&mut self,id:usize)->(out:Result<Option<(RestoreTicket,T)>,RestoreError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            out.is_ok() && out->Ok_0.is_some() ==> old(self).live(id)
                && final(self).queues()[id].issued()
                && final(self).queues()[id].protocol().selected()==Some(out->Ok_0.unwrap().0)
                && old(self).queues()[id].slots()[out->Ok_0.unwrap().0.token as int]==Some(out->Ok_0.unwrap().1),
    {
        if !self.contains(id) {return Err(RestoreError::InvalidState);}
        let mut queue=self.take(id);let out=queue.pop();self.put(id,queue);out
    }
    pub fn complete(&mut self,id:usize,ticket:RestoreTicket,outcome:RestoreOutcome,retry:Option<T>)->(out:Result<(),Option<T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            out.is_ok()==(old(self).live(id) && old(self).queues()[id].completion_enabled(ticket,outcome,retry)),
            out.is_err() ==> out->Err_0==retry,
    {
        if !self.contains(id) {return Err(retry);}
        let mut queue=self.take(id);let out=queue.complete(ticket,outcome,retry);self.put(id,queue);out
    }
    #[allow(clippy::type_complexity)]
    pub fn complete_future<E>(&mut self,id:usize,completion:Completion<RestoreTicket,Result<(),E>>,retry:Option<T>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,T>,(Completion<RestoreTicket,Result<(),E>>,Option<T>)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            out.is_err() ==> out->Err_0==(completion,retry),
            out.is_ok() ==> old(self).live(id) && out->Ok_0.result==completion.result()
                && old(self).queues()[id].issued()
                && old(self).queues()[id].protocol().selected()==Some(completion.argument())
                && !final(self).queues()[id].issued(),
    {
        if !self.contains(id) {return Err((completion,retry));}
        let mut queue=self.take(id);let out=queue.complete_future(completion,retry,policy);self.put(id,queue);out
    }
    #[allow(clippy::type_complexity)]
    pub fn complete_failure<E>(&mut self,id:usize,ticket:RestoreTicket,error:E,retry:Option<T>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,T>,(RestoreTicket,E,Option<T>)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            out.is_err() ==> out->Err_0==(ticket,error,retry),
            out.is_ok() ==> out->Ok_0.result==Err(error) && out->Ok_0.outcome!=RestoreOutcome::Succeeded,
    {
        if !self.contains(id) {return Err((ticket,error,retry));}
        let mut queue=self.take(id);let out=queue.complete_failure(ticket,error,retry,policy);self.put(id,queue);out
    }
    pub fn retry(&mut self,id:usize)->(out:Result<RestoreTicket,RestoreError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            out.is_ok()==(old(self).live(id) && old(self).queues()[id].retry_enabled()),
            out.is_ok() ==> !final(self).queues()[id].protocol().failed_spec(),
    {
        if !self.contains(id) {return Err(RestoreError::InvalidState);}
        let mut queue=self.take(id);let out=queue.retry();self.put(id,queue);out
    }
    pub fn has_pending(&self)->(out:bool)
        requires self.wf(),ensures out==self.any_pending(),
    {
        let ids=self.active_ids();let mut i=0;
        while i<ids.len()
            invariant self.wf(),ids@.to_set()==self.queues().dom(),i<=ids.len(),
                forall|j:int| 0<=j<i ==> !self.queues()[#[trigger] ids@[j]].protocol().stage().pending(),
            decreases ids.len()-i,
        {
            assert(ids@.to_set().contains(ids@[i as int]));assert(self.live(ids@[i as int]));
            if self.entries.get(&ids[i]).unwrap().is_pending() {return true;}
            i+=1;
        }
        false
    }
    pub fn has_failed(&self)->(out:bool)
        requires self.wf(),ensures out==self.any_failed(),
    {
        let ids=self.active_ids();let mut i=0;
        while i<ids.len()
            invariant self.wf(),ids@.to_set()==self.queues().dom(),i<=ids.len(),
                forall|j:int| 0<=j<i ==> !self.queues()[#[trigger] ids@[j]].protocol().failed_spec(),
            decreases ids.len()-i,
        {
            assert(ids@.to_set().contains(ids@[i as int]));assert(self.live(ids@[i as int]));
            if self.entries.get(&ids[i]).unwrap().has_failed() {return true;}
            i+=1;
        }
        false
    }
    pub fn can_retry_all(&self)->(out:bool)
        requires self.wf(),ensures out==self.retries_ready(),
    {
        if !self.has_failed() {return false;}
        let ids=self.active_ids();let mut i=0;
        while i<ids.len()
            invariant self.wf(),self.any_failed(),ids@.to_set()==self.queues().dom(),i<=ids.len(),
                forall|j:int| 0<=j<i && self.queues()[#[trigger] ids@[j]].protocol().failed_spec() ==> self.queues()[ids@[j]].retry_enabled(),
            decreases ids.len()-i,
        {
            assert(ids@.to_set().contains(ids@[i as int]));assert(self.live(ids@[i as int]));
            let queue=self.entries.get(&ids[i]).unwrap();
            if queue.has_failed() && !queue.can_retry() {return false;}
            i+=1;
        }
        true
    }
    pub fn retry_all(&mut self)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),out==old(self).retries_ready(),
            final(self).domain_ids()==old(self).domain_ids(),final(self).closed()==old(self).closed(),
            final(self).queues().dom()==old(self).queues().dom(),
            final(self).next_id()==old(self).next_id(),final(self).last_domain()==old(self).last_domain(),
            out ==> !final(self).any_failed(),!out ==> *final(self)==*old(self),
    {
        if !self.can_retry_all() {return false;}
        let ghost prior=*self;
        let ids=self.active_ids();let mut i=0;
        while i<ids.len()
            invariant self.wf(),prior.retries_ready(),ids@.no_duplicates(),ids@.to_set()==self.queues().dom(),
                self.domain_ids()==prior.domain_ids(),self.closed()==prior.closed(),
                self.next_id()==prior.next_id(),self.last_domain()==prior.last_domain(),
                self.queues().dom()==prior.queues().dom(),i<=ids.len(),
                forall|j:int| i<=j<ids.len() ==> self.queues()[#[trigger] ids@[j]]==prior.queues()[ids@[j]],
                forall|j:int| 0<=j<i ==> !self.queues()[#[trigger] ids@[j]].protocol().failed_spec(),
            decreases ids.len()-i,
        {
            assert(ids@.to_set().contains(ids@[i as int]));assert(self.live(ids@[i as int]));
            let id=ids[i];
            if self.entries.get(&id).unwrap().has_failed() {
                assert(prior.live(id));assert(self.queues()[id].retry_enabled());
                let _result=self.retry(id);assert(_result.is_ok());
            }
            i+=1;
        }
        true
    }
    pub fn can_finish(&self,target:&[Binding])->(out:bool)
        requires self.wf(),ensures out ==> !self.any_pending() && !self.any_failed(),
    {
        let ids=self.active_ids();let mut i=0;
        while i<ids.len()
            invariant self.wf(),ids@.to_set()==self.queues().dom(),i<=ids.len(),
                forall|j:int| 0<=j<i ==> !self.queues()[#[trigger] ids@[j]].protocol().stage().pending()
                    && !self.queues()[ids@[j]].protocol().failed_spec(),
            decreases ids.len()-i,
        {
            assert(ids@.to_set().contains(ids@[i as int]));assert(self.live(ids@[i as int]));
            let id=ids[i];let queue=self.entries.get(&id).unwrap();
            if queue.is_pending() || queue.has_failed() {return false;}
            if id!=0 && !queue.can_finish(target) {return false;}
            i+=1;
        }
        true
    }
    pub fn can_seal(&self)->(out:bool)
        requires self.wf(),ensures out==self.all_drained(),
    {
        let ids=self.active_ids();let mut i=0;
        while i<ids.len()
            invariant self.wf(),ids@.to_set()==self.queues().dom(),i<=ids.len(),
                forall|j:int| 0<=j<i ==> drained(self.queues()[#[trigger] ids@[j]]),
            decreases ids.len()-i,
        {
            assert(ids@.to_set().contains(ids@[i as int]));assert(self.live(ids@[i as int]));
            let queue=self.entries.get(&ids[i]).unwrap();
            if !queue.is_empty() || queue.is_pending() || !queue.is_settled() {return false;}
            i+=1;
        }
        true
    }
    /// An admitted poll blocks sealing even while its inverse stack is empty.
    /// Failed/issued receipts also prevent removal. Only live metadata remains.
    pub fn remove(&mut self,id:usize)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).frame(old(self),id),
            out==(old(self).live(id) && drained(old(self).queues()[id])),
            out ==> final(self).queues()==old(self).queues().remove(id)
                && final(self).domain_ids()==old(self).domain_ids().remove(id)
                && !old(self).queues()[id].issued()
                && forall|j:int| 0<=j<old(self).queues()[id].slots().len() ==> #[trigger] old(self).queues()[id].slots()[j].is_none(),
            !out ==> *final(self)==*old(self),
    {
        if !self.contains(id) {return false;}
        let queue=self.entries.get(&id).unwrap();
        if !queue.is_empty() || queue.is_pending() || !queue.is_settled() {return false;}
        let _queue=self.take(id);self.domains.remove(&id);true
    }
    /// Inspect every owned queue and close admission in one exclusive operation.
    /// There is no host-supplied manifest from which a group could be omitted.
    pub fn seal(&mut self)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),out==old(self).all_drained(),out ==> final(self).closed(),
            final(self).next_id()==old(self).next_id(),final(self).last_domain()==old(self).last_domain(),
            out ==> final(self).queues()==Map::empty() && final(self).domain_ids()==Map::empty(),
            !out ==> *final(self)==*old(self),
            out ==> forall|id:usize| #[trigger] old(self).live(id) ==>
                !old(self).queues()[id].issued() && !old(self).queues()[id].protocol().stage().pending()
                && forall|j:int| 0<=j<old(self).queues()[id].slots().len() ==> #[trigger] old(self).queues()[id].slots()[j].is_none(),
    {
        if !self.can_seal() {return false;}
        let ghost prior=*self;
        proof {
            assert forall|id:usize| #[trigger] prior.live(id) implies
                !prior.queues()[id].issued() && !prior.queues()[id].protocol().stage().pending()
                && forall|j:int| 0<=j<prior.queues()[id].slots().len() ==> #[trigger] prior.queues()[id].slots()[j].is_none() by {
                let q=prior.queues()[id];assert(q.wf());assert(drained(q));q.empty_payloads();
            }
        }
        self.entries=BTreeMap::new();self.domains=BTreeMap::new();self.sealed=true;true
    }
}
}
