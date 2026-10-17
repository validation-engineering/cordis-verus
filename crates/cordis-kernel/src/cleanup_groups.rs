//! Own all cleanup queues of an episode. Group removal and final sealing inspect
//! the actual queues, including issued callbacks, failures and pending stages.
//! Sealing accepts no caller-supplied drain flag, and queues cannot be mutably
//! borrowed. Only live queues occupy storage; identities are never reused.
#[cfg(verus_keep_ghost)]
use crate::action_ledger::ActionKind;
use crate::action_ledger::ActionTicket;
use crate::async_completion::Completion;
use crate::cleanup_journal::{RestoreError, RestoreOutcome, RestoreTicket};
use crate::cleanup_queue::completion::{CleanupPolicy, CleanupReport};
use crate::cleanup_queue::landing::StageReport;
use crate::cleanup_queue::CleanupQueue;
use crate::reversible_value::joint::groups::{Event as GroupEvent, State as GroupState};
use crate::reversible_value::joint::{self, Journal, Member};
use crate::Binding;
use std::collections::BTreeMap;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

verus! {
#[derive(Copy,Clone,PartialEq,Eq,Structural)]
enum MembershipAction {Add,Remove,ConsumedFailure}

pub struct CleanupGroups<T> {
    entries:BTreeMap<usize,CleanupQueue<T>>,
    domains:BTreeMap<usize,u64>,
    next:usize,
    last_domain:u64,
    sealed:bool,
    consumed_failure:bool,
    lifecycle:Option<ActionTicket>,
    execution:Option<Journal>,
    membership:Option<Member>,
}

pub open spec fn drained<T>(queue:CleanupQueue<T>)->bool {
    queue.protocol().waiting().len()==0 && queue.protocol().selected().is_none()
        && !queue.protocol().stage().pending() && queue.protocol().stage().settled()
}

impl<T> CleanupGroups<T> {
    pub closed spec fn execution_journal(&self)->Option<Journal> {self.execution}
    pub open spec fn linked(&self,queue:CleanupQueue<T>)->bool {
        queue.link().is_some()==self.execution_journal().is_some()
            && (queue.link().is_some() ==> queue.link().unwrap().0==self.execution_journal().unwrap())
    }
    pub closed spec fn origin(&self)->Option<ActionTicket> {self.lifecycle}
    pub fn lifecycle_ticket(&self)->(out:Option<ActionTicket>) ensures out==self.origin(), {self.lifecycle}
    pub closed spec fn queues(&self)->Map<usize,CleanupQueue<T>> {self.entries@}
    pub closed spec fn domain_ids(&self)->Map<usize,u64> {self.domains@}
    pub closed spec fn next_id(&self)->usize {self.next}
    pub closed spec fn last_domain(&self)->u64 {self.last_domain}
    pub closed spec fn closed(&self)->bool {self.sealed}
    /// Sticky evidence that an accepted cleanup was consumed after failure.
    /// Removing a completed group must not erase this distinction.
    pub closed spec fn drained_failure(&self)->bool {self.consumed_failure}
    pub fn has_consumed_failure(&self)->(out:bool) ensures out==self.drained_failure(),
    {self.consumed_failure}
    pub open spec fn live(&self,id:usize)->bool {self.queues().contains_key(id)}
    pub open spec fn storage_wf(&self)->bool {
        &&& self.origin().is_some() ==> self.origin().unwrap().kind==ActionKind::Setup
        &&& self.queues().dom().subset_of(self.domain_ids().dom())
        &&& forall|id:usize| #[trigger] self.domain_ids().contains_key(id) ==>
            id<self.next_id() && self.domain_ids()[id]<=self.last_domain()
        &&& forall|a:usize,b:usize| #[trigger] self.domain_ids().contains_key(a)
            && #[trigger] self.domain_ids().contains_key(b) && a!=b ==> self.domain_ids()[a]!=self.domain_ids()[b]
        &&& forall|id:usize| #[trigger] self.queues().contains_key(id) ==> self.queues()[id].wf()
            && self.queues()[id].protocol().domain_id()==self.domain_ids()[id] && !self.closed() && self.linked(self.queues()[id])
    }
    pub open spec fn entry(queue:CleanupQueue<T>)->(nat,u64) {
        (match queue.link() {Some((_,key))=>key,None=>0nat},queue.protocol().domain_id())
    }
    pub open spec fn members(queues:Map<usize,CleanupQueue<T>>)->Map<usize,(nat,u64)> {
        Map::new(queues.dom(),|id:usize|Self::entry(queues[id]))
    }
    proof fn members_insert(queues:Map<usize,CleanupQueue<T>>,id:usize,queue:CleanupQueue<T>)
        ensures Self::members(queues.insert(id,queue))==Self::members(queues).insert(id,Self::entry(queue)),
    {assert(Self::members(queues.insert(id,queue)) =~= Self::members(queues).insert(id,Self::entry(queue)));}
    proof fn members_remove(queues:Map<usize,CleanupQueue<T>>,id:usize)
        ensures Self::members(queues.remove(id))==Self::members(queues).remove(id),
    {assert(Self::members(queues.remove(id)) =~= Self::members(queues).remove(id));}
    pub open spec fn observation(&self)->GroupState {
        GroupState {origin:self.origin(),queues:Self::members(self.queues()),next:self.next_id(),last_domain:self.last_domain(),
            sealed:self.closed(),consumed_failure:self.drained_failure()}
    }
    pub closed spec fn link(&self)->Option<(Journal,nat)> {
        match self.membership {Some(member)=>Some((member.journal(),member.key())),None=>None}
    }
    pub closed spec fn membership_trace(&self)->Seq<joint::Frame> {
        match self.membership {Some(member)=>member.events(),None=>Seq::empty()}
    }
    pub closed spec fn traces(&self,state:GroupState)->bool {
        self.membership.is_some()==self.execution.is_some() && (self.membership.is_some() ==> {
            let member=self.membership.unwrap();member.wf() && member.journal()==self.execution.unwrap()
                && member.record()==(joint::Record::Groups {state})
        })
    }
    pub open spec fn wf(&self)->bool {self.storage_wf() && self.traces(self.observation())}
    pub open spec fn frame(&self,prior:&Self,id:usize)->bool {
        self.link()==prior.link() && self.execution_journal()==prior.execution_journal() && self.origin()==prior.origin() && self.next_id()==prior.next_id() && self.last_domain()==prior.last_domain() && self.closed()==prior.closed()
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
    pub open spec fn any_issued(&self)->bool {
        exists|id:usize| #[trigger] self.queues().contains_key(id) && self.queues()[id].issued()
    }
    pub open spec fn any_failed(&self)->bool {
        exists|id:usize| #[trigger] self.queues().contains_key(id) && self.queues()[id].protocol().failed_spec()
    }
    pub open spec fn retries_ready(&self)->bool {
        self.any_failed() && forall|id:usize| #[trigger] self.queues().contains_key(id)
            && self.queues()[id].protocol().failed_spec() ==> self.queues()[id].retry_enabled()
    }
    pub fn new(root_domain:u64)->(out:Self)
        ensures out.execution_journal().is_none(),out.wf(),out.origin().is_none(),!out.closed(),!out.drained_failure(),out.queues().dom()==set![0usize],out.next_id()==1,
            out.queues()[0].slots().len()==0,out.domain_ids()==map![0usize=>root_domain],out.last_domain()==root_domain,
    {
        let mut entries=BTreeMap::new();entries.insert(0, CleanupQueue::scope(root_domain));
        let mut domains=BTreeMap::new();domains.insert(0,root_domain);
        Self {entries,domains,next:1,last_domain:root_domain,sealed:false,consumed_failure:false,lifecycle:None,execution:None,membership:None}
    }
    pub(crate) fn for_lifecycle(ticket:ActionTicket,root_domain:u64)->(out:Self)
        requires ticket.kind==ActionKind::Setup,
        ensures out.execution_journal().is_none(),out.wf(),out.origin()==Some(ticket),!out.closed(),!out.drained_failure(),
            out.queues().dom()==set![0usize],out.domain_ids()==map![0usize=>root_domain],
    {
        let mut out=Self::new(root_domain);out.lifecycle=Some(ticket);out
    }
    /// Bind fresh native queues once, before any work can escape the Begin call.
    /// Removed queues remain historical records; the membership entry names
    /// exactly the queues still held by this owner.
    pub(crate) fn attach_execution(&mut self,journal:&Journal)
        requires old(self).wf(),old(self).execution_journal().is_none(),old(self).queues().dom()==set![0usize],
        ensures final(self).wf(),final(self).execution_journal()==Some(*journal),
            final(self).origin()==old(self).origin(),final(self).domain_ids()==old(self).domain_ids(),
            final(self).next_id()==old(self).next_id(),final(self).last_domain()==old(self).last_domain(),
            final(self).closed()==old(self).closed(),final(self).drained_failure()==old(self).drained_failure(),
            final(self).queues().dom()==old(self).queues().dom(),
            final(self).queues()[0].protocol()==old(self).queues()[0].protocol(),
            final(self).queues()[0].slots()==old(self).queues()[0].slots(),final(self).queues()[0].issued()==old(self).queues()[0].issued(),
    {
        let mut queue=self.take(0);
        queue.attach_execution(journal);
        self.entries.insert(0,queue);self.execution=Some(journal.clone());
        self.membership=Some(journal.allocate(Ghost(joint::Record::Groups {state:self.observation()})));
    }
    pub fn execution_domain(&self)->(out:Option<&Journal>)
        ensures out.is_some()==self.execution_journal().is_some(),out.is_some() ==> *out.unwrap()==self.execution_journal().unwrap(),
    {self.execution.as_ref()}
    pub open spec fn observed(&self,state:Map<nat,joint::Record>)->bool {
        self.link().is_some() && state.contains_key(self.link().unwrap().1)
            && state[self.link().unwrap().1]==(joint::Record::Groups {state:self.observation()})
            && forall|id:usize| #[trigger] self.queues().contains_key(id) ==> {
            let queue=self.queues()[id];let key=queue.link().unwrap().1;
            queue.link().is_some() && state.contains_key(key) && state[key]==(joint::Record::Cleanup {state:queue.observation()})
        }
    }
    pub(crate) fn certify(&self,view:&joint::ReadView)
        requires self.wf(),view.wf(),self.execution_journal()==Some(view.journal_spec()),
        ensures self.observed(view.state()),
    {
        self.membership.as_ref().unwrap().certify(view);
        let ids=self.active_ids();let mut i=0;
        while i<ids.len()
            invariant self.wf(),view.wf(),self.execution_journal()==Some(view.journal_spec()),
                ids@.to_set()==self.queues().dom(),i<=ids.len(),
                forall|j:int| 0<=j<i ==> {
                    let queue=self.queues()[#[trigger] ids@[j]];let key=queue.link().unwrap().1;
                    queue.link().is_some() && view.state().contains_key(key)
                        && view.state()[key]==(joint::Record::Cleanup {state:queue.observation()})
                },
            decreases ids.len()-i,
        {
            assert(self.queues().contains_key(ids@[i as int]));
            self.entries.get(&ids[i]).unwrap().certify(view);i+=1;
        }
        assert forall|id:usize| #[trigger] self.queues().contains_key(id) implies {
            let queue=self.queues()[id];let key=queue.link().unwrap().1;
            queue.link().is_some() && view.state().contains_key(key)
                && view.state()[key]==(joint::Record::Cleanup {state:queue.observation()})
        } by {
            let j=choose|j:int| 0<=j<ids.len() && ids@[j]==id;
            assert(ids@[j]==id);
        }
    }
    pub(crate) proof fn execution_link(&self)
        requires self.wf(),ensures self.link().is_some()==self.execution_journal().is_some(),
            self.link().is_some() ==> Some(self.link().unwrap().0)==self.execution_journal(),
    {}
    pub(crate) fn certify_membership(&self,view:&joint::WriteView)
        requires self.wf(),view.wf(),self.execution_journal()==Some(view.journal_spec()),
        ensures self.link().is_some(),view.state().contains_key(self.link().unwrap().1),
            view.state()[self.link().unwrap().1]==(joint::Record::Groups {state:self.observation()}),
            0<self.membership_trace().len()<=view.events().len(),view.events().take(self.membership_trace().len() as int)==self.membership_trace(),
            self.membership_trace().last().event.key==self.link().unwrap().1,
    {self.membership.as_ref().unwrap().certify_write(view);}
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
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).storage_wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),
            final(self).membership==old(self).membership,final(self).traces(old(self).observation()),
            final(self).traces(GroupState {queues:Self::members(final(self).queues()).insert(id,Self::entry(out)),..final(self).observation()}),
            final(self).domain_ids()==old(self).domain_ids(),final(self).queues()==old(self).queues().remove(id),
            out==old(self).queues()[id],out.wf(),final(self).linked(out),
            out.protocol().domain_id()==final(self).domain_ids()[id],!final(self).closed(),
    {
        let ghost prior=*self;
        let out=self.entries.remove(&id).unwrap();
        assert(self.queues()==prior.queues().remove(id));
        proof {Self::members_remove(prior.queues(),id);
            assert(Self::members(self.queues()).insert(id,Self::entry(out)) =~= Self::members(prior.queues()));}
        out
    }
    fn put(&mut self,id:usize,queue:CleanupQueue<T>)
        requires old(self).storage_wf(),!old(self).closed(),old(self).domain_ids().contains_key(id),
            !old(self).live(id),queue.wf(),old(self).linked(queue),queue.protocol().domain_id()==old(self).domain_ids()[id],
            old(self).traces(GroupState {queues:Self::members(old(self).queues()).insert(id,Self::entry(queue)),..old(self).observation()}),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),
            final(self).membership==old(self).membership,final(self).queues()==old(self).queues().insert(id,queue),
    {
        let ghost prior=*self;
        self.entries.insert(id,queue);
        assert(self.queues()==prior.queues().insert(id,queue));
        proof {Self::members_insert(prior.queues(),id,queue);}
    }
    fn commit_membership(&mut self,Ghost(before):Ghost<GroupState>,Ghost(event):Ghost<GroupEvent>,kind:MembershipAction,id:usize,removed:Option<&CleanupQueue<T>>)
        requires old(self).storage_wf(),old(self).traces(before),
            joint::groups::step(before,old(self).observation(),event),
            match event {GroupEvent::Add {id:added,..}=>kind==MembershipAction::Add && id==added,GroupEvent::Remove {id:removed}=>kind==MembershipAction::Remove && id==removed,GroupEvent::ConsumedFailure=>kind==MembershipAction::ConsumedFailure,_=>false},
            event is Add ==> old(self).live(event->Add_id) && (old(self).execution_journal().is_some() ==> old(self).queues()[event->Add_id].link().is_some())
                && (event->Add_key,event->Add_domain)==Self::entry(old(self).queues()[event->Add_id]),
            event is Remove ==> removed.is_some() && removed.unwrap().wf() && old(self).linked(*removed.unwrap())
                && drained(*removed.unwrap())
                && before.queues[event->Remove_id]==Self::entry(*removed.unwrap()),
        ensures final(self).wf(),final(self).queues()==old(self).queues(),final(self).domain_ids()==old(self).domain_ids(),
            final(self).origin()==old(self).origin(),final(self).next_id()==old(self).next_id(),final(self).last_domain()==old(self).last_domain(),
            final(self).closed()==old(self).closed(),final(self).drained_failure()==old(self).drained_failure(),
            final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),
            final(self).link().is_some() ==> final(self).membership_trace().last().event.change==(joint::Change::Groups {event}),
    {
        let ghost after=self.observation();
        if let Some(journal)=&self.execution {
            // No payload is dropped and no nested queue/value/slot lock is
            // acquired under this guard.
            let mut view=journal.write();
            if kind==MembershipAction::Add {self.entries.get(&id).unwrap().certify_write(&view);}
            if kind==MembershipAction::Remove {let q=removed.unwrap();q.certify_write(&view);proof {q.drained_observation();}}
            proof {reveal(joint::changes);reveal(joint::groups::guard);}
            view=self.membership.as_mut().unwrap().update_guarded(view,Ghost(joint::Record::Groups {state:after}),Ghost(joint::Change::Groups {event}));
            view.finish();
        }
    }
    fn commit_seal(&mut self)
        requires old(self).wf(),old(self).all_drained(),
        ensures final(self).storage_wf(),final(self).traces(GroupState {queues:Map::empty(),sealed:true,..old(self).observation()}),
            final(self).queues()==old(self).queues(),final(self).domain_ids()==old(self).domain_ids(),
            final(self).origin()==old(self).origin(),final(self).next_id()==old(self).next_id(),final(self).last_domain()==old(self).last_domain(),
            final(self).closed()==old(self).closed(),final(self).drained_failure()==old(self).drained_failure(),
            final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),
            final(self).link().is_some() ==> final(self).membership_trace().last().event.change==(joint::Change::Groups {event:GroupEvent::Seal}),
    {
        if let Some(journal)=&self.execution {
            let ids=self.active_ids();let mut view=journal.write();let mut i=0;
            let ghost before=self.observation();
            while i<ids.len()
                invariant self.wf(),self.all_drained(),view.wf(),view.journal_spec()==*journal,self.execution_journal()==Some(*journal),
                    before==self.observation(),ids@.to_set()==self.queues().dom(),i<=ids.len(),
                    forall|j:int| 0<=j<i ==> joint::groups::drained(view.state(),before.queues[#[trigger] ids@[j]]),
                decreases ids.len()-i,
            {
                let q=self.entries.get(&ids[i]).unwrap();q.certify_write(&view);proof {q.drained_observation();}i+=1;
            }
            assert forall|id:usize| #[trigger] before.queues.contains_key(id) implies joint::groups::drained(view.state(),before.queues[id]) by {
                let j=choose|j:int|0<=j<ids.len() && ids@[j]==id;assert(ids@[j]==id);
            }
            proof {reveal(joint::changes);reveal(joint::groups::guard);}
            view=self.membership.as_mut().unwrap().update_guarded(view,
                Ghost(joint::Record::Groups {state:GroupState {queues:Map::empty(),sealed:true,..before}}),Ghost(joint::Change::Groups {event:GroupEvent::Seal}));
            view.finish();
        }
    }
    fn consume_failure(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).queues()==old(self).queues(),final(self).domain_ids()==old(self).domain_ids(),
            final(self).origin()==old(self).origin(),final(self).next_id()==old(self).next_id(),final(self).last_domain()==old(self).last_domain(),
            final(self).closed()==old(self).closed(),final(self).drained_failure(),final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),
    {
        if self.consumed_failure {return;}
        let ghost before=self.observation();self.consumed_failure=true;
        self.commit_membership(Ghost(before),Ghost(GroupEvent::ConsumedFailure),MembershipAction::ConsumedFailure,0,None);
    }
    /// Domains increase just as the host's global receipt allocator does. The
    /// high-water mark rejects reuse without retaining each removed queue.
    pub fn add_iterator(&mut self,domain:u64,committed:Vec<Binding>)->(out:Result<usize,RestoreError>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),
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
        let ghost before=self.observation();let ghost before_queues=self.queues();
        let id=self.next;self.next+=1;self.last_domain=domain;
        let mut queue=CleanupQueue::iterator(domain,committed);
        if let Some(journal)=&self.execution {queue.attach_execution(journal);}
        let ghost key=Self::entry(queue).0;
        proof {Self::members_insert(before_queues,id,queue);}
        self.entries.insert(id,queue);
        self.domains.insert(id,domain);
        self.commit_membership(Ghost(before),Ghost(GroupEvent::Add {id,key,domain}),MembershipAction::Add,id,None);
        Ok(id)
    }
    /// Acquisition uses the actual stage state, not a host-maintained shadow set.
    /// A cancelled pending stage may still land and register its inverse.
    pub open spec fn acquisition_open(&self,id:usize)->bool {
        self.live(id) && !self.queues()[id].protocol().stage().cancellation()
    }
    pub fn accepts_acquisition(&self,id:usize)->(out:bool)
        ensures out==self.acquisition_open(id),
    {match self.entries.get(&id) {Some(queue)=>!queue.is_cancelled(),None=>false}}
    pub fn can_add_iterator(&self,domain:u64)->(out:bool)
        ensures out==(!self.closed() && domain>self.last_domain() && self.next_id()<usize::MAX),
    {!self.sealed && domain>self.last_domain && self.next<usize::MAX}
    pub fn register(&mut self,id:usize,payload:T)->(out:Result<usize,T>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).queues().dom()==old(self).queues().dom(), final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),out.is_ok()==old(self).live(id),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==payload,
            out.is_ok() ==> final(self).live(id)
                && out->Ok_0==old(self).queues()[id].slots().len()
                && final(self).queues()[id].link()==old(self).queues()[id].link()
                && final(self).queues()[id].slots()==old(self).queues()[id].slots().push(Some(payload)),
    {
        match self.register_following(id,payload,Tracked(None),Tracked(None)) {Ok(insertion)=>Ok(insertion.token),Err(payload)=>Err(payload)}
    }
    pub(crate) fn register_following(&mut self,id:usize,payload:T,Tracked(cause):Tracked<Option<joint::Receipt>>,Tracked(pending):Tracked<Option<joint::Pending>>)->(out:Result<crate::cleanup_queue::Insertion,T>)
        requires old(self).wf(),cause.is_some() ==> cause.unwrap().wf(),
            pending.is_some() ==> old(self).live(id) && joint::registration_pending(pending,cause,old(self).queues()[id].link()),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).queues().dom()==old(self).queues().dom(), final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),out.is_ok()==old(self).live(id),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==payload,
            out.is_ok() ==> final(self).live(id) && final(self).acquisition_open(id)==old(self).acquisition_open(id)
                && out->Ok_0.token==old(self).queues()[id].slots().len()
                && final(self).queues()[id].link()==old(self).queues()[id].link()
                && final(self).queues()[id].slots()==old(self).queues()[id].slots().push(Some(payload))
                && final(self).queues()[id].protocol().waiting()==old(self).queues()[id].protocol().waiting().push(out->Ok_0.token)
                && out->Ok_0.recorded(final(self).queues()[id].link(),final(self).queues()[id].observation(),cause,joint::pending_index(pending)),
    {
        if !self.contains(id) {return Err(payload);}
        let mut queue=self.take(id);let token=queue.register_following(payload,Tracked(cause),Tracked(pending));self.put(id,queue);Ok(token)
    }
    pub open spec fn poll_enabled(&self,id:usize,target:Option<&[Binding]>)->bool {
        self.live(id) && (self.queues()[id].protocol().stage().pending()
            || (!self.queues()[id].protocol().stage().settled() && !self.queues()[id].protocol().stage().cancellation()
                && target.is_some() && crate::episode::binding_set(target.unwrap()@)
                    ==crate::episode::binding_set(self.queues()[id].protocol().stage().committed_view())))
    }
    pub fn admit(&mut self,id:usize,target:Option<&[Binding]>)->(out:bool)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),out ==> old(self).live(id),
            final(self).live(id)==old(self).live(id),
            out ==> final(self).queues()[id].protocol().stage().pending(),
            out==old(self).poll_enabled(id,target),
    {
        if !self.contains(id) {return false;}
        let mut queue=self.take(id);let out=queue.admit(target);self.put(id,queue);out
    }
    pub fn cancel(&mut self,id:usize)
        requires old(self).wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),
            final(self).live(id)==old(self).live(id),
            old(self).live(id) ==> final(self).queues()[id].protocol().stage().cancellation()
                && final(self).queues()[id].protocol().stage().pending()==old(self).queues()[id].protocol().stage().pending(),
    {
        if !self.contains(id) {return;}
        let mut queue=self.take(id);queue.cancel();self.put(id,queue);
    }
    pub fn land_result<E>(&mut self,id:usize,result:Result<Option<T>,E>)
        ->(out:Result<StageReport<E>,Result<Option<T>,E>>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            out.is_ok()==(old(self).live(id) && old(self).queues()[id].protocol().stage().pending()),
            out.is_err() ==> out->Err_0==result,
            out.is_ok() && result.is_ok() && result->Ok_0.is_some() ==>
                final(self).queues()[id].slots()==old(self).queues()[id].slots().push(result->Ok_0),
            out.is_ok() ==> out->Ok_0.error==match result {Err(error)=>Some(error),_=>None},
            out.is_ok() ==> !final(self).queues()[id].protocol().stage().pending()
                && out->Ok_0.continue_iteration==(result.is_ok() && result->Ok_0.is_some()
                    && !old(self).queues()[id].protocol().stage().cancellation()),
    {
        if !self.contains(id) {return Err(result);}
        let mut queue=self.take(id);let out=queue.land_result(result);self.put(id,queue);out
    }
    pub fn pop(&mut self,id:usize)->(out:Result<Option<(RestoreTicket,T)>,RestoreError>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
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
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==(old(self).drained_failure() || (out.is_ok() && outcome==RestoreOutcome::Drained)),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            out.is_ok()==(old(self).live(id) && old(self).queues()[id].completion_enabled(ticket,outcome,retry)),
            out.is_err() ==> out->Err_0==retry,
    {
        if !self.contains(id) {return Err(retry);}
        let mut queue=self.take(id);let out=queue.complete(ticket,outcome,retry);self.put(id,queue);
        if out.is_ok() && outcome==RestoreOutcome::Drained {self.consume_failure();}
        out
    }
    #[allow(clippy::type_complexity)]
    pub fn complete_future<E>(&mut self,id:usize,completion:Completion<RestoreTicket,Result<(),E>>,retry:Option<T>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,T>,(Completion<RestoreTicket,Result<(),E>>,Option<T>)>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==(old(self).drained_failure() || (out.is_ok() && out->Ok_0.outcome==RestoreOutcome::Drained)),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            out.is_err() ==> out->Err_0==(completion,retry),
            out.is_ok() ==> old(self).live(id) && out->Ok_0.result==completion.result()
                && old(self).queues()[id].issued()
                && old(self).queues()[id].protocol().selected()==Some(completion.argument())
                && !final(self).queues()[id].issued(),
    {
        if !self.contains(id) {return Err((completion,retry));}
        let mut queue=self.take(id);let out=queue.complete_future(completion,retry,policy);self.put(id,queue);
        if let Ok(report)=&out {if report.outcome==RestoreOutcome::Drained {self.consume_failure();}}
        out
    }
    #[allow(clippy::type_complexity)]
    pub fn complete_failure<E>(&mut self,id:usize,ticket:RestoreTicket,error:E,retry:Option<T>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,T>,(RestoreTicket,E,Option<T>)>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==(old(self).drained_failure() || (out.is_ok() && out->Ok_0.outcome==RestoreOutcome::Drained)),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            out.is_err() ==> out->Err_0==(ticket,error,retry),
            out.is_ok() ==> out->Ok_0.result==Err(error) && out->Ok_0.outcome!=RestoreOutcome::Succeeded,
    {
        if !self.contains(id) {return Err((ticket,error,retry));}
        let mut queue=self.take(id);let out=queue.complete_failure(ticket,error,retry,policy);self.put(id,queue);
        if let Ok(report)=&out {if report.outcome==RestoreOutcome::Drained {self.consume_failure();}}
        out
    }
    #[allow(clippy::type_complexity)]
    pub fn complete_result<E>(&mut self,id:usize,ticket:RestoreTicket,result:Result<(),E>,retry:Option<T>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,T>,(RestoreTicket,Result<(),E>,Option<T>)>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
            final(self).drained_failure()==(old(self).drained_failure() || (out.is_ok() && out->Ok_0.outcome==RestoreOutcome::Drained)),
            out.is_err() ==> out->Err_0==(ticket,result,retry),
            out.is_ok() ==> out->Ok_0.result==result && out->Ok_0.outcome==crate::cleanup_queue::completion::outcome(result,retry,policy),
    {
        if !self.contains(id) {return Err((ticket,result,retry));}
        let mut queue=self.take(id);let out=queue.complete_result(ticket,result,retry,policy);self.put(id,queue);
        if let Ok(report)=&out {if report.outcome==RestoreOutcome::Drained {self.consume_failure();}}
        out
    }
    pub fn retry(&mut self,id:usize)->(out:Result<RestoreTicket,RestoreError>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),final(self).domain_ids()==old(self).domain_ids(),final(self).live(id)==old(self).live(id),
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
    pub fn has_issued(&self)->(out:bool)
        requires self.wf(),ensures out==self.any_issued(),
    {
        let ids=self.active_ids();let mut i=0;
        while i<ids.len()
            invariant self.wf(),ids@.to_set()==self.queues().dom(),i<=ids.len(),
                forall|j:int| 0<=j<i ==> !self.queues()[#[trigger] ids@[j]].issued(),
            decreases ids.len()-i,
        {
            assert(ids@.to_set().contains(ids@[i as int]));assert(self.live(ids@[i as int]));
            if self.entries.get(&ids[i]).unwrap().is_issued() {return true;}
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
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),out==old(self).retries_ready(),
            final(self).domain_ids()==old(self).domain_ids(),final(self).closed()==old(self).closed(),
            final(self).queues().dom()==old(self).queues().dom(),
            final(self).next_id()==old(self).next_id(),final(self).last_domain()==old(self).last_domain(),
            out ==> !final(self).any_failed(),!out ==> *final(self)==*old(self),
    {
        if !self.can_retry_all() {return false;}
        let ghost prior=*self;
        let ids=self.active_ids();let mut i=0;
        while i<ids.len()
            invariant self.wf(),self.link()==prior.link(),self.execution_journal()==prior.execution_journal(),prior.retries_ready(),ids@.no_duplicates(),ids@.to_set()==self.queues().dom(),
                self.domain_ids()==prior.domain_ids(),self.closed()==prior.closed(),
                self.next_id()==prior.next_id(),self.last_domain()==prior.last_domain(),
                self.drained_failure()==prior.drained_failure(),self.origin()==prior.origin(),
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
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),
            out==(old(self).live(id) && drained(old(self).queues()[id])),
            out ==> final(self).queues()==old(self).queues().remove(id)
                && final(self).domain_ids()==old(self).domain_ids().remove(id)
                && !old(self).queues()[id].issued()
                && forall|j:int| 0<=j<old(self).queues()[id].slots().len() ==> #[trigger] old(self).queues()[id].slots()[j].is_none(),
            !out ==> *final(self)==*old(self),
            out && final(self).link().is_some() ==> final(self).membership_trace().last().event.change==(joint::Change::Groups {event:GroupEvent::Remove {id}}),
    {
        if !self.contains(id) {return false;}
        let queue=self.entries.get(&id).unwrap();
        if !queue.is_empty() || queue.is_pending() || !queue.is_settled() {return false;}
        let ghost before=self.observation();let ghost before_queues=self.queues();
        let queue=self.take(id);self.domains.remove(&id);
        proof {Self::members_remove(before_queues,id);}
        self.commit_membership(Ghost(before),Ghost(GroupEvent::Remove {id}),MembershipAction::Remove,id,Some(&queue));true
    }
    /// Inspect every owned queue and close admission in one exclusive operation.
    /// There is no host-supplied manifest from which a group could be omitted.
    pub fn seal(&mut self)->(out:bool)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).drained_failure()==old(self).drained_failure(),out==old(self).all_drained(),out ==> final(self).closed(),
            final(self).next_id()==old(self).next_id(),final(self).last_domain()==old(self).last_domain(),
            out ==> final(self).queues()==Map::empty() && final(self).domain_ids()==Map::empty(),
            !out ==> *final(self)==*old(self),
            out && final(self).link().is_some() ==> final(self).membership_trace().last().event.change==(joint::Change::Groups {event:GroupEvent::Seal}),
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
        self.commit_seal();
        self.entries=BTreeMap::new();self.domains=BTreeMap::new();self.sealed=true;
        assert(Self::members(self.queues()) =~= Map::empty());true
    }
}
impl<C,X> CleanupGroups<crate::lifecycle_state::registration::shared_child::ChildCleanup<C,X>> {
    pub fn dispatch(&mut self,id:usize)->(out:Result<Option<crate::cleanup_queue::completion::CleanupDispatch<C,X>>,RestoreError>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),final(self).wf(),final(self).origin()==old(self).origin(),final(self).frame(old(self),id),
            final(self).domain_ids()==old(self).domain_ids(),final(self).queues().dom()==old(self).queues().dom(),
            final(self).drained_failure()==old(self).drained_failure(),
            (out.is_err() || out==Ok(None)) && old(self).live(id) ==> final(self).queues()[id].same(&old(self).queues()[id])
                && final(self).queues()[id].trace()==old(self).queues()[id].trace(),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().selected_from(old(self).queues()[id].protocol().selected(),old(self).queues()[id].protocol().waiting()),
            out.is_ok() && out->Ok_0.is_some() ==> old(self).live(id) && out->Ok_0.unwrap().from_slot(old(self).queues()[id].slots()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap() is Value ==> {
                let report=out->Ok_0.unwrap();let ticket=report->Value_ticket;let completion=report->Value_completion;
                &&& completion.evidence().records(old(self).queues()[id].slots()[ticket.token as int].unwrap()->Value_0,ticket,old(self).queues()[id].link())
                &&& final(self).queues()[id].link().is_some() ==> completion.evidence().acknowledgement().unwrap().events()==final(self).queues()[id].trace()
                &&& final(self).queues()[id].slots()==old(self).queues()[id].slots().update(ticket.token as int,
                    if completion.restored.is_some() {None} else {old(self).queues()[id].slots()[ticket.token as int]})
                &&& final(self).queues()[id].protocol().failed_spec()==completion.restored.is_none()
            },
    {
        if !self.contains(id) {return Err(RestoreError::InvalidState);}
        let mut queue=self.take(id);let out=queue.dispatch();self.put(id,queue);out
    }
}

}

#[path = "payload_cleanup.rs"]
pub mod payload;
