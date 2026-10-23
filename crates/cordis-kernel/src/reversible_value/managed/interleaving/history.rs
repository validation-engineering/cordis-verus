//! A constructive source log for the production mixed cleanup dispatcher.
//! Retained slots, not a supplied success list, determine missing obligations.
#[cfg(verus_keep_ghost)]
use super::{super::cleanup_path::Turn, inverse_action};
use super::{
    super::{Action, Owner},
    Event,
};
use crate::reversible_value::joint;
#[cfg(verus_keep_ghost)]
use crate::{cleanup_groups::payload::recovery as cleanup, cleanup_queue::CleanupQueue};
use vstd::prelude::*;

verus! {
type Slots<A,R,T,M,X> = Seq<Option<Action<A,R,T,M,X>>>;
#[allow(dead_code)]
pub tracked struct History<A,R,T:?Sized,M,X> {
    ghost initial:Slots<A,R,T,M,X>,
    ghost current:Slots<A,R,T,M,X>,
    ghost link:Option<(joint::Journal,nat)>,
    ghost domain:u64,
    ghost events:Seq<Event<A,R,T,M,X>>,
    receipts:Map<int,joint::Receipt>,
}
pub open spec fn consumed<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,receipts:Map<int,joint::Receipt>,link:Option<(joint::Journal,nat)>,token:int,action:Action<A,R,T,M,X>,i:int)->bool {
    0<=i<events.len() && events[i] is Managed && events[i].source() && events[i].succeeded()
        && events[i].inverse()==inverse_action(action) && events[i]->Managed_0.queue_link()==link && events[i]->Managed_0.ticket().token==token
        && (link.is_some() ==> receipts.contains_key(i) && receipts[i].wf() && receipts[i].same(&events[i]->Managed_0.acknowledgement().unwrap()))
}
impl<A,R,T:?Sized,M,X> History<A,R,T,M,X> {
    /// Original action at each token; later registrations only append entries.
    pub closed spec fn initial(&self)->Seq<Option<Action<A,R,T,M,X>>> {self.initial}
    pub closed spec fn current(&self)->Seq<Option<Action<A,R,T,M,X>>> {self.current}
    pub closed spec fn domain(&self)->u64 {self.domain}
    pub closed spec fn link(&self)->Option<(joint::Journal,nat)> {self.link}
    pub closed spec fn events(&self)->Seq<Event<A,R,T,M,X>> {self.events}
    pub closed spec fn receipts(&self)->Map<int,joint::Receipt> {self.receipts}
    pub open spec fn matches(&self,queue:CleanupQueue<Action<A,R,T,M,X>>)->bool {
        queue.wf() && self.link()==queue.link() && self.domain()==queue.protocol().domain_id() && self.current()==queue.slots()
    }
    /// Only an ordinary host action can remain issued across public calls.
    /// Managed inverses execute and acknowledge inside the verified dispatcher.
    pub open spec fn host_turn(&self,queue:CleanupQueue<Action<A,R,T,M,X>>)->bool {
        queue.issued() ==> queue.protocol().selected().is_some() && {
            let token=queue.protocol().selected().unwrap().token as int;
            token>=self.initial().len() || self.initial()[token].is_none() || !cleanup::managed(self.initial()[token].unwrap())
        }
    }
    pub open spec fn accounted(&self,token:int)->bool {
        self.initial()[token].is_some() && cleanup::managed(self.initial()[token].unwrap()) ==> {
            self.current()[token]==self.initial()[token] || self.current()[token].is_none()
                && exists|i:int|#[trigger] consumed(self.events(),self.receipts(),self.link(),token,self.initial()[token].unwrap(),i)
        }
    }
    #[verifier::opaque]
    pub open spec fn wf(&self)->bool {
        &&& self.current().len()>=self.initial().len()
        &&& forall|i:int|0<=i<self.events().len() ==> (#[trigger] self.events()[i]).source()
        &&& forall|token:int|0<=token<self.initial().len() ==> #[trigger] self.accounted(token)
    }
    proof fn establish(&self)
        requires self.current().len()>=self.initial().len(),
            forall|i:int|0<=i<self.events().len() ==> (#[trigger] self.events()[i]).source(),
            forall|token:int|0<=token<self.initial().len() ==> #[trigger] self.accounted(token),
        ensures self.wf(),
    {reveal(History::wf);}
    pub proof fn sources(&self)
        requires self.wf(),
        ensures forall|i:int|0<=i<self.events().len() ==> (#[trigger] self.events()[i]).source(),
    {reveal(History::wf);}
    pub proof fn conservation(&self,token:int)
        requires self.wf(),0<=token<self.initial().len(),
        ensures self.accounted(token),
    {reveal(History::wf);}
    pub proof fn extent(&self)
        requires self.wf(),ensures self.current().len()>=self.initial().len(),
    {reveal(History::wf);}
    pub proof fn new(queue:CleanupQueue<Action<A,R,T,M,X>>)->(tracked out:Self)
        requires queue.wf(),
        ensures out.wf(),out.matches(queue),out.initial()==queue.slots(),out.events().len()==0,out.host_turn(queue),
    {
        reveal(History::wf);queue.issued_slot_empty();
        Self {initial:queue.slots(),current:queue.slots(),link:queue.link(),domain:queue.protocol().domain_id(),events:Seq::empty(),receipts:Map::tracked_empty()}
    }
    /// Appending registrations cannot reset old token identities or witnesses.
    pub open spec fn starts_with(&self,slots:Seq<Option<Action<A,R,T,M,X>>>)->bool {
        slots.len()<=self.initial().len() && self.initial().take(slots.len() as int)==slots
    }
    pub proof fn extend(tracked &mut self,queue:CleanupQueue<Action<A,R,T,M,X>>)
        requires old(self).wf(),old(self).current().len()==old(self).initial().len(),queue.wf(),
            queue.link()==old(self).link(),queue.protocol().domain_id()==old(self).domain(),
            queue.slots().len()>=old(self).current().len(),queue.slots().take(old(self).current().len() as int)==old(self).current(),
        ensures old(self).host_turn(queue) ==> final(self).host_turn(queue),
            final(self).wf(),final(self).matches(queue),final(self).starts_with(old(self).initial()),
            final(self).initial().len()==queue.slots().len(),
            final(self).initial()==old(self).initial()+queue.slots().subrange(old(self).initial().len() as int,queue.slots().len() as int),
            final(self).events()==old(self).events(),final(self).link()==old(self).link(),final(self).domain()==old(self).domain(),
    {
        hide(Event::source);hide(inverse_action);
        queue.issued_slot_empty();self.frame(queue);self.sources();let ghost prior=*self;let n=self.initial.len();
        self.initial=self.initial+self.current.subrange(n as int,self.current.len() as int);
        assert(self.initial().take(n as int)==prior.initial());
        assert forall|token:int|0<=token<self.initial().len() implies #[trigger] self.accounted(token) by {
            if token<n {
                prior.conservation(token);assert(self.initial()[token]==prior.initial()[token]);
                if self.initial()[token].is_some() && cleanup::managed(self.initial()[token].unwrap()) && self.current()[token]!=self.initial()[token] {
                    let i=choose|i:int|#[trigger] consumed(prior.events(),prior.receipts(),prior.link(),token,prior.initial()[token].unwrap(),i);
                    assert(consumed(self.events(),self.receipts(),self.link(),token,self.initial()[token].unwrap(),i));
                }
            } else {assert(self.initial()[token]==self.current()[token]);}
        }
        if queue.issued() {
            let token=queue.protocol().selected().unwrap().token as int;
            if token<n {assert(self.initial()[token]==prior.initial()[token]);}
            else {assert(self.initial()[token]==queue.slots()[token]);}
        }
        self.establish();
    }
    pub proof fn prefix_transitive(&self,prior:Self,slots:Seq<Option<Action<A,R,T,M,X>>>)
        requires prior.starts_with(slots),self.starts_with(prior.initial()),
        ensures self.starts_with(slots),
    {assert(self.initial().take(slots.len() as int) =~= slots);}

    /// Actual independent writes/restores may be inserted between cleanup turns.
    /// They never silently consume this queue's retained slots.
    pub proof fn foreign(tracked &mut self,event:Event<A,R,T,M,X>)
        requires old(self).wf(),event.source(),
        ensures final(self).wf(),final(self).initial()==old(self).initial(),final(self).current()==old(self).current(),
            final(self).link()==old(self).link(),final(self).domain()==old(self).domain(),
            final(self).events()==old(self).events().push(event),
    {
        hide(Event::source);hide(inverse_action);
        self.sources();self.extent();let ghost prior=*self;self.events=self.events.push(event);
        assert forall|i:int|0<=i<self.events().len() implies (#[trigger] self.events()[i]).source() by {
            if i<prior.events().len() {assert(self.events()[i]==prior.events()[i]);} else {assert(self.events()[i]==event);}
        }
        assert forall|token:int|0<=token<self.initial().len() implies #[trigger] self.accounted(token) by {
            prior.conservation(token);
            if self.initial()[token].is_some() && cleanup::managed(self.initial()[token].unwrap()) && self.current()[token]!=self.initial()[token] {
                let i=choose|i:int|#[trigger] consumed(prior.events(),prior.receipts(),prior.link(),token,prior.initial()[token].unwrap(),i);
                assert(self.events()[i]==prior.events()[i]);
                assert(consumed(self.events(),self.receipts(),self.link(),token,self.initial()[token].unwrap(),i));
            }
        }
        self.establish();
    }
    /// Follow actual queue changes that preserve the tracked managed tokens,
    /// including Retry and appending later inverse registrations.
    pub proof fn frame(tracked &mut self,queue:CleanupQueue<Action<A,R,T,M,X>>)
        requires old(self).wf(),queue.wf(),queue.link()==old(self).link(),queue.protocol().domain_id()==old(self).domain(),
            queue.slots().len()>=old(self).initial().len(),
            forall|token:int|0<=token<old(self).initial().len() && (#[trigger] old(self).initial()[token]).is_some() && cleanup::managed(old(self).initial()[token].unwrap()) ==>
                queue.slots()[token]==old(self).current()[token],
        ensures final(self).wf(),final(self).matches(queue),final(self).initial()==old(self).initial(),final(self).events()==old(self).events(),
            final(self).link()==old(self).link(),final(self).domain()==old(self).domain(),
    {
        hide(Event::source);hide(inverse_action);
        self.sources();self.extent();let ghost prior=*self;self.current=queue.slots();
        assert(self.events()==prior.events());
        assert forall|i:int|0<=i<self.events().len() implies (#[trigger] self.events()[i]).source() by {assert(self.events()[i]==prior.events()[i]);}
        assert forall|token:int|0<=token<self.initial().len() implies #[trigger] self.accounted(token) by {
            prior.conservation(token);
            if self.initial()[token].is_some() && cleanup::managed(self.initial()[token].unwrap()) {
                assert(self.current()[token]==prior.current()[token]);
                if self.current()[token]!=self.initial()[token] {
                    let i=choose|i:int|#[trigger] consumed(prior.events(),prior.receipts(),prior.link(),token,prior.initial()[token].unwrap(),i);
                    assert(consumed(self.events(),self.receipts(),self.link(),token,self.initial()[token].unwrap(),i));
                }
            }
        }
        self.establish();
    }
    pub proof fn record(tracked &mut self,before:CleanupQueue<Action<A,R,T,M,X>>,after:CleanupQueue<Action<A,R,T,M,X>>,tracked dispatch:&Turn<A,R,T,M,X>)
        requires old(self).wf(),old(self).matches(before),dispatch.finished(before,after),dispatch.authentic(),
        ensures final(self).host_turn(after),
            final(self).wf(),final(self).matches(after),final(self).initial()==old(self).initial(),
            final(self).link()==old(self).link(),final(self).domain()==old(self).domain(),
            final(self).events()==if dispatch.managed() {old(self).events().push(Event::Managed(*dispatch))} else {old(self).events()},
    {
        hide(joint::valid);hide(joint::step);hide(Event::source);hide(inverse_action);
        self.sources();self.extent();let ghost prior=*self;dispatch.selected_kind(before.slots());
        let token=dispatch.ticket().token as int;
        if !dispatch.managed() && token<self.initial().len() {
            self.conservation(token);
            assert(self.initial()[token].is_none() || !cleanup::managed(self.initial()[token].unwrap()));
        }
        if dispatch.managed() {
            let i=self.events.len() as int;
            if self.link.is_some() {let tracked receipt=dispatch.acknowledgement_receipt();if let Some(r)=receipt {self.receipts.tracked_insert(i,r);}}
            self.events=self.events.push(Event::Managed(*dispatch));
            assert(Event::Managed(*dispatch).source()) by {reveal(Event::source);}
        }
        self.current=after.slots();
        assert forall|i:int|0<=i<self.events().len() implies (#[trigger] self.events()[i]).source() by {
            if i<prior.events().len() {assert(self.events()[i]==prior.events()[i]);} else {assert(self.events()[i]==Event::Managed(*dispatch));}
        }
        assert forall|token:int|0<=token<self.initial().len() implies #[trigger] self.accounted(token) by {
            prior.conservation(token);
            if self.initial()[token].is_some() && cleanup::managed(self.initial()[token].unwrap()) {
                if prior.current()[token]==prior.initial()[token] {
                    if token==dispatch.ticket().token && dispatch.managed() && dispatch.succeeded() {
                        assert(consumed(self.events(),self.receipts(),self.link(),token,self.initial()[token].unwrap(),prior.events().len() as int));
                    }
                } else {
                    let i=choose|i:int|#[trigger] consumed(prior.events(),prior.receipts(),prior.link(),token,prior.initial()[token].unwrap(),i);
                    assert(i<prior.events().len());assert(self.events()[i]==prior.events()[i]);
                    assert(self.receipts().contains_key(i)==prior.receipts().contains_key(i));
                    assert(consumed(self.events(),self.receipts(),self.link(),token,self.initial()[token].unwrap(),i));
                }
            }
        }
        self.establish();
    }

}
impl<C,G,A,R,T:?Sized,M,X> Owner<C,G,A,R,T,M,X> {
    /// The actual retry keeps every inverse in the recorded path and allocates
    /// a fresh attempt. Rejected retry leaves that path unchanged as well.
    pub fn retry_recorded(&mut self,id:usize,Tracked(history):Tracked<&mut History<A,R,T,M,X>>)
        ->(out:Result<crate::cleanup_journal::RestoreTicket,crate::cleanup_journal::RestoreError>)
        requires old(self).wf(),old(self).cleanup_state().live(id),old(history).wf(),old(history).matches(old(self).cleanup_state().queues()[id]),
        ensures old(history).host_turn(old(self).cleanup_state().queues()[id]) ==> final(history).host_turn(final(self).cleanup_state().queues()[id]),
            final(history).current()==old(history).current(),
            final(self).wf(),final(self).cleanup_state().live(id),final(history).wf(),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(history).link()==old(history).link(),final(history).domain()==old(history).domain(),
            final(history).matches(final(self).cleanup_state().queues()[id]),final(history).initial()==old(history).initial(),final(history).events()==old(history).events(),
            out.is_ok()==old(self).cleanup_state().queues()[id].retry_enabled(),
            out.is_ok() ==> final(self).cleanup_state().queues()[id].protocol().selected()==Some(out->Ok_0)
                && out->Ok_0.token==old(self).cleanup_state().queues()[id].protocol().selected().unwrap().token
                && out->Ok_0.attempt>old(self).cleanup_state().queues()[id].protocol().selected().unwrap().attempt,
    {
        let out=self.retry(id);proof {history.extent();history.frame(self.cleanup_state().queues()[id]);}out
    }
    /// Execute the same production dispatcher and retain its erased source
    /// history. Failed attempts remain in both the queue and this event log.
    pub fn dispatch_recorded(&mut self,id:usize,Tracked(history):Tracked<&mut History<A,R,T,M,X>>)
        ->(out:crate::cleanup_groups::payload::DispatchResult<A,R,std::sync::Arc<super::super::Slot<T,M>>,T,X>)
        requires old(self).wf(),old(self).cleanup_state().live(id),old(history).wf(),old(history).matches(old(self).cleanup_state().queues()[id]),
        ensures old(history).host_turn(old(self).cleanup_state().queues()[id]) ==> final(history).host_turn(final(self).cleanup_state().queues()[id]),
            final(history).current().len()==old(history).current().len(),
            out.is_err() || out==Ok(None) ==> final(history).current()==old(history).current(),
            final(self).wf(),final(history).wf(),final(self).cleanup_state().live(id),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().authentic()
                && out->Ok_0.unwrap().finished(old(self).cleanup_state().queues()[id],final(self).cleanup_state().queues()[id]),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(history).link()==old(history).link(),final(history).domain()==old(history).domain(),
            final(history).matches(final(self).cleanup_state().queues()[id]),final(history).initial()==old(history).initial(),
            final(history).events()==if out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed()
                {old(history).events().push(Event::Managed(out->Ok_0.unwrap()))} else {old(history).events()},
    {self.dispatch_recorded_following(Tracked(None),id,Tracked(history))}
    pub(crate) fn dispatch_recorded_following(&mut self,Tracked(cause):Tracked<Option<joint::Receipt>>,id:usize,Tracked(history):Tracked<&mut History<A,R,T,M,X>>)
        ->(out:crate::cleanup_groups::payload::DispatchResult<A,R,std::sync::Arc<super::super::Slot<T,M>>,T,X>)
        requires old(self).wf(),cause.is_some() ==> cause.unwrap().wf(),old(self).cleanup_state().live(id),old(history).wf(),old(history).matches(old(self).cleanup_state().queues()[id]),
        ensures out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed() ==> out->Ok_0.unwrap().follows_boundary(cause),
            old(history).host_turn(old(self).cleanup_state().queues()[id]) ==> final(history).host_turn(final(self).cleanup_state().queues()[id]),
            final(history).current().len()==old(history).current().len(),
            out.is_err() || out==Ok(None) ==> final(history).current()==old(history).current(),
            final(self).wf(),final(history).wf(),final(self).cleanup_state().live(id),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().authentic()
                && out->Ok_0.unwrap().finished(old(self).cleanup_state().queues()[id],final(self).cleanup_state().queues()[id]),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(history).link()==old(history).link(),final(history).domain()==old(history).domain(),
            final(history).matches(final(self).cleanup_state().queues()[id]),final(history).initial()==old(history).initial(),
            final(history).events()==if out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed()
                {old(history).events().push(Event::Managed(out->Ok_0.unwrap()))} else {old(history).events()},
    {
        let ghost before=self.cleanup_state().queues()[id];
        let out=self.dispatch_payload_cleanup_following(Tracked(cause),id);
        proof {if let Ok(Some(ref dispatch))=out {history.record(before,self.cleanup_state().queues()[id],dispatch);} else {
            self.cleanup_state().queues()[id].unchanged_slots(&before);
        }}
        out
    }
}
}

pub mod release;

pub mod lifecycle;
