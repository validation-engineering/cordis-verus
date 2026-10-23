//! Lifecycle ownership of erased cleanup histories. The core cannot be mutably
//! borrowed, so every supported mutation maintains its actual queue boundary.
use super::{Action, History, Owner};
#[cfg(verus_keep_ghost)]
use crate::cleanup_groups::drained;
use crate::cleanup_groups::payload::DispatchResult;
use crate::cleanup_journal::{RestoreError, RestoreTicket};
use crate::cleanup_queue::CleanupQueue;
use crate::reversible_value::managed::Slot;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
type Queue<A,R,T,M,X> = CleanupQueue<Action<A,R,T,M,X>>;
type Histories<A,R,T,M,X> = Map<usize,History<A,R,T,M,X>>;
type Queues<A,R,T,M,X> = Map<usize,Queue<A,R,T,M,X>>;

/// An actual Execution with proof-only histories and terminal queue snapshots.
/// Attachment fixes the original registered prefix. Later registrations extend
/// its obligations; no mutable core escape can reset that prefix.
pub struct RecordedExecution<C,G,A,R,T:?Sized,M,X> {
    core:Owner<C,G,A,R,T,M,X>,
    #[allow(dead_code)]
    value_sources:Tracked<crate::reversible_value::history::sources::Sources<crate::reversible_value::payload::State<T>>>,
    #[allow(dead_code)]
    baseline:Ghost<Owner<C,G,A,R,T,M,X>>,
    #[allow(dead_code)]
    histories:Tracked<Histories<A,R,T,M,X>>,
    #[allow(dead_code)]
    terminal:Ghost<Queues<A,R,T,M,X>>,
    #[allow(dead_code)]
    origins:Ghost<Queues<A,R,T,M,X>>,
    /// The last managed invocation return or cleanup acknowledgement. External
    /// observations still need their own source and completeness conditions.
    #[allow(dead_code)]
    recovery_boundary:Tracked<Option<crate::reversible_value::joint::Receipt>>,
}

proof fn initialize<A,R,T:?Sized,M,X>(queues:Queues<A,R,T,M,X>,upper:usize)->(tracked out:Histories<A,R,T,M,X>)
    requires forall|id:usize|#[trigger] queues.contains_key(id) ==> queues[id].wf(),
    ensures out.dom()==queues.dom().filter(|id:usize|id<upper),
        forall|id:usize|#[trigger] out.contains_key(id) ==> out[id].wf() && out[id].matches(queues[id]) && out[id].initial()==queues[id].slots() && out[id].events().len()==0 && out[id].host_turn(queues[id]),
    decreases upper,
{
    if upper==0 {Map::tracked_empty()} else {
        let id=(upper-1) as usize;
        let tracked mut out=initialize(queues,id);
        if queues.contains_key(id) {let tracked history=History::new(queues[id]);out.tracked_insert(id,history);}
        assert(out.dom() =~= queues.dom().filter(|key:usize|key<upper));
        out
    }
}

/// Append an authentic observation to the other owned queues without changing
/// their retained slots. Recursion is erased; it performs no runtime traversal.
proof fn observe_prefix<A,R,T:?Sized,M,X>(tracked histories:&mut Histories<A,R,T,M,X>,event:super::super::Event<A,R,T,M,X>,except:Option<usize>,upper:usize)
    requires event.source(),forall|id:usize|#[trigger] old(histories).contains_key(id) ==> old(histories)[id].wf(),
    ensures final(histories).dom()==old(histories).dom(),
        forall|id:usize|#[trigger] old(histories).contains_key(id) ==> {
            let before=old(histories)[id];let after=final(histories)[id];
            &&& after.wf() && after.initial()==before.initial() && after.current()==before.current() && after.link()==before.link() && after.domain()==before.domain()
            &&& after.events()==if id<upper && Some(id)!=except {before.events().push(event)} else {before.events()}
            &&& (id>=upper || Some(id)==except) ==> after==before
        },
    decreases upper,
{
    hide(super::super::Event::source);
    if upper>0 {
        let id=(upper-1) as usize;
        observe_prefix(histories,event,except,id);
        if histories.contains_key(id) && Some(id)!=except {
            let tracked mut history=histories.tracked_remove(id);
            history.foreign(event);
            histories.tracked_insert(id,history);
        }
    }
}

impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    pub closed spec fn value_sources(&self)->crate::reversible_value::history::sources::Sources<crate::reversible_value::payload::State<T>> {self.value_sources@}
    pub proof fn sources_witness(tracked &self)->(tracked out:&crate::reversible_value::history::sources::Sources<crate::reversible_value::payload::State<T>>)
        requires self.wf(),ensures *out==self.value_sources(),out.wf(),
    {self.facts();self.value_sources.borrow()}
    pub closed spec fn core(&self)->Owner<C,G,A,R,T,M,X> {self.core}
    pub closed spec fn baseline(&self)->Owner<C,G,A,R,T,M,X> {self.baseline@}
    pub closed spec fn histories(&self)->Histories<A,R,T,M,X> {self.histories@}
    pub closed spec fn terminal(&self)->Queues<A,R,T,M,X> {self.terminal@}
    pub closed spec fn origins(&self)->Queues<A,R,T,M,X> {self.origins@}
    pub closed spec fn recovery_boundary(&self)->Option<crate::reversible_value::joint::Receipt> {self.recovery_boundary@}
    pub proof fn recovery_boundary_witness(tracked &self)->(tracked out:&Option<crate::reversible_value::joint::Receipt>)
        ensures *out==self.recovery_boundary(),
    {self.recovery_boundary.borrow()}
    pub open spec fn recovery_boundary_valid(&self)->bool {
        self.recovery_boundary().is_some() ==> self.recovery_boundary().unwrap().wf()
            && self.core().execution_journal()==Some(self.recovery_boundary().unwrap().journal())
    }
    pub open spec fn entry(&self,id:usize)->bool {
        let h=self.histories()[id];let base=self.origins()[id];
        &&& self.sources_for_history(id)
        &&& h.wf() && h.starts_with(base.slots()) && h.current().len()==h.initial().len() && h.link()==base.link() && h.domain()==base.protocol().domain_id()
        &&& if self.core().cleanup_state().live(id) {
            !self.terminal().contains_key(id) && h.matches(self.core().cleanup_state().queues()[id]) && h.host_turn(self.core().cleanup_state().queues()[id])
        } else {
            self.terminal().contains_key(id) && h.matches(self.terminal()[id]) && drained(self.terminal()[id])
        }
    }
    #[verifier::opaque]
    pub open spec fn wf(&self)->bool {
        &&& self.core().wf() && self.baseline().wf() && self.recovery_boundary_valid() && self.value_sources().wf()
        &&& self.core().cleanup_state().link()==self.baseline().cleanup_state().link()
        &&& self.core().origin()==self.baseline().origin()
        &&& self.histories().dom()==self.origins().dom()
        &&& self.baseline().cleanup_state().queues().dom().subset_of(self.origins().dom())
        &&& forall|id:usize|#[trigger] self.baseline().cleanup_state().queues().contains_key(id) ==> self.origins()[id]==self.baseline().cleanup_state().queues()[id]
        &&& forall|id:usize|#[trigger] self.histories().contains_key(id) ==> id<self.core().cleanup_state().next_id()
        &&& self.core().cleanup_state().queues().dom().subset_of(self.histories().dom())
        &&& self.terminal().dom().subset_of(self.histories().dom())
        &&& forall|id:usize|#[trigger] self.histories().contains_key(id) ==> self.entry(id)
    }
    pub proof fn facts(&self)
        requires self.wf(),
        ensures self.core().wf(),self.baseline().wf(),self.recovery_boundary_valid(),self.value_sources().wf(),self.core().origin()==self.baseline().origin(),
            self.core().cleanup_state().link()==self.baseline().cleanup_state().link(),
            self.histories().dom()==self.origins().dom(),
            self.baseline().cleanup_state().queues().dom().subset_of(self.origins().dom()),
            forall|id:usize|#[trigger] self.baseline().cleanup_state().queues().contains_key(id) ==> self.origins()[id]==self.baseline().cleanup_state().queues()[id],
            forall|id:usize|#[trigger] self.histories().contains_key(id) ==> id<self.core().cleanup_state().next_id(),
            self.core().cleanup_state().queues().dom().subset_of(self.histories().dom()),
            self.terminal().dom().subset_of(self.histories().dom()),
            forall|id:usize|#[trigger] self.histories().contains_key(id) ==> self.entry(id),
    {reveal(RecordedExecution::wf);}
    pub fn new(core:Owner<C,G,A,R,T,M,X>)->(out:Self)
        requires core.wf(),
        ensures out.wf(),out.core()==core,out.baseline()==core,out.terminal()==Map::empty(),out.recovery_boundary().is_none(),
            forall|id:usize|#[trigger] out.histories().contains_key(id) ==> out.histories()[id].events().len()==0,
    {
        let tracked histories=initialize(core.cleanup_state().queues(),core.cleanup_state().next_id());
        proof {assert(histories.dom() =~= core.cleanup_state().queues().dom());reveal(RecordedExecution::wf);}
        let tracked value_sources=crate::reversible_value::history::sources::Sources::new();
        Self {value_sources:Tracked(value_sources),baseline:Ghost(core),origins:Ghost(core.cleanup_state().queues()),core,histories:Tracked(histories),terminal:Ghost(Map::empty()),recovery_boundary:Tracked(None)}
    }
    /// Immutable inspection retains ownership of the mutation path.
    pub fn execution(&self)->(out:&Owner<C,G,A,R,T,M,X>) ensures *out==self.core(), {&self.core}
    pub proof fn history(tracked &self,id:usize)->(tracked out:&History<A,R,T,M,X>)
        requires self.wf(),self.histories().contains_key(id),
        ensures *out==self.histories()[id],out.wf(),
    {
        self.facts();let tracked histories=self.histories.borrow();histories.tracked_borrow(id)
    }
    pub fn dispatch(&mut self,id:usize)->(out:DispatchResult<A,R,std::sync::Arc<Slot<T,M>>,T,X>)
        requires old(self).wf(),old(self).core().cleanup_state().live(id),
        ensures old(self).conserved() ==> final(self).conserved(),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().from_slot(old(self).core().cleanup_state().queues()[id].slots())
                && out->Ok_0.unwrap().finished(old(self).core().cleanup_state().queues()[id],final(self).core().cleanup_state().queues()[id]),
            final(self).source_order_extends(old(self)),final(self).value_sources().extends(old(self).value_sources()),final(self).wf(),final(self).origins()==old(self).origins(),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed() ==> out->Ok_0.unwrap().carrier().covered(final(self).value_sources()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed() ==> out->Ok_0.unwrap().authentic()
                && out->Ok_0.unwrap().queue_link()==old(self).histories()[id].link(),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==> final(self).histories()[group].initial()==old(self).histories()[group].initial(),
            old(self).recovery_boundary().is_some() ==> final(self).recovery_boundary().is_some()
                && final(self).recovery_boundary().unwrap().covers(&old(self).recovery_boundary().unwrap()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed() ==> out->Ok_0.unwrap().follows_boundary(old(self).recovery_boundary()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed() && old(self).core().execution_journal().is_some() ==>
                final(self).recovery_boundary().is_some() && final(self).recovery_boundary().unwrap().same(&out->Ok_0.unwrap().acknowledgement().unwrap()),
            !(out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed()) ==> final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).baseline()==old(self).baseline(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            final(self).core().cleanup_state().live(id),
            final(self).histories()[id].events()==if out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed()
                {old(self).histories()[id].events().push(super::super::Event::Managed(out->Ok_0.unwrap()))} else {old(self).histories()[id].events()},
            forall|other:usize|other!=id && #[trigger] old(self).histories().contains_key(other) ==> final(self).histories()[other].events()==
                if out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed()
                {old(self).histories()[other].events().push(super::super::Event::Managed(out->Ok_0.unwrap()))} else {old(self).histories()[other].events()},
    {
        let ghost prior=*self;
        proof {self.facts();}
        let tracked mut history=self.histories.borrow_mut().tracked_remove(id);
        let tracked cause=match self.recovery_boundary.borrow() {Some(receipt)=>Some(receipt.duplicate()),None=>None};
        let ghost original=self.recovery_boundary();
        let out=self.core.dispatch_recorded_following(Tracked(cause),id,Tracked(&mut history));
        proof {
            self.histories.borrow_mut().tracked_insert(id,history);
            if let Ok(Some(ref dispatch))=out {if dispatch.managed() {
                self.value_sources.borrow_mut().retain_dispatch(dispatch);
                let upper=self.core().cleanup_state().next_id();
                observe_prefix(self.histories.borrow_mut(),super::super::Event::Managed(*dispatch),Some(id),upper);
                if self.core().execution_journal().is_some() {
                    dispatch.acknowledgement_records();
                    self.recovery_boundary=Tracked(dispatch.acknowledgement_receipt());
                }
                assert(dispatch.follows_boundary(original));
            }}
            if self.recovery_boundary()==original && original.is_some() {
                assert(original.unwrap().events().take(original.unwrap().events().len() as int) =~= original.unwrap().events());
            }
            assert(self.core().wf());
            assert(self.recovery_boundary_valid());
            assert forall|group:usize|#[trigger] self.histories().contains_key(group) implies self.entry(group) by {};
            reveal(RecordedExecution::wf);
            let suffix=if out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().managed()
                {seq![super::super::Event::Managed(out->Ok_0.unwrap())]} else {Seq::empty()};
            if prior.recovery_boundary().is_some() && super::super::sources::order::local(suffix,prior.recovery_boundary().unwrap().journal()) {
                if let Ok(Some(ref dispatch))=out {if dispatch.managed() {
                    assert(suffix[0]==super::super::Event::Managed(*dispatch));
                    assert(suffix[0].checkpoint().journal()==prior.recovery_boundary().unwrap().journal());
                    dispatch.source_order(prior.recovery_boundary().unwrap(),self.recovery_boundary().unwrap());
                }}
            }
            assert forall|group:usize|#[trigger] prior.histories().contains_key(group) implies
                self.histories()[group].events()==prior.histories()[group].events()+suffix by {
                assert(self.histories()[group].events() =~= prior.histories()[group].events()+suffix);
            }
            self.extend_source_order(&prior,suffix);
            if prior.conserved() {
                assert forall|group:usize,i:int|self.histories().contains_key(group)
                    && 0<=i<self.histories()[group].current().len() && (#[trigger] self.histories()[group].current()[i]).is_some() implies
                        i<self.histories()[group].initial().len() && self.histories()[group].current()[i]==self.histories()[group].initial()[i] by {
                    if group==id {
                        if let Ok(Some(ref dispatch))=out {
                            assert(dispatch.finished(prior.core().cleanup_state().queues()[id],self.core().cleanup_state().queues()[id]));
                        }
                    }
                    assert(prior.histories()[group].current()[i].is_some());
                }
            }

        }
        out
    }
    /// The production effect allocator creates the group and queued request.
    /// Its actual empty queue becomes the new group's permanent origin.
    pub fn enqueue_effect(&mut self,source:usize,domain:u64,committed:Vec<crate::Binding>,payload:G)->(out:Result<usize,(Vec<crate::Binding>,G)>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).terminal()==old(self).terminal(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==(committed,payload),
            out.is_ok() ==> !old(self).histories().contains_key(out->Ok_0)
                && out->Ok_0==old(self).core().cleanup_state().next_id()
                && final(self).origins()==old(self).origins().insert(out->Ok_0,final(self).core().cleanup_state().queues()[out->Ok_0])
                && final(self).histories().dom()==old(self).histories().dom().insert(out->Ok_0)
                && final(self).histories()[out->Ok_0].initial().len()==0
                && final(self).histories()[out->Ok_0].events().len()==0,
            forall|id:usize|#[trigger] old(self).histories().contains_key(id) ==> final(self).histories()[id]==old(self).histories()[id],
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}
        let out=self.core.enqueue_effect(source,domain,committed,payload);
        proof {if let Ok(id)=out {
            let queue=self.core.cleanup_state().queues()[id];
            self.origins=Ghost(self.origins@.insert(id,queue));
            let tracked history=History::new(queue);self.histories.borrow_mut().tracked_insert(id,history);
        }reveal(RecordedExecution::wf);}
        out
    }
    /// Late registration extends the same token obligations; prior consumption
    /// evidence and the original function-return prefix are never reset.
    pub fn register(&mut self,id:usize,action:Action<A,R,T,M,X>)->(out:Result<usize,Action<A,R,T,M,X>>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),out.is_ok()==old(self).core().cleanup_state().live(id),
            out.is_err() ==> out->Err_0==action && final(self).histories()==old(self).histories(),
            out.is_ok() ==> out->Ok_0==old(self).histories()[id].initial().len()
                && final(self).histories()[id].initial()==old(self).histories()[id].initial().push(Some(action))
                && final(self).histories()[id].events()==old(self).histories()[id].events(),
            forall|other:usize|other!=id && #[trigger] old(self).histories().contains_key(other) ==> final(self).histories()[other]==old(self).histories()[other],
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}
        let ghost before=*self;
        let out=self.core.register(id,action);
        proof {if out.is_ok() {
            let tracked mut history=self.histories.borrow_mut().tracked_remove(id);let ghost prior=history;
            assert(before.entry(id));assert(history.matches(before.core().cleanup_state().queues()[id]));
            assert(self.core.cleanup_state().queues()[id].slots()==history.current().push(Some(action)));
            assert(self.core.cleanup_state().queues()[id].slots().take(history.current().len() as int) =~= history.current());
            history.extend(self.core.cleanup_state().queues()[id]);
            history.prefix_transitive(prior,self.origins()[id].slots());
            self.histories.borrow_mut().tracked_insert(id,history);
        }reveal(RecordedExecution::wf);}
        out
    }
    pub fn retry(&mut self,id:usize)->(out:Result<RestoreTicket,RestoreError>)
        requires old(self).wf(),old(self).core().cleanup_state().live(id),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),final(self).core().cleanup_state().live(id),
            final(self).histories()[id].events()==old(self).histories()[id].events(),
            out.is_ok()==old(self).core().cleanup_state().queues()[id].retry_enabled(),
            out.is_ok() ==> out->Ok_0.token==old(self).core().cleanup_state().queues()[id].protocol().selected().unwrap().token
                && out->Ok_0.attempt>old(self).core().cleanup_state().queues()[id].protocol().selected().unwrap().attempt,
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}
        let tracked mut history=self.histories.borrow_mut().tracked_remove(id);
        let out=self.core.retry_recorded(id,Tracked(&mut history));
        proof {self.histories.borrow_mut().tracked_insert(id,history);reveal(RecordedExecution::wf);}
        out
    }
    /// Record an authentic external write/restore. This does not establish that
    /// the observation is exhaustive or ordered: the linked trajectory theorem
    /// continues to check those source conditions.
    pub proof fn observe_foreign(tracked &mut self,event:super::super::Event<A,R,T,M,X>)
        requires old(self).wf(),event.source(),event.carrier().covered(old(self).value_sources()),
        ensures final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).origins()==old(self).origins(),
            forall|id:usize|#[trigger] old(self).histories().contains_key(id) ==> final(self).histories()[id].initial()==old(self).histories()[id].initial()
                && final(self).histories()[id].current()==old(self).histories()[id].current(),
            final(self).wf(),final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|id:usize|#[trigger] old(self).histories().contains_key(id) ==> final(self).histories()[id].events()==old(self).histories()[id].events().push(event),
    {
        self.facts();let upper=self.core().cleanup_state().next_id();
        observe_prefix(self.histories.borrow_mut(),event,None,upper);
        reveal(RecordedExecution::wf);
    }
    /// Early group removal keeps its actual drained boundary after storage is
    /// gone. Rejected removal cannot manufacture a terminal observation.
    pub fn remove(&mut self,id:usize)->(out:bool)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).histories()==old(self).histories(),
            final(self).terminal()==if out {old(self).terminal().insert(id,old(self).core().cleanup_state().queues()[id])} else {old(self).terminal()},
            out ==> !final(self).core().cleanup_state().live(id) && final(self).terminal().contains_key(id),
            !out ==> *final(self)==*old(self),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}
        let (removed,_terminal)=self.core.remove_observed(id);
        proof {if removed {self.terminal=Ghost(self.terminal@.insert(id,_terminal@.unwrap()));}reveal(RecordedExecution::wf);}
        removed
    }
}
}

pub mod native;

pub mod recovery;

pub mod callbacks;

pub mod work;

pub mod children;

pub mod function;

pub mod observer;

pub mod sources;

pub mod values;

pub mod order;

pub mod producer_capture;
pub mod producer_recovery;

pub mod unload_census;

pub mod deletion_capture;
pub mod unload_capture;

pub mod unload_client;

pub mod host;
