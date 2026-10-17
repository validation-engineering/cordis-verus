//! A common linearization point for the checked native execution domain.
//! The lock orders real mutations; maps, trace and ownership tokens are erased.
//! A foreign object remains an explicit external reference, never a guessed value.
use super::history::{Authority, Witness};
use super::{Event, ValueState};
use crate::refinement as r;
use std::sync::Arc;
use vstd::prelude::*;
use vstd::resource::map::{GhostMapAuth, GhostPointsTo};
use vstd::resource::Loc;
use vstd::rwlock::{ReadHandle, RwLock, RwLockPredicate, WriteHandle};

verus! {
pub struct Object {pub domain:Loc,pub key:nat}
#[allow(inconsistent_fields)]
pub enum Record {
    Object {source:Loc,state:ValueState},
    Slot {source:Loc,revision:u64,object:Object},
    Payload {source:Loc,revision:u64},
    RetiredPayload {source:Loc,revision:u64},
    Native {state:native::State},
    Recipes {state:recipes::State},
    Configuration {state:configuration::State},
    Sources {state:sources::State},
    Work {state:episode::WorkState},
    Cleanup {state:episode::CleanupState},
    Groups {state:groups::State},
    Host {state:host::State},
    Control {state:control::State},
}
#[allow(inconsistent_fields)]
pub enum Change {Allocate,Sources {event:sources::Event},Configuration {event:configuration::Event},Recipes {event:recipes::Event},Control {event:control::Event},Host {event:host::Event},Value {event:Event},Replace,PayloadReplace,PayloadApply,PayloadRestore,PayloadRetire,Native {actor:usize,rule:r::Rule},
    Work {event:episode::WorkChange},Cleanup {event:episode::CleanupChange},Groups {event:groups::Event},RegisterInverse {write:nat}}
#[verifier::opaque]
pub open spec fn changes(before:Record,after:Record,change:Change)->bool {
    match (before,after,change) {
        (Record::Object {source:a,state:x},Record::Object {source:b,state:y},Change::Value {event})=>
            a==b && event.valid() && event.before()==x && event.after()==y,
        (Record::Slot {source:a,revision:x,..},Record::Slot {source:b,revision:y,..},Change::Replace)=>
            a==b && x<u64::MAX && y==x+1,
        (Record::Payload {source:a,revision:x},Record::Payload {source:b,revision:y},Change::PayloadReplace|Change::PayloadApply|Change::PayloadRestore)=>
            a==b && x<u64::MAX && y==x+1,
        (Record::Payload {source:a,revision:x},Record::RetiredPayload {source:b,revision:y},Change::PayloadRetire)=>
            a==b && y==x,
        (Record::Sources {state:a},Record::Sources {state:b},Change::Sources {event})=>sources::step(a,b,event),
        (Record::Configuration {state:a},Record::Configuration {state:b},Change::Configuration {event})=>configuration::step(a,b,event),
        (Record::Recipes {state:a},Record::Recipes {state:b},Change::Recipes {event})=>recipes::step(a,b,event),
        (Record::Native {state:x},Record::Native {state:y},Change::Native {actor,rule})=>native::step(x,y,actor,rule),
        (Record::Work {state:a},Record::Work {state:b},Change::Work {event})=>episode::work_step(a,b,event),
        (Record::Cleanup {state:a},Record::Cleanup {state:b},Change::Cleanup {event})=>episode::cleanup_step(a,b,event),
        (Record::Groups {state:a},Record::Groups {state:b},Change::Groups {event})=>groups::step(a,b,event),
        (Record::Host {state:a},Record::Host {state:b},Change::Host {event})=>host::step(a,b,event),
        (Record::Control {state:a},Record::Control {state:b},Change::Control {event})=>control::step(a,b,event),
        (Record::Cleanup {state:a},Record::Cleanup {state:b},Change::RegisterInverse {..})=>episode::cleanup_step(a,b,episode::CleanupChange::Register),
        _=>false,
    }
}
pub struct Step {pub key:nat,pub change:Change,pub after:Record,
    pub pending:bool,pub settled:Option<nat>}
/// Unregistered inverses of managed writes in this execution domain. The
/// linear capability is held by the actual Applied/Batch until registration.
/// This is not a census of arbitrary raw API values or of OS resources.
#[allow(dead_code)]
pub tracked struct Pending {ghost journal:Journal,point:GhostPointsTo<nat,nat>}
impl Pending {
    pub closed spec fn journal(&self)->Journal {self.journal}
    pub closed spec fn at(&self)->nat {self.point.key()}
    pub closed spec fn object(&self)->nat {self.point.value()}
    pub closed spec fn wf(&self)->bool {self.point.id()==self.journal.inner.pred().pending}
}
pub open spec fn pending_index(p:Option<Pending>)->Option<nat> {match p {Some(p)=>Some(p.at()),None=>None}}
pub open spec fn pending_matches(p:Option<Pending>,journal:Journal,key:nat,at:nat,enabled:bool)->bool {
    p.is_some()==enabled && (p.is_some() ==> p.unwrap().wf() && p.unwrap().journal()==journal
        && p.unwrap().object()==key && p.unwrap().at()==at)
}
pub open spec fn registration_pending(p:Option<Pending>,cause:Option<Receipt>,link:Option<(Journal,nat)>)->bool {
    p.is_some() ==> p.unwrap().wf() && link.is_some() && p.unwrap().journal()==link.unwrap().0
        && cause.is_some() && cause.unwrap().wf() && cause.unwrap().forward()
        && cause.unwrap().journal()==p.unwrap().journal() && cause.unwrap().at()==p.unwrap().at()
        && cause.unwrap().event().key==p.unwrap().object()
}
pub open spec fn local(link:Option<(Journal,nat)>,journal:Journal)->bool {link.is_some() && link.unwrap().0==journal}
proof fn existing_change(before:Record,after:Record,change:Change)
    requires changes(before,after,change),ensures change!=Change::Allocate,
{reveal(changes);}
pub open spec fn guard(state:Map<nat,Record>,before:Record,change:Change)->bool {
    match change {Change::Sources {event}=>before is Sources && sources::guard(state,before->Sources_state,event),
        Change::Recipes {event}=>before is Recipes && recipes::guard(state,before->Recipes_state,event),
        Change::Host {event}=>before is Host && host::guard(state,before->Host_state,event),
        Change::Control {event}=>before is Control && control::guard(state,before->Control_state,event),
        _=>groups::guard(state,before,change)}
}
pub open spec fn step(before:Map<nat,Record>,after:Map<nat,Record>,event:Step)->bool {
    after==before.insert(event.key,event.after) && match event.change {
        Change::Allocate=>!before.contains_key(event.key),
        _=>before.contains_key(event.key) && changes(before[event.key],event.after,event.change)
            && guard(before,before[event.key],event.change),
    }
}
pub struct Frame {pub event:Step,pub state:Map<nat,Record>,pub pending:Map<nat,nat>}
pub open spec fn state_at(events:Seq<Frame>,n:nat)->Map<nat,Record> {
    if n==0 {Map::empty()} else {events[n-1].state}
}
pub open spec fn forward(step:Step)->bool {
    match step.change {Change::PayloadApply=>true,Change::Value {event}=>event.valid() && (event is Forward || event is Computed),_=>false}
}
/// A same-domain registration names a real earlier forward operation. Other
/// rules, including external-domain registration, make no such assertion.
pub open spec fn caused(events:Seq<Frame>,step:Step)->bool {
    match step.change {Change::RegisterInverse {write}=>write<events.len() && forward(events[write as int].event),_=>true}
}
pub open spec fn pending_at(events:Seq<Frame>,n:nat)->Map<nat,nat> {
    if n==0 {Map::empty()} else {events[n-1].pending}
}
pub open spec fn pending_step(before:Map<nat,nat>,after:Map<nat,nat>,event:Step,index:nat)->bool {
    if event.pending {
        forward(event) && event.settled.is_none() && !before.contains_key(index) && after==before.insert(index,event.key)
    } else if event.settled.is_some() {
        let at=event.settled.unwrap();
        event.change==(Change::RegisterInverse {write:at}) && before.contains_key(at) && after==before.remove(at)
    } else {after==before}
}
pub open spec fn valid(events:Seq<Frame>)->bool {
    &&& forall|i:int| 0<=i<events.len() ==> step(state_at(events,i as nat),#[trigger] events[i].state,events[i].event)
        && caused(events.take(i),events[i].event)
        && pending_step(pending_at(events,i as nat),events[i].pending,events[i].event,i as nat)
    &&& forall|i:int,k:nat| 0<=i<events.len() && #[trigger] events[i].pending.contains_key(k) ==> k<=i
}
/// Journal entries are allocated once and never removed. Retired ownership
/// lives in the record's state, so its allocation has no earlier same-key event.
pub proof fn key_persists(frames:Seq<Frame>,start:nat,end:nat,key:nat)
    requires valid(frames),start<=end<=frames.len(),state_at(frames,start).contains_key(key),
    ensures state_at(frames,end).contains_key(key),
    decreases end-start,
{
    if start<end {
        key_persists(frames,start,(end-1) as nat,key);
        assert(step(state_at(frames,(end-1) as nat),frames[end-1].state,frames[end-1].event));
    }
}
/// Every observed record was installed by an actual earlier event in this trace.
pub proof fn record_origin(frames:Seq<Frame>,end:nat,key:nat)->(at:nat)
    requires valid(frames),end<=frames.len(),state_at(frames,end).contains_key(key),
    ensures at<end,frames[at as int].event.key==key,frames[at as int].event.after==state_at(frames,end)[key],
    decreases end,
{
    assert(end>0);let n=(end-1) as nat;
    assert(step(state_at(frames,n),frames[n as int].state,frames[n as int].event));
    if frames[n as int].event.key==key {n} else {record_origin(frames,n,key)}
}
#[verifier::rlimit(20)]
pub proof fn append(events:Seq<Frame>,event:Step,next:Map<nat,Record>,pending:Map<nat,nat>)
    requires valid(events),step(state_at(events,events.len()),next,event),caused(events,event),
        pending_step(pending_at(events,events.len()),pending,event,events.len()),
    ensures valid(events.push(Frame {event,state:next,pending})),
{
    let added=Frame {event,state:next,pending};
    assert forall|i:int| 0<=i<events.push(added).len() implies
        step(state_at(events.push(added),i as nat),#[trigger] events.push(added)[i].state,events.push(added)[i].event)
            && caused(events.push(added).take(i),events.push(added)[i].event)
            && pending_step(pending_at(events.push(added),i as nat),events.push(added)[i].pending,events.push(added)[i].event,i as nat) by {
        if i<events.len() {assert(events.push(added).take(i) =~= events.take(i));}
        else {assert(events.push(added).take(i) =~= events);}
    }
    assert forall|i:int,k:nat| 0<=i<events.push(added).len() && #[trigger] events.push(added)[i].pending.contains_key(k) implies k<=i by {
        if i==events.len() && k!=events.len() {
            assert(pending_at(events,events.len()).contains_key(k));
            if events.len()>0 {assert(events.last().pending.contains_key(k));}
        }
    }
}
proof fn pending_back(events:Seq<Frame>,write:nat,start:nat,until:nat)
    requires valid(events),write<start<=until<=events.len(),pending_at(events,until).contains_key(write),
    ensures pending_at(events,start).contains_key(write),pending_at(events,start)[write]==pending_at(events,until)[write],
    decreases until-start,
{
    if start<until {
        let i=(until-1) as int;
        assert(step(state_at(events,i as nat),events[i].state,events[i].event));
        assert(pending_step(pending_at(events,i as nat),events[i].pending,events[i].event,i as nat));
        assert(write<i);
        assert(pending_at(events,i as nat).contains_key(write));
        assert(pending_at(events,i as nat)[write]==pending_at(events,until)[write]);
        pending_back(events,write,start,i as nat);
    }
}
/// A pending entry cannot disappear and later reappear: only its own forward
/// index may create it. This exposes every intervening state, not just endpoints.
pub proof fn pending_since(events:Seq<Frame>,write:nat,until:nat)
    requires valid(events),until<=events.len(),pending_at(events,until).contains_key(write),
    ensures write<until,events[write as int].event.pending,forward(events[write as int].event),
        forall|n:nat| write<n<=until ==> #[trigger] pending_at(events,n).contains_pair(write,events[write as int].event.key),
{
    assert(until>0);
    assert(events[until-1].pending.contains_key(write));
    assert(write<until);
    pending_back(events,write,write+1,until);
    assert(step(state_at(events,write),events[write as int].state,events[write as int].event));
    if write>0 {assert(!events[write-1].pending.contains_key(write));}
    assert(!pending_at(events,write).contains_key(write));
    assert(events[write as int].event.pending);
    assert(pending_at(events,until)[write]==events[write as int].event.key);
    assert forall|n:nat| write<n<=until implies #[trigger] pending_at(events,n).contains_pair(write,events[write as int].event.key) by {
        pending_back(events,write,n,until);
    }
}
/// Ordered positions of one real object's local operations in this domain.
/// Once an earlier write is absent, it cannot reappear under arbitrary
/// interleavings. Only the write's own index can create its pending entry.
pub proof fn pending_absent_later(frames:Seq<Frame>,write:nat,start:nat,end:nat)
    requires valid(frames),write<start<=end<=frames.len(),!pending_at(frames,start).contains_key(write),
    ensures forall|n:nat| start<=n<=end ==> !#[trigger] pending_at(frames,n).contains_key(write),
{
    assert forall|n:nat| start<=n<=end implies !#[trigger] pending_at(frames,n).contains_key(write) by {
        if pending_at(frames,n).contains_key(write) {pending_back(frames,write,start,n);}
    }
}
/// A managed forward obligation can be consumed by only one real commit.
pub proof fn unique_settlement(frames:Seq<Frame>,first:nat,second:nat,write:nat)
    requires valid(frames),first<frames.len(),second<frames.len(),
        frames[first as int].event.settled==Some(write),frames[second as int].event.settled==Some(write),
    ensures first==second,
{
    assert(step(state_at(frames,first),frames[first as int].state,frames[first as int].event));
    assert(step(state_at(frames,second),frames[second as int].state,frames[second as int].event));
    assert(pending_step(pending_at(frames,first),frames[first as int].pending,frames[first as int].event,first));
    assert(pending_step(pending_at(frames,second),frames[second as int].pending,frames[second as int].event,second));
    // Settled and newly-created obligations are mutually exclusive.
    assert(!frames[first as int].event.pending && !frames[second as int].event.pending);
    assert(caused(frames.take(first as int),frames[first as int].event));
    assert(caused(frames.take(second as int),frames[second as int].event));
    if first<second {pending_absent_later(frames,write,first+1,second);}
    if second<first {pending_absent_later(frames,write,second+1,first);}
}

pub open spec fn indexed(events:Seq<Event>,positions:Seq<nat>,frames:Seq<Frame>,key:nat)->bool {
    &&& positions.len()==events.len()
    &&& forall|i:int| 0<=i<events.len() ==> #[trigger] positions[i]<frames.len()
        && frames[positions[i] as int].event.key==key && frames[positions[i] as int].event.change==(Change::Value {event:events[i]})
    &&& forall|i:int,j:int| 0<=i<j<events.len() ==> #[trigger] positions[i]<#[trigger] positions[j]
}
pub proof fn extend_indexed(events:Seq<Event>,positions:Seq<nat>,before:Seq<Frame>,after:Seq<Frame>,key:nat)
    requires indexed(events,positions,before,key),before.len()<=after.len(),after.take(before.len() as int)==before,
    ensures indexed(events,positions,after,key),
{
    assert forall|i:int| 0<=i<events.len() implies #[trigger] positions[i]<after.len()
        && after[positions[i] as int].event.key==key && after[positions[i] as int].event.change==(Change::Value {event:events[i]}) by {
        assert(after[positions[i] as int]==before[positions[i] as int]);
    }
}
pub proof fn append_indexed(events:Seq<Event>,positions:Seq<nat>,before:Seq<Frame>,after:Seq<Frame>,key:nat,event:Event)
    requires indexed(events,positions,before,key),before.len()<after.len(),after.take(before.len() as int)==before,
        after.last().event.key==key,after.last().event.change==(Change::Value {event}),
    ensures indexed(events.push(event),positions.push((after.len()-1) as nat),after,key),
{
    extend_indexed(events,positions,before,after,key);
    let next=positions.push((after.len()-1) as nat);
    assert forall|i:int,j:int| 0<=i<j<events.push(event).len() implies #[trigger] next[i]<#[trigger] next[j] by {
        if j==events.len() {assert(positions[i]<before.len());}
    }
}

#[allow(dead_code)]
struct Cell {auth:Tracked<GhostMapAuth<nat,Record>>,history:Tracked<Authority<Frame>>,pending:Tracked<GhostMapAuth<nat,nat>>,next:Ghost<nat>}
impl Cell {
    spec fn wf(&self)->bool {
        self.history@.wf() && valid(self.history@.events())
            && references::history(self.history@.events(),self.history@.source())
            && state_at(self.history@.events(),self.history@.events().len())==self.auth@@
            && pending_at(self.history@.events(),self.history@.events().len())==self.pending@@
            && forall|key:nat| #[trigger] self.auth@@.contains_key(key) <==> key<self.next@
    }
    proof fn transfer(tracked &mut self,journal:Journal,event:Step,tracked pending:Option<Pending>)->(tracked out:Option<Pending>)
        requires valid(old(self).history@.events()),old(self).pending@.id()==journal.inner.pred().pending,
            old(self).pending@@==pending_at(old(self).history@.events(),old(self).history@.events().len()),
            event.pending ==> forward(event) && pending.is_none(),
            event.settled==pending_index(pending),
            pending.is_some() ==> pending.unwrap().wf() && pending.unwrap().journal()==journal
                && event.change==(Change::RegisterInverse {write:pending.unwrap().at()}),
        ensures final(self).history==old(self).history,final(self).auth==old(self).auth,final(self).next==old(self).next,
            final(self).pending@.id()==old(self).pending@.id(),
            pending_step(old(self).pending@@,final(self).pending@@,event,old(self).history@.events().len()),
            pending_matches(out,journal,event.key,old(self).history@.events().len(),event.pending),
    {
        let at=self.history@.events().len();
        if event.pending {
            if at>0 {assert forall|k:nat| self.pending@@.contains_key(k) implies k<at by {
                assert(self.history@.events()[at-1].pending.contains_key(k));
            }}
            let tracked point=self.pending.borrow_mut().insert(at,event.key);
            Some(Pending {journal,point})
        } else {
            if let Some(debt)=pending {
                debt.point.agree(self.pending.borrow());
                self.pending.borrow_mut().delete_points_to(debt.point);
            }
            None
        }
    }
    proof fn record(tracked &mut self,event:Step,prior:Map<nat,Record>)
        requires old(self).history@.wf(),valid(old(self).history@.events()),
            references::history(old(self).history@.events(),old(self).history@.source()),
            references::linked(prior,event.after,old(self).history@.source()),
            state_at(old(self).history@.events(),old(self).history@.events().len())==prior,
            step(prior,old(self).auth@@,event),caused(old(self).history@.events(),event),
            pending_step(pending_at(old(self).history@.events(),old(self).history@.events().len()),old(self).pending@@,event,old(self).history@.events().len()),
        ensures final(self).history@.wf(),valid(final(self).history@.events()),
            references::history(final(self).history@.events(),final(self).history@.source()),
            state_at(final(self).history@.events(),final(self).history@.events().len())==final(self).auth@@,
            final(self).history@.source()==old(self).history@.source(),
            final(self).auth==old(self).auth,final(self).pending==old(self).pending,final(self).next==old(self).next,
            final(self).history@.events()==old(self).history@.events().push(Frame {event,state:final(self).auth@@,pending:final(self).pending@@}),
    {
        references::append(self.history@.events(),Frame {event,state:self.auth@@,pending:self.pending@@},self.history@.source());
        append(self.history@.events(),event,self.auth@@,self.pending@@);
        self.history.borrow_mut().append(Frame {event,state:self.auth@@,pending:self.pending@@});
    }
}
#[allow(dead_code)]
struct Predicate {source:Loc,history:Loc,pending:Loc}
impl RwLockPredicate<Cell> for Predicate {
    closed spec fn inv(self,cell:Cell)->bool {cell.wf() && cell.auth@.id()==self.source && cell.history@.source()==self.history && cell.pending@.id()==self.pending}
}
/// Share this domain with native lifecycle and newly allocated values. No
/// callback runs under this lock, and it never acquires a value or slot lock.
pub struct Journal {inner:Arc<RwLock<Cell,Predicate>>}
impl Clone for Journal {
    fn clone(&self)->(out:Self) ensures out==*self, {Self {inner:self.inner.clone()}}
}
/// One held read epoch used only inside checked owners. No payload callback,
/// destructor or value/slot lock may be entered while this guard is held.
pub(crate) struct ReadView<'a> {journal:&'a Journal,guard:ReadHandle<'a,Cell,Predicate>}
impl<'a> ReadView<'a> {
    pub closed spec fn journal_spec(&self)->Journal {*self.journal}
    pub closed spec fn state(&self)->Map<nat,Record> {self.guard.view().auth@@}
    pub closed spec fn events(&self)->Seq<Frame> {self.guard.view().history@.events()}
    pub closed spec fn wf(&self)->bool {
        self.guard.rwlock()==*self.journal.inner && self.guard.view().wf()
            && self.guard.view().auth@.id()==self.journal.inner.pred().source
            && self.guard.view().history@.source()==self.journal.inner.pred().history
    }
    pub(crate) fn certify_history(&self,_earlier:&Snapshot)
        requires self.wf(),_earlier.certified(),_earlier.journal_spec()==self.journal_spec(),
        ensures _earlier.domain()==self.journal_spec().source(),_earlier.events().len()<=self.events().len(),self.events().take(_earlier.events().len() as int)==_earlier.events(),
    {
        let _cell=self.guard.borrow();
        proof {_cell.history.borrow().extends(_earlier.witness.borrow());}
    }
    /// Borrow already collected receipts after taking the Journal lock. The
    /// caller must collect them before this epoch; no slot lock is taken here.
    pub(crate) fn certify_receipts<K>(&self,Tracked(receipts):Tracked<&Map<K,Receipt>>)
        requires self.wf(),forall|k:K| receipts.contains_key(k) ==> #[trigger] receipts[k].wf(),
        ensures forall|k:K| receipts.contains_key(k) && #[trigger] receipts[k].journal()==self.journal_spec() ==>
            receipts[k].events().len()<=self.events().len()
                && self.events().take(receipts[k].events().len() as int)==receipts[k].events(),
    {
        let _cell=self.guard.borrow();
        proof {
            receipts_included(_cell.history.borrow(),receipts,receipts.dom(),self.journal_spec());
        }
    }
    pub(crate) fn valid_history(&self)
        requires self.wf(),ensures valid(self.events()),references::history(self.events(),self.journal_spec().source()),
            state_at(self.events(),self.events().len())==self.state(),
    {let _cell=self.guard.borrow();}
    pub(crate) fn finish(self)->(out:Snapshot)
        requires self.wf(),
        ensures out.certified(),out.journal_spec()==self.journal_spec(),out.domain()==self.journal_spec().source(),out.events()==self.events(),out.last()==self.state(),
    {
        let _cell=self.guard.borrow();
        let tracked witness=_cell.history.borrow().snapshot();
        self.guard.release_read();Snapshot {journal:self.journal.clone(),witness:Tracked(witness)}
    }
}
proof fn receipts_included<K>(tracked authority:&Authority<Frame>,tracked receipts:&Map<K,Receipt>,keys:Set<K>,journal:Journal)
    requires authority.wf(),authority.source()==journal.inner.pred().history,keys.subset_of(receipts.dom()),
        forall|k:K| receipts.contains_key(k) ==> #[trigger] receipts[k].wf(),
    ensures forall|k:K| keys.contains(k) && #[trigger] receipts[k].journal()==journal ==>
        receipts[k].events().len()<=authority.events().len()
            && authority.events().take(receipts[k].events().len() as int)==receipts[k].events(),
    decreases keys.len(),
{
    if !keys.is_empty() {
        let k=keys.choose();
        assert(keys.contains(k));assert(receipts.contains_key(k));assert(receipts[k].wf());
        let tracked receipt=receipts.tracked_borrow(k);
        if receipt.journal()==journal {authority.extends(&receipt.witness);}
        receipts_included(authority,receipts,keys.remove(k),journal);
    }
}
/// Authenticate a local target against this held trace authority. Foreign
/// domains are explicitly retained, with no assertion about their current value.
proof fn certify_reference(tracked authority:&Authority<Frame>,record:Record,tracked receipt:&Option<Receipt>)
    requires authority.wf(),valid(authority.events()),references::evidence(record,*receipt),
    ensures references::linked(state_at(authority.events(),authority.events().len()),record,authority.source()),
{
    if record is Slot {
        let object=record->Slot_object;
        if object.domain==authority.source() {
            if let Some(ref target)=*receipt {
                authority.extends(&target.witness);
                let frames=authority.events();let i=target.at();
                assert(frames[i as int]==target.events()[i as int]);
                assert(step(state_at(frames,i),frames[i as int].state,frames[i as int].event));
                references::object_retained(frames,i+1,frames.len(),object.key);
            }
        }
    }
}
impl Journal {
    /// Include all earlier instruction witnesses, even across A/B/A domain
    /// alternation. Only local histories enter this real read checkpoint.
    pub(crate) fn join_receipts<K>(&self,Tracked(receipts):Tracked<&Map<K,Receipt>>,Tracked(first):Tracked<Option<Receipt>>)->(out:Tracked<Option<Receipt>>)
        requires first.is_some() ==> first.unwrap().wf(),forall|k:K|receipts.contains_key(k) ==> #[trigger] receipts[k].wf(),
        ensures out@.is_some() ==> out@.unwrap().wf() && out@.unwrap().journal()==*self,
            first.is_some() && first.unwrap().journal()==*self ==> out@.is_some() && out@.unwrap().covers(&first.unwrap()),
            forall|k:K|receipts.contains_key(k) && #[trigger] receipts[k].journal()==*self ==> out@.is_some() && out@.unwrap().covers(&receipts[k]),
    {
        let guard=self.inner.acquire_read();let _cell=guard.borrow();let tracked result;
        proof {
            receipts_included(_cell.history.borrow(),receipts,receipts.dom(),*self);
            if let Some(ref receipt)=first {if receipt.journal()==*self {_cell.history.borrow().extends(&receipt.witness);}}
            result=if _cell.history@.events().len()>0 {Some(Receipt {journal:*self,witness:_cell.history.borrow().snapshot()})} else {None};
            assert forall|k:K|receipts.contains_key(k) && #[trigger] receipts[k].journal()==*self implies result.is_some() && result.unwrap().covers(&receipts[k]) by {
                assert(receipts[k].wf());assert(receipts[k].events().len()>0);
            }
        }
        guard.release_read();Tracked(result)
    }
    /// Join two already acquired causes at the real journal read lock. This
    /// adds no event. Foreign causes cannot acquire an invented common order.
    pub(crate) fn join_causes(&self,Tracked(first):Tracked<Option<Receipt>>,Tracked(second):Tracked<Option<Receipt>>)->(out:Tracked<Option<Receipt>>)
        requires first.is_some() ==> first.unwrap().wf(),second.is_some() ==> second.unwrap().wf(),
        ensures out@.is_some() ==> out@.unwrap().wf() && out@.unwrap().journal()==*self,
            first.is_some() && first.unwrap().journal()==*self ==> out@.is_some() && out@.unwrap().covers(&first.unwrap()),
            second.is_some() && second.unwrap().journal()==*self ==> out@.is_some() && out@.unwrap().covers(&second.unwrap()),
    {
        let guard=self.inner.acquire_read();let _cell=guard.borrow();
        let tracked result;
        proof {
            if let Some(ref receipt)=first {if receipt.journal()==*self {_cell.history.borrow().extends(&receipt.witness);}}
            if let Some(ref receipt)=second {if receipt.journal()==*self {_cell.history.borrow().extends(&receipt.witness);}}
            result=if _cell.history@.events().len()>0 {
                Some(Receipt {journal:*self,witness:_cell.history.borrow().snapshot()})
            } else {None};
        }
        guard.release_read();Tracked(result)
    }
}
/// Persistent proof of an actual journal prefix. Entirely erased, including
/// the Journal reference; constructing one requires the authoritative owner.
#[allow(dead_code)]
pub tracked struct Receipt {ghost journal:Journal,witness:Witness<Frame>}
impl Receipt {
    pub closed spec fn journal(&self)->Journal {self.journal}
    pub closed spec fn events(&self)->Seq<Frame> {self.witness.events()}
    pub closed spec fn authentic(&self)->bool {self.witness.wf() && self.witness.source()==self.journal.inner.pred().history}
    pub open spec fn wf(&self)->bool {self.authentic() && self.events().len()>0 && valid(self.events())}
    pub open spec fn same(&self,other:&Self)->bool {self.journal()==other.journal() && self.events()==other.events()}
    pub open spec fn forward(&self)->bool {forward(self.event())}
    pub open spec fn at(&self)->nat {(self.events().len()-1) as nat}
    pub open spec fn event(&self)->Step {self.events().last().event}
    pub open spec fn covers(&self,earlier:&Self)->bool {self.journal()==earlier.journal()
        && earlier.events().len()<=self.events().len() && self.events().take(earlier.events().len() as int)==earlier.events()}
    pub proof fn cover_through(&self,middle:&Self,earlier:&Self)
        requires self.covers(middle),middle.covers(earlier),
        ensures self.covers(earlier),
    {assert(self.events().take(earlier.events().len() as int) =~= middle.events().take(earlier.events().len() as int));}
    pub proof fn included(&self,earlier:&Self)
        requires self.covers(earlier),earlier.events().len()>0,
        ensures earlier.at()<self.events().len(),self.events()[earlier.at() as int].event==earlier.event(),
    {}
    pub proof fn after_cover(&self,middle:&Self,earlier:&Self)
        requires self.follows(middle),middle.covers(earlier),
        ensures self.follows(earlier),
    {assert(self.events().take(earlier.events().len() as int) =~= middle.events().take(earlier.events().len() as int));}
    pub open spec fn follows(&self,earlier:&Self)->bool {self.journal()==earlier.journal()
        && earlier.events().len()<self.events().len() && self.events().take(earlier.events().len() as int)==earlier.events()}
    pub proof fn transition(&self)
        requires self.wf(),
        ensures pending_step(pending_at(self.events(),self.at()),self.events().last().pending,self.event(),self.at()),
    {
        assert(step(state_at(self.events(),self.at()),self.events()[self.at() as int].state,self.event()));
    }
    pub proof fn duplicate(tracked &self)->(tracked out:Self)
        ensures out.wf()==self.wf(),out.same(self),
    {Self {journal:self.journal,witness:self.witness.duplicate()}}
}
#[allow(dead_code)]
pub(crate) struct Member {journal:Journal,point:Tracked<GhostPointsTo<nat,Record>>,latest:Tracked<Witness<Frame>>}
impl Member {
    pub closed spec fn wf(&self)->bool {self.point@.id()==self.journal.inner.pred().source && self.latest@.wf()
        && self.latest@.source()==self.journal.inner.pred().history && self.events().len()>0 && valid(self.events())
        && self.events().last().event.key==self.key() && self.events().last().event.after==self.record()}
    pub proof fn receipt(tracked &self)->(tracked out:Receipt)
        requires self.wf(),ensures out.wf(),out.journal()==self.journal(),out.events()==self.events(),out.event().key==self.key(),out.event().after==self.record(),
    {Receipt {journal:self.journal,witness:self.latest.borrow().duplicate()}}
    pub closed spec fn events(&self)->Seq<Frame> {self.latest@.events()}
    pub closed spec fn record(&self)->Record {self.point@.value()}
    pub closed spec fn journal(&self)->Journal {self.journal}
    pub closed spec fn key(&self)->nat {self.point@.key()}
    pub(crate) fn certify(&self,view:&ReadView)
        requires self.wf(),view.wf(),view.journal_spec()==self.journal(),
        ensures view.state().contains_key(self.key()),view.state()[self.key()]==self.record(),
            self.events().len()<=view.events().len(),view.events().take(self.events().len() as int)==self.events(),
    {
        let _cell=view.guard.borrow();
        proof {self.point.borrow().agree(_cell.auth.borrow());_cell.history.borrow().extends(self.latest.borrow());}
    }
    pub(crate) fn certify_write(&self,_view:&WriteView)
        requires self.wf(),_view.wf(),_view.journal_spec()==self.journal(),
        ensures _view.state().contains_key(self.key()),_view.state()[self.key()]==self.record(),
            0<self.events().len()<=_view.events().len(),_view.events().take(self.events().len() as int)==self.events(),
            self.events().last().event.key==self.key(),
    {proof {self.point.borrow().agree(_view.cell.auth.borrow());_view.cell.history.borrow().extends(self.latest.borrow());}}
    /// Commit a cross-record transition only after its real members have been
    /// certified in this same held write epoch. No callback enters this scope.
    #[verifier::rlimit(20)]
    pub(crate) fn update_guarded<'a>(&mut self,view:WriteView<'a>,Ghost(after):Ghost<Record>,Ghost(change):Ghost<Change>)->(out:WriteView<'a>)
        requires old(self).wf(),view.wf(),view.journal_spec()==old(self).journal(),
            changes(old(self).record(),after,change),change is Groups || change is Host || change is Control || change is Recipes || change is Sources,
            guard(view.state(),old(self).record(),change),
        ensures final(self).wf(),final(self).record()==after,final(self).key()==old(self).key(),final(self).journal()==old(self).journal(),
            out.wf(),out.journal_spec()==view.journal_spec(),out.state()==view.state().insert(old(self).key(),after),
            final(self).events()==out.events(),final(self).events().len()==view.events().len()+1,
            out.events().take(view.events().len() as int)==view.events(),
            final(self).events().last().event==(Step {key:old(self).key(),change,after,pending:false,settled:None}),
            old(self).events().len()<final(self).events().len(),final(self).events().take(old(self).events().len() as int)==old(self).events(),
    {
        let journal=view.journal;
        #[allow(unused_mut)] // The authority changes only in erased proof state.
        let mut cell=view.cell;
        let guard=view.guard;
        proof {
            self.point.borrow().agree(cell.auth.borrow());
            cell.history.borrow().extends(self.latest.borrow());
            let prior=cell.auth@@;let key=self.key();let earlier=self.events();
            reveal(changes);assert(!(after is Slot));
            assert(prior.contains_key(key));
            assert(prior[key]==self.record());
            existing_change(self.record(),after,change);
            self.point.borrow_mut().update(cell.auth.borrow_mut(),after);
            assert(self.key()==key);
            assert(cell.auth@@==prior.insert(key,after));
            let event=Step {key,change,after,pending:false,settled:None};
            assert(step(prior,cell.auth@@,event));
            let _pending=cell.transfer(self.journal(),event,None);
            cell.record(event,prior);
            assert forall|k:nat| #[trigger] cell.auth@@.contains_key(k) <==> k<cell.next@ by {
                assert(cell.auth@@.contains_key(k)==prior.contains_key(k));
            }
            assert(cell.wf());
            self.latest=Tracked(cell.history.borrow().snapshot());
            assert(self.events().take(earlier.len() as int) =~= earlier);
        }
        WriteView {journal,cell,guard}
    }
    pub(crate) fn domain(&self)->(out:Journal) ensures out==self.journal(), {self.journal.clone()}
    pub(crate) fn observe(&self)->(out:Snapshot)
        requires self.wf(),
        ensures out.certified(),out.journal_spec()==self.journal(),out.domain()==self.journal().source(),out.last().contains_key(self.key()),out.last()[self.key()]==self.record(),
            self.events().len()<=out.events().len(),out.events().take(self.events().len() as int)==self.events(),
    {
        let guard=self.journal.inner.acquire_read();let _cell=guard.borrow();
        proof {self.point.borrow().agree(_cell.auth.borrow());_cell.history.borrow().extends(self.latest.borrow());}
        let tracked witness=_cell.history.borrow().snapshot();
        guard.release_read();Snapshot {journal:self.journal.clone(),witness:Tracked(witness)}
    }
    pub(crate) fn observe_following(&self,Tracked(earlier):Tracked<&Receipt>)->(out:Snapshot)
        requires self.wf(),earlier.wf(),
        ensures earlier.journal()==self.journal() ==> earlier.events().len()<=out.events().len()
                && out.events().take(earlier.events().len() as int)==earlier.events(),
            out.certified(),out.journal_spec()==self.journal(),out.domain()==self.journal().source(),out.last().contains_key(self.key()),out.last()[self.key()]==self.record(),
            self.events().len()<=out.events().len(),out.events().take(self.events().len() as int)==self.events(),
    {
        let guard=self.journal.inner.acquire_read();let _cell=guard.borrow();
        proof {self.point.borrow().agree(_cell.auth.borrow());_cell.history.borrow().extends(self.latest.borrow());
            if earlier.journal()==self.journal() {_cell.history.borrow().extends(&earlier.witness);}}
        let tracked witness=_cell.history.borrow().snapshot();
        guard.release_read();Snapshot {journal:self.journal.clone(),witness:Tracked(witness)}
    }
    pub open spec fn object(&self)->Object {Object {domain:self.journal().source(),key:self.key()}}
    #[verifier::rlimit(20)]
    pub(crate) fn observe_after(&self,_earlier:&Snapshot)->(out:Snapshot)
        requires self.wf(),_earlier.certified(),_earlier.journal_spec()==self.journal(),
        ensures out.certified(),out.extends(_earlier),out.journal_spec()==self.journal(),out.domain()==self.journal().source(),
            out.last().contains_key(self.key()),out.last()[self.key()]==self.record(),
            self.events().len()<=out.events().len(),out.events().take(self.events().len() as int)==self.events(),
    {
        let guard=self.journal.inner.acquire_read();let _cell=guard.borrow();
        proof {self.point.borrow().agree(_cell.auth.borrow());_cell.history.borrow().extends(_earlier.witness.borrow());_cell.history.borrow().extends(self.latest.borrow());}
        let tracked witness=_cell.history.borrow().snapshot();
        guard.release_read();Snapshot {journal:self.journal.clone(),witness:Tracked(witness)}
    }
    #[allow(unused_mut)] // Only the erased resources change under the real lock.
    #[verifier::rlimit(20)]
    pub(crate) fn update(&mut self,Ghost(after):Ghost<Record>,Ghost(change):Ghost<Change>)
        requires old(self).wf(),changes(old(self).record(),after,change),!(after is Slot),!(change is RegisterInverse),!(change is Groups),!(change is Host) && !(change is Control) && !(change is Recipes) && !(change is Sources),
        ensures final(self).wf(),final(self).record()==after,final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            old(self).events().len()<final(self).events().len(),final(self).events().take(old(self).events().len() as int)==old(self).events(),
            final(self).events().last().event==(Step {key:old(self).key(),change,after,pending:false,settled:None}),
    {let _pending=self.update_following(Ghost(after),Ghost(change),Tracked(None),Ghost(false),Tracked(None));}
    #[allow(unused_mut)] // Only the erased resources change under the real lock.
    #[verifier::rlimit(20)]
    pub(crate) fn update_following(&mut self,Ghost(after):Ghost<Record>,Ghost(change):Ghost<Change>,Tracked(cause):Tracked<Option<Receipt>>,Ghost(managed):Ghost<bool>,Tracked(pending):Tracked<Option<Pending>>)->(out:Tracked<Option<Pending>>)
        requires old(self).wf(),changes(old(self).record(),after,change),!(change is Groups),!(change is Host) && !(change is Control) && !(change is Recipes) && !(change is Sources),cause.is_some() ==> cause.unwrap().wf(),references::evidence(after,cause),
            change is RegisterInverse ==> cause.is_some() && cause.unwrap().journal()==old(self).journal()
                && cause.unwrap().forward() && cause.unwrap().at()==change->RegisterInverse_write,
            managed ==> change is PayloadApply || change is Value && (change->Value_event is Forward || change->Value_event is Computed),
            pending.is_some() ==> pending.unwrap().wf() && pending.unwrap().journal()==old(self).journal()
                && change==(Change::RegisterInverse {write:pending.unwrap().at()}) && !managed,
        ensures pending_matches(out@,old(self).journal(),old(self).key(),(final(self).events().len()-1) as nat,managed),
            final(self).wf(),final(self).record()==after,final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            old(self).events().len()<final(self).events().len(),final(self).events().take(old(self).events().len() as int)==old(self).events(),
            final(self).events().last().event==(Step {key:old(self).key(),change,after,pending:managed,settled:pending_index(pending)}),
            cause.is_some() && cause.unwrap().journal()==old(self).journal() ==>
                cause.unwrap().events().len()<final(self).events().len()
                && final(self).events().take(cause.unwrap().events().len() as int)==cause.unwrap().events(),
    {
        let (mut cell,guard)=self.journal.inner.acquire_write();
        let tracked produced;
        proof {
            self.point.borrow().agree(cell.auth.borrow());
            cell.history.borrow().extends(self.latest.borrow());
            if let Some(ref earlier)=cause {
                if earlier.journal()==self.journal() {cell.history.borrow().extends(&earlier.witness);}
            }
            certify_reference(cell.history.borrow(),after,&cause);
            let earlier=self.events();let history=cell.history@.events();
            let prior=cell.auth@@;
            let key=self.key();
            assert(prior.contains_key(key));
            assert(prior[key]==self.record());
            assert(changes(prior[key],after,change));
            existing_change(self.record(),after,change);
            self.point.borrow_mut().update(cell.auth.borrow_mut(),after);
            assert(self.key()==key);
            assert(cell.auth@@==prior.insert(key,after));
            let settled=pending_index(pending);
            let event=Step {key:self.key(),change,after,pending:managed,settled};
            reveal(groups::guard);
            assert(step(prior,cell.auth@@,event));
            if managed {reveal(changes);assert(forward(event));}
            produced=cell.transfer(self.journal(),event,pending);
            if change is RegisterInverse {
                let cause=cause.unwrap();
                assert(history[cause.at() as int]==cause.events()[cause.at() as int]);
            }
            cell.record(event,prior);
            assert(cell.wf());
            self.latest=Tracked(cell.history.borrow().snapshot());
            assert(self.events().take(earlier.len() as int) =~= earlier);
            if cause.is_some() && cause.unwrap().journal()==self.journal() {
                assert(self.events().take(cause.unwrap().events().len() as int) =~= cause.unwrap().events());
            }
        }
        guard.release_write(cell);Tracked(produced)
    }
}
#[allow(dead_code)]
pub struct Snapshot {journal:Journal,witness:Tracked<Witness<Frame>>}
impl Snapshot {
    pub(crate) fn receipt(&self)->(out:Tracked<Receipt>)
        requires self.certified(),self.events().len()>0,
        ensures out@.wf(),out@.journal()==self.journal_spec(),out@.events()==self.events(),
    {Tracked(Receipt {journal:self.journal,witness:self.witness.borrow().duplicate()})}

    /// Retain the actual read checkpoint as a causal input to a later write.
    /// No extra event or runtime history is allocated.
    pub(crate) fn checkpoint_receipt(&self)->(out:Tracked<Receipt>)
        requires self.certified(),self.events().len()>0,
        ensures out@.wf(),out@.journal()==self.journal_spec(),out@.events()==self.events(),
    {Tracked(Receipt {journal:self.journal,witness:self.witness.borrow().duplicate()})}

    pub closed spec fn journal_spec(&self)->Journal {self.journal}
    pub closed spec fn domain(&self)->Loc {self.journal.source()}
    pub closed spec fn events(&self)->Seq<Frame> {self.witness@.events()}
    pub closed spec fn certified(&self)->bool {self.witness@.wf() && valid(self.events()) && references::history(self.events(),self.domain())
        && self.witness@.source()==self.journal.inner.pred().history}
    pub open spec fn last(&self)->Map<nat,Record> {state_at(self.events(),self.events().len())}
    pub open spec fn pending(&self)->Map<nat,nat> {pending_at(self.events(),self.events().len())}
    /// Export the closed snapshot invariant to proof clients in other modules.
    pub proof fn valid_history(&self)
        requires self.certified(),ensures valid(self.events()),references::history(self.events(),self.domain()),
    {}

    pub open spec fn extends(&self,earlier:&Self)->bool {
        self.journal_spec()==earlier.journal_spec() && self.domain()==earlier.domain() && earlier.events().len()<=self.events().len()
            && self.events().take(earlier.events().len() as int)==earlier.events()
    }
    /// The trace starts empty. Every allocation, actual object mutation, swap
    /// and lifecycle commit is classified in one sequence; unrelated entries
    /// are framed at every step, without a caller-provided coherent snapshot.
    pub proof fn trajectory(&self)->(states:Seq<Map<nat,Record>>)
        requires self.certified(),
        ensures states.len()==self.events().len()+1,states.first()==Map::<nat,Record>::empty(),states.last()==self.last(),
            forall|i:int| 0<=i<self.events().len() ==> step(#[trigger] states[i],states[i+1],self.events()[i].event)
                && references::linked(states[i],self.events()[i].event.after,self.domain()),
            forall|i:int| 0<=i<states.len() ==> references::closed(#[trigger] states[i],self.domain()),
    {
        assert forall|i:int| 0<=i<=self.events().len() implies references::closed(#[trigger] state_at(self.events(),i as nat),self.domain()) by {
            references::at(self.events(),i as nat,self.domain());
        }
        Seq::new(self.events().len()+1,|i:int|state_at(self.events(),i as nat))
    }
    /// Every current local slot resolves, including replacements committed
    /// after an earlier slot receipt was collected by another thread.
    pub proof fn references(&self)
        requires self.certified(),ensures references::closed(self.last(),self.domain()),
    {references::at(self.events(),self.events().len(),self.domain());}
    /// The complete inverse obligation projection starts empty and is checked
    /// at the same commits as value and queue updates.
    pub proof fn pending_trajectory(&self)->(states:Seq<Map<nat,nat>>)
        requires self.certified(),
        ensures states.len()==self.events().len()+1,states.first()==Map::<nat,nat>::empty(),states.last()==self.pending(),
            forall|i:int| 0<=i<self.events().len() ==> pending_step(#[trigger] states[i],states[i+1],self.events()[i].event,i as nat),
    {
        assert forall|i:int| 0<=i<self.events().len() implies pending_step(pending_at(self.events(),i as nat),pending_at(self.events(),(i+1) as nat),self.events()[i].event,i as nat) by {
            assert(step(state_at(self.events(),i as nat),self.events()[i].state,self.events()[i].event));
        }
        Seq::new(self.events().len()+1,|i:int|pending_at(self.events(),i as nat))
    }
    /// Resolve only objects actually registered in this domain. Cross-domain
    /// references stay absent rather than acquiring an invented heap value.
    pub open spec fn resolve(&self,object:Object)->Option<ValueState> {
        if object.domain==self.domain() && self.last().contains_key(object.key) && self.last()[object.key] is Object
            {Some(self.last()[object.key]->Object_state)} else {None}
    }
    pub fn refresh(&self)->(out:Self)
        requires self.certified(),ensures out.certified(),out.extends(self),
    {
        let guard=self.journal.inner.acquire_read();let _cell=guard.borrow();
        proof {_cell.history.borrow().extends(self.witness.borrow());}
        let tracked witness=_cell.history.borrow().snapshot();
        guard.release_read();Snapshot {journal:self.journal.clone(),witness:Tracked(witness)}
    }
}
/// A bounded write epoch for composing actual owner records. All data under
/// this lock is erased; callers inspect queue metadata and release explicitly.
pub(crate) struct WriteView<'a> {journal:&'a Journal,cell:Cell,guard:WriteHandle<'a,Cell,Predicate>}
impl<'a> WriteView<'a> {
    pub closed spec fn journal_spec(&self)->Journal {*self.journal}
    pub closed spec fn state(&self)->Map<nat,Record> {self.cell.auth@@}
    pub closed spec fn events(&self)->Seq<Frame> {self.cell.history@.events()}
    pub closed spec fn wf(&self)->bool {
        self.guard.rwlock()==*self.journal.inner && self.cell.wf()
            && self.cell.auth@.id()==self.journal.inner.pred().source
            && self.cell.history@.source()==self.journal.inner.pred().history
            && self.cell.pending@.id()==self.journal.inner.pred().pending
    }
    /// Authenticate previously collected effect witnesses in this same write
    /// epoch. No value/slot lock or callback is entered while it is held.
    pub(crate) fn certify_receipts<K>(&self,Tracked(receipts):Tracked<&Map<K,Receipt>>)
        requires self.wf(),forall|k:K| receipts.contains_key(k) ==> #[trigger] receipts[k].wf(),
        ensures forall|k:K| receipts.contains_key(k) && #[trigger] receipts[k].journal()==self.journal_spec() ==>
            receipts[k].events().len()<=self.events().len()
                && self.events().take(receipts[k].events().len() as int)==receipts[k].events(),
    {proof {receipts_included(self.cell.history.borrow(),receipts,receipts.dom(),self.journal_spec());}}
    pub(crate) fn finish(self)
        requires self.wf(),
    {self.guard.release_write(self.cell);}
}
impl Journal {
    pub(crate) fn write(&self)->(out:WriteView<'_>)
        ensures out.wf(),out.journal_spec()==*self,
    {let (cell,guard)=self.inner.acquire_write();WriteView {journal:self,cell,guard}}
    pub(crate) fn read(&self)->(out:ReadView<'_>)
        ensures out.wf(),out.journal_spec()==*self,
    {ReadView {journal:self,guard:self.inner.acquire_read()}}
    /// Stable identity of this domain's authoritative execution history.
    pub closed spec fn source(&self)->Loc {self.inner.pred().history}
    pub fn new()->(out:Self) {
        let tracked (auth,_)=GhostMapAuth::new(Map::empty());
        let tracked history=Authority::new();
        let tracked (pending,_)=GhostMapAuth::new(Map::empty());
        let ghost pred=Predicate {source:auth.id(),history:history.source(),pending:pending.id()};
        Self {inner:Arc::new(RwLock::new(Cell {auth:Tracked(auth),history:Tracked(history),pending:Tracked(pending),next:Ghost(0nat)},Ghost(pred)))}
    }
    #[verifier::rlimit(20)]
    pub(crate) fn allocate(&self,Ghost(record):Ghost<Record>)->(out:Member)
        requires !(record is Slot),
        ensures out.wf(),out.journal()==*self,out.record()==record,
            out.events().len()>0,out.events().last().event.change==Change::Allocate,
            out.events().last().event.key==out.key(),out.events().last().event.after==record,
    {self.allocate_referencing(Ghost(record),Tracked(None))}
    /// A slot may enter the trace only with an actual object receipt. The
    /// receipt is collected before this lock; it remains valid across writes.
    #[verifier::rlimit(20)]
    pub(crate) fn allocate_referencing(&self,Ghost(record):Ghost<Record>,Tracked(target):Tracked<Option<Receipt>>)->(out:Member)
        requires references::evidence(record,target),
        ensures out.wf(),out.journal()==*self,out.record()==record,
            out.events().len()>0,out.events().last().event.change==Change::Allocate,
            out.events().last().event.key==out.key(),out.events().last().event.after==record,
    {
        let (mut cell,guard)=self.inner.acquire_write();
        let tracked point;
        let ghost key=cell.next@;
        let ghost prior=cell.auth@@;
        proof {
            certify_reference(cell.history.borrow(),record,&target);
            point=cell.auth.borrow_mut().insert(key,record);
        }
        cell.next=Ghost(key+1);
        proof {
            cell.record(Step {key,change:Change::Allocate,after:record,pending:false,settled:None},prior);
        }
        proof {
            assert forall|k:nat| #[trigger] cell.auth@@.contains_key(k) <==> k<cell.next@ by {
                if k!=key {assert(cell.auth@@.contains_key(k)==prior.contains_key(k));}
            }
            assert(cell.wf());
        }
        let tracked latest=cell.history.borrow().snapshot();
        guard.release_write(cell);
        Member {journal:self.clone(),point:Tracked(point),latest:Tracked(latest)}
    }
    pub fn snapshot(&self)->(out:Snapshot)
        ensures out.certified(),out.journal_spec()==*self,out.domain()==self.source(),
            classification::history(out.events()),
    {
        let guard=self.inner.acquire_read();
        let _cell=guard.borrow();
        let tracked witness=_cell.history.borrow().snapshot();
        guard.release_read();let out=Snapshot {journal:self.clone(),witness:Tracked(witness)};
        proof {out.classify();}out
    }
}
impl Default for Journal {fn default()->Self {Self::new()}}
}

#[path = "episode_execution.rs"]
pub mod episode;

#[path = "group_execution.rs"]
pub mod groups;

#[path = "recipe_execution.rs"]
pub mod recipes;

#[path = "native_execution.rs"]
pub mod native;

#[path = "host_execution.rs"]
pub mod host;

#[path = "control_execution.rs"]
pub mod control;

#[path = "value_references.rs"]
pub mod references;

#[path = "configuration_execution.rs"]
pub mod configuration;

#[path = "source_execution.rs"]
pub mod sources;

#[path = "joint_classification.rs"]
pub mod classification;

#[path = "payload_execution.rs"]
pub mod payload;
