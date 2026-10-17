//! Actual shared progress, owned by Execution and observed by escaped handles.
//! Payloads retain their exclusive host owner; a linear erased permission binds
//! those payload fields to this same checked status cell and Journal member.
use crate::effect_work::EffectRun;
use crate::execution::Execution;
use crate::reversible_value::joint::host::{EpisodeIdentity, Event, Kind, State};
use crate::reversible_value::joint::{self, Journal, Member};
use std::sync::Arc;
use vstd::prelude::*;
use vstd::resource::map::{GhostMapAuth, GhostPointsTo};
use vstd::resource::Loc;
use vstd::rwlock::{RwLock, RwLockPredicate};

verus! {
/// Erased interpretation of the actual error/terminal/Child fields. Only the
/// HostStatus holding the linear point can change these fields in the cell.
#[allow(dead_code)] // Metadata exists only in erased permissions.
struct Payload {errors:nat,terminal:bool,child:Option<usize>}
#[allow(dead_code)]
struct Cell {
    kind:Kind,episode:Option<EpisodeIdentity>,owner:Ghost<Option<nat>>,
    cancelled:bool,initialized:bool,finished:bool,
    payload:Tracked<GhostMapAuth<(),Payload>>,member:Member,birth:Ghost<nat>,
}
impl Cell {
    closed spec fn data(&self)->Payload {self.payload@@[()]}
    closed spec fn state(&self)->State {
        State {owner:self.owner@,episode:self.episode,kind:self.kind,cancelled:self.cancelled,
            initialized:self.initialized,finished:self.finished,errors:self.data().errors,
            terminal:self.data().terminal,child:self.data().child}
    }
    closed spec fn storage_wf(&self)->bool {
        self.payload@@.dom()==set![()] && joint::host::origin(self.member.events(),self.member.key(),self.birth@,self.state())
    }
    closed spec fn wf(&self)->bool {self.storage_wf() && self.member.wf() && self.member.record()==(joint::Record::Host {state:self.state()})}
    fn observe(&self)->(out:Observation)
        requires self.wf(),ensures out.wf(),out.allocation()==self.birth@,out.state()==self.state(),out.journal()==self.member.journal(),out.key()==self.member.key(),out.history()==self.member.events(),
    {
        let out=Observation {cancelled:self.cancelled,initialized:self.initialized,finished:self.finished,witness:Tracked(self.member.receipt()),birth:Ghost(self.birth@)};
        proof {joint::host::history_progress(out.history(),out.key());}
        out
    }
    fn commit(&mut self,Ghost(before):Ghost<State>,Ghost(event):Ghost<Event>)
        requires old(self).storage_wf(),old(self).member.wf(),old(self).member.record()==(joint::Record::Host {state:before}),
            joint::host::step(before,old(self).state(),event),event!=Event::EffectInitialized,event!=Event::EffectFinished,
        ensures final(self).wf(),final(self).birth==old(self).birth,final(self).state()==old(self).state(),final(self).payload==old(self).payload,
            final(self).member.journal()==old(self).member.journal(),final(self).member.key()==old(self).member.key(),
            final(self).member.events().last().event.change==(joint::Change::Host {event}),
    {
        let journal=self.member.domain();let view=journal.write();
        proof {reveal(joint::changes);reveal(joint::host::guard);}
        let view=self.member.update_guarded(view,Ghost(joint::Record::Host {state:self.state()}),Ghost(joint::Change::Host {event}));view.finish();
    }
}
#[allow(dead_code)]
struct Predicate {journal:Journal,key:nat,owner:Option<nat>,episode:Option<EpisodeIdentity>,kind:Kind,payload:Loc,birth:nat}
impl RwLockPredicate<Cell> for Predicate {
    closed spec fn inv(self,cell:Cell)->bool {
        cell.wf() && cell.member.journal()==self.journal && cell.member.key()==self.key
            && cell.owner@==self.owner && cell.episode==self.episode && cell.kind==self.kind && cell.payload@.id()==self.payload && cell.birth@==self.birth
    }
}
/// The three returned flags and an authentic prefix ending at their member's
/// actual latest commit. The witness is erased; this does not lock the Journal
/// or claim that unrelated members are still at this older global prefix.
#[allow(dead_code)]
pub struct Observation {cancelled:bool,initialized:bool,finished:bool,witness:Tracked<joint::Receipt>,birth:Ghost<nat>}
impl Observation {
    pub closed spec fn wf(&self)->bool {self.witness@.wf() && self.witness@.event().after is Host
        && joint::host::history(self.history(),self.key()) && joint::host::origin(self.history(),self.key(),self.birth@,self.state())
        && self.cancelled==self.state().cancelled && self.initialized==self.state().initialized && self.finished==self.state().finished}
    /// Audit any interval of this actual receipt, retaining all interleavings.
    pub proof fn progress_between(&self,start:nat,end:nat)
        requires self.wf(),start<=end<=self.history().len(),joint::host::recorded(self.history(),start,self.key()),
        ensures joint::host::segment(self.history(),start,end,self.key()),
    {}
    pub closed spec fn allocation(&self)->nat {self.birth@}
    /// The source is the actual constructor commit, not a caller-selected
    /// initial state. Every subsequent step of this handle is classified.
    pub proof fn lifetime(&self)
        requires self.wf(),
        ensures joint::valid(self.history()),joint::host::origin(self.history(),self.key(),self.allocation(),self.state()),
            forall|index:nat| self.allocation()<index<=self.history().len() ==>
                #[trigger] joint::host::recorded(self.history(),index,self.key())
                && joint::host::segment(self.history(),self.allocation()+1,index,self.key()),
            forall|index:nat| self.allocation()<index<self.history().len() ==>
                #[trigger] joint::host::classified(self.history(),index,self.key()),
    {
        let frames=self.history();let birth=self.allocation();let key=self.key();
        assert(joint::step(joint::state_at(frames,birth),frames[birth as int].state,frames[birth as int].event));
        assert(joint::host::recorded(frames,birth+1,key));
        assert forall|index:nat| birth<index<=frames.len() implies
            #[trigger] joint::host::recorded(frames,index,key) && joint::host::segment(frames,birth+1,index,key) by {
            joint::host::progress_between(frames,birth+1,index,key);
        }
    }

    pub proof fn classified_step(&self,index:nat)
        requires self.wf(),index<self.history().len(),joint::host::recorded(self.history(),index,self.key()),
        ensures joint::host::classified(self.history(),index,self.key()),
    {}
    pub closed spec fn state(&self)->State {self.witness@.event().after->Host_state}
    pub closed spec fn journal(&self)->Journal {self.witness@.journal()}
    pub closed spec fn key(&self)->nat {self.witness@.event().key}
    pub closed spec fn history(&self)->Seq<joint::Frame> {self.witness@.events()}
    pub fn cancelled(&self)->(out:bool) requires self.wf(),ensures out==self.state().cancelled, {self.cancelled}
    pub fn initialized(&self)->(out:bool) requires self.wf(),ensures out==self.state().initialized, {self.initialized}
    pub fn finished(&self)->(out:bool) requires self.wf(),ensures out==self.state().finished, {self.finished}
    pub closed spec fn retirement_recorded(&self)->bool {
        self.state().kind is Effect && self.state().owner.is_some()
            && exists|index:int| 0<=index<self.history().len()-1
                && #[trigger] self.history()[index].event.change==(joint::Change::Groups {event:joint::groups::Event::Remove {id:self.state().kind->Effect_group}})
                && self.history()[index].event.key==self.state().owner.unwrap()
    }
}
/// Only Execution and HostStatus can create/retain a link. It contains no user
/// payload, callback, Waker or strong Episode reference.
pub struct Link {inner:Arc<RwLock<Cell,Predicate>>}
impl Clone for Link {fn clone(&self)->(out:Self) ensures out==*self, {Self {inner:self.inner.clone()}}}
impl Link {
    pub closed spec fn journal(&self)->Journal {self.inner.pred().journal}
    pub closed spec fn key(&self)->nat {self.inner.pred().key}
    pub closed spec fn allocation(&self)->nat {self.inner.pred().birth}
    pub closed spec fn owner(&self)->Option<nat> {self.inner.pred().owner}
    pub closed spec fn episode(&self)->Option<EpisodeIdentity> {self.inner.pred().episode}
    pub closed spec fn kind(&self)->Kind {self.inner.pred().kind}
    closed spec fn payload_source(&self)->Loc {self.inner.pred().payload}
    pub open spec fn bound<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->bool {
        self.owner().is_some() && execution.cleanup_state().link()==Some((self.journal(),self.owner().unwrap()))
            && self.episode().is_some() && self.episode().unwrap().owns(execution)
    }
    pub open spec fn observed(&self,observation:&Observation)->bool {
        observation.wf() && observation.journal()==self.journal() && observation.key()==self.key() && observation.allocation()==self.allocation()
            && observation.state().owner==self.owner() && observation.state().episode==self.episode() && observation.state().kind==self.kind()
    }
    fn new(journal:&Journal,kind:Kind,episode:Option<EpisodeIdentity>,Ghost(owner):Ghost<Option<nat>>)
        ->(out:(Self,Tracked<GhostPointsTo<(),Payload>>,Observation))
        ensures out.0.journal()==*journal,out.0.kind()==kind,out.0.episode()==episode,out.0.owner()==owner,
            out.1@.id()==out.0.payload_source(),out.1@.key()==(),out.1@.value()==(Payload {errors:0,terminal:false,child:None}),
            out.0.observed(&out.2),out.2.state()==(State {owner,episode,kind,cancelled:false,initialized:false,finished:false,errors:0,terminal:false,child:None}),
    {
        let tracked (mut payload,_)=GhostMapAuth::new(Map::<(),Payload>::empty());
        let tracked point=payload.insert((),Payload {errors:0,terminal:false,child:None});
        let ghost initial=State {owner,episode,kind,cancelled:false,initialized:false,finished:false,errors:0,terminal:false,child:None};
        let member=journal.allocate(Ghost(joint::Record::Host {state:initial}));
        let ghost birth=(member.events().len()-1) as nat;
        let ghost pred=Predicate {journal:*journal,key:member.key(),owner,episode,kind,payload:payload.id(),birth};
        let cell=Cell {kind,episode,owner:Ghost(owner),cancelled:false,initialized:false,finished:false,payload:Tracked(payload),member,birth:Ghost(birth)};
        let observation=cell.observe();
        (Self {inner:Arc::new(RwLock::new(cell,Ghost(pred)))},Tracked(point),observation)
    }
    fn matches_episode<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->(out:bool)
        ensures out==(self.episode().is_some() && self.episode().unwrap().owns(execution)),
    {
        let guard=self.inner.acquire_read();let cell=guard.borrow();
        let out=match &cell.episode {Some(owner)=>owner.matches(execution),None=>false};
        guard.release_read();out
    }
}
#[allow(dead_code)]
pub struct HostStatus<E> {
    link:Link,errors:Vec<E>,terminal:Option<E>,child:Option<usize>,
    point:Tracked<GhostPointsTo<(),Payload>>,latest:Ghost<Observation>,
}
impl<E> HostStatus<E> {
    pub closed spec fn errors_spec(&self)->Seq<E> {self.errors@}
    pub closed spec fn terminal_spec(&self)->Option<E> {self.terminal}
    pub closed spec fn child_spec(&self)->Option<usize> {self.child}
    closed spec fn payload(&self)->Payload {Payload {errors:self.errors@.len(),terminal:self.terminal.is_some(),child:self.child}}
    pub closed spec fn journal(&self)->Journal {self.link.journal()}
    pub closed spec fn key(&self)->nat {self.link.key()}
    /// This is the last observation retained by this exclusive payload owner,
    /// not an immutable model of the concurrently shared progress flags.
    pub closed spec fn last_observed(&self)->Observation {self.latest@}
    pub closed spec fn kind(&self)->Kind {self.link.kind()}
    pub closed spec fn wf(&self)->bool {
        self.point@.id()==self.link.payload_source() && self.point@.key()==() && self.point@.value()==self.payload()
            && self.link.observed(&self.last_observed()) && self.last_observed().state().errors==self.errors@.len()
            && self.last_observed().state().terminal==self.terminal.is_some() && self.last_observed().state().child==self.child
    }
    pub closed spec fn binding(&self)->Link {self.link}
    pub open spec fn owned_by<V,C,G,I>(&self,execution:&Execution<V,C,G,I>,id:usize)->bool {
        execution.status_links().contains_pair(id,self.binding())
    }
    pub open spec fn bound<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->bool {self.binding().bound(execution)}
    pub open spec fn observes(&self,observation:&Observation)->bool {self.binding().observed(observation)}
    pub fn matches_episode<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->(out:bool)
        ensures out==(self.binding().episode().is_some() && self.binding().episode().unwrap().owns(execution)),
    {self.link.matches_episode(execution)}
    fn new(journal:&Journal,kind:Kind,episode:Option<EpisodeIdentity>,Ghost(owner):Ghost<Option<nat>>)->(out:Self)
        ensures out.wf(),out.journal()==*journal,out.kind()==kind,out.link.episode()==episode,out.link.owner()==owner,
            out.last_observed().state()==(State {owner,episode,kind,cancelled:false,initialized:false,finished:false,errors:0,terminal:false,child:None}),
            out.errors_spec()==Seq::<E>::empty(),out.terminal_spec().is_none(),out.child_spec().is_none(),
    {
        let (link,point,_observation)=Link::new(journal,kind,episode,Ghost(owner));
        Self {link,point,latest:Ghost(_observation),errors:Vec::new(),terminal:None,child:None}
    }
    pub fn external_service()->(out:Self)
        ensures out.wf(),out.kind()==Kind::Service,!out.last_observed().state().finished,!out.last_observed().state().initialized,
    {Self::new(&Journal::new(),Kind::Service,None,Ghost(None))}
    pub fn errors(&self)->(out:&Vec<E>) ensures out@==self.errors_spec(), {&self.errors}
    pub fn terminal_error(&self)->(out:Option<&E>)
        ensures out.is_some()==self.terminal_spec().is_some(),out.is_some() ==> *out.unwrap()==self.terminal_spec().unwrap(),
    {self.terminal.as_ref()}
    pub fn external_child_id(&self)->(out:Option<usize>) ensures out==self.child_spec(), {self.child}
    pub fn observe(&self)->(out:Observation)
        requires self.wf(),ensures self.observes(&out),out.state().errors==self.errors_spec().len(),out.state().terminal==self.terminal_spec().is_some(),out.state().child==self.child_spec(),
    {
        let guard=self.link.inner.acquire_read();let cell=guard.borrow();
        proof {self.point.borrow().agree(cell.payload.borrow());}
        let out=cell.observe();guard.release_read();out
    }
    /// Unlike observe's member-local receipt, this captures the entire Journal
    /// under one read epoch while the actual status cell remains locked.
    pub fn execution_snapshot(&self)->(out:joint::Snapshot)
        requires self.wf(),ensures out.certified(),out.journal_spec()==self.journal(),
            out.last().contains_key(self.key()),out.last()[self.key()] is Host,
            out.last()[self.key()]->Host_state.errors==self.errors_spec().len(),
            out.last()[self.key()]->Host_state.terminal==self.terminal_spec().is_some(),
            out.last()[self.key()]->Host_state.child==self.child_spec(),
            joint::classification::history(out.events()),
    {
        let guard=self.link.inner.acquire_read();let cell=guard.borrow();
        proof {self.point.borrow().agree(cell.payload.borrow());}
        let out=cell.member.observe();guard.release_read();proof {out.classify();}out
    }
    pub fn cancel(&mut self)
        requires old(self).wf(),ensures final(self).wf(),final(self).binding()==old(self).binding(),
            final(self).errors_spec()==old(self).errors_spec(),final(self).terminal_spec()==old(self).terminal_spec(),final(self).child_spec()==old(self).child_spec(),
            final(self).last_observed().state().cancelled,
    {
        let (mut cell,guard)=self.link.inner.acquire_write();
        proof {self.point.borrow().agree(cell.payload.borrow());}
        if !cell.cancelled {
            let ghost before=cell.state();cell.cancelled=true;
            proof {reveal(joint::host::step);}cell.commit(Ghost(before),Ghost(Event::Cancel));
        }
        let _observation=cell.observe();self.latest=Ghost(_observation);guard.release_write(cell);
    }
    pub fn push_error(&mut self,error:E)
        requires old(self).wf(),ensures final(self).wf(),final(self).binding()==old(self).binding(),
            final(self).errors_spec()==old(self).errors_spec().push(error),final(self).terminal_spec()==old(self).terminal_spec(),final(self).child_spec()==old(self).child_spec(),
            final(self).last_observed().history().last().event.change==(joint::Change::Host {event:Event::Error}),
    {
        let link=self.link.clone();let (mut cell,guard)=link.inner.acquire_write();
        proof {self.point.borrow().agree(cell.payload.borrow());}
        let ghost before=cell.state();self.errors.push(error);
        proof {let data=self.payload();self.point.borrow_mut().update(cell.payload.borrow_mut(),data);assert(cell.payload@@.dom() =~= set![()]);reveal(joint::host::step);}
        cell.commit(Ghost(before),Ghost(Event::Error));let _observation=cell.observe();self.latest=Ghost(_observation);guard.release_write(cell);
    }
    pub fn report_terminal(&mut self,error:E)->(unused:Option<E>)
        requires old(self).wf(),ensures final(self).wf(),final(self).binding()==old(self).binding(),
            final(self).errors_spec()==old(self).errors_spec(),final(self).child_spec()==old(self).child_spec(),
            old(self).kind()!=Kind::Service ==> unused==Some(error) && final(self).terminal_spec()==old(self).terminal_spec(),
            old(self).kind()==Kind::Service ==> final(self).last_observed().state().cancelled
                && final(self).terminal_spec()==if old(self).terminal_spec().is_some() {old(self).terminal_spec()} else {Some(error)},
    {
        let link=self.link.clone();let (mut cell,guard)=link.inner.acquire_write();
        proof {self.point.borrow().agree(cell.payload.borrow());}
        if cell.kind!=Kind::Service {guard.release_write(cell);return Some(error);}
        let ghost before=cell.state();cell.cancelled=true;
        let unused=if self.terminal.is_none() {self.terminal=Some(error);None} else {Some(error)};
        proof {let data=self.payload();self.point.borrow_mut().update(cell.payload.borrow_mut(),data);assert(cell.payload@@.dom() =~= set![()]);reveal(joint::host::step);}
        cell.commit(Ghost(before),Ghost(Event::Terminal));let _observation=cell.observe();self.latest=Ghost(_observation);guard.release_write(cell);unused
    }
    pub fn assign_child(&mut self,id:usize)->(out:bool)
        requires old(self).wf(),ensures final(self).wf(),final(self).binding()==old(self).binding(),
            final(self).errors_spec()==old(self).errors_spec(),final(self).terminal_spec()==old(self).terminal_spec(),
            out==(old(self).kind()==Kind::Service && old(self).child_spec().is_none()),
            final(self).child_spec()==if out {Some(id)} else {old(self).child_spec()},
    {
        let link=self.link.clone();let (mut cell,guard)=link.inner.acquire_write();
        proof {self.point.borrow().agree(cell.payload.borrow());}
        if cell.kind!=Kind::Service || self.child.is_some() {guard.release_write(cell);return false;}
        let ghost before=cell.state();self.child=Some(id);
        proof {let data=self.payload();self.point.borrow_mut().update(cell.payload.borrow_mut(),data);assert(cell.payload@@.dom() =~= set![()]);reveal(joint::host::step);}
        cell.commit(Ghost(before),Ghost(Event::Child));let _observation=cell.observe();self.latest=Ghost(_observation);guard.release_write(cell);true
    }
    pub fn report_service_initialized(&mut self)->(out:bool)
        requires old(self).wf(),ensures final(self).wf(),final(self).binding()==old(self).binding(),
            final(self).errors_spec()==old(self).errors_spec(),final(self).terminal_spec()==old(self).terminal_spec(),final(self).child_spec()==old(self).child_spec(),
            out==(old(self).kind()==Kind::Service),out ==> final(self).last_observed().state().initialized,
    {
        let (mut cell,guard)=self.link.inner.acquire_write();
        proof {self.point.borrow().agree(cell.payload.borrow());}
        if cell.kind!=Kind::Service {guard.release_write(cell);return false;}
        if !cell.initialized {
            let ghost before=cell.state();cell.initialized=true;
            proof {reveal(joint::host::step);}cell.commit(Ghost(before),Ghost(Event::ServiceInitialized));
        }
        let _observation=cell.observe();self.latest=Ghost(_observation);guard.release_write(cell);true
    }
    pub fn report_service_finished(&mut self)->(out:bool)
        requires old(self).wf(),ensures final(self).wf(),final(self).binding()==old(self).binding(),
            final(self).errors_spec()==old(self).errors_spec(),final(self).terminal_spec()==old(self).terminal_spec(),final(self).child_spec()==old(self).child_spec(),
            out==(old(self).kind()==Kind::Service && old(self).terminal_spec().is_none()),out ==> final(self).last_observed().state().finished,
    {
        let (mut cell,guard)=self.link.inner.acquire_write();
        proof {self.point.borrow().agree(cell.payload.borrow());}
        if cell.kind!=Kind::Service || self.terminal.is_some() {guard.release_write(cell);return false;}
        if !cell.finished {
            let ghost before=cell.state();cell.finished=true;
            proof {reveal(joint::host::step);}cell.commit(Ghost(before),Ghost(Event::ServiceFinished));
        }
        let _observation=cell.observe();self.latest=Ghost(_observation);guard.release_write(cell);true
    }
}

impl<V,C,G,I> Execution<V,C,G,I> {
    pub fn service_status<E>(&self)->(out:HostStatus<E>)
        requires self.wf(),ensures out.wf(),out.kind()==Kind::Service,
            !out.last_observed().state().finished,!out.last_observed().state().initialized,
            self.execution_journal().is_some() ==> out.bound(self),
    {
        proof {self.representation();self.groups.execution_link();}
        match self.groups.execution_domain() {
            Some(journal)=>HostStatus::new(journal,Kind::Service,Some(EpisodeIdentity {origin:self.lifecycle_ticket(),work_domain:self.work().domain()}),Ghost(Some(self.cleanup_state().link().unwrap().1))),
            None=>HostStatus::external_service(),
        }
    }
    /// Install exactly one shared status for the actual live group. The link
    /// retained here is the one returned to the payload owner, not an ID lookup
    /// supplied later by an ordinary host or a foreign status object.
    pub fn effect_status<E>(&mut self,id:usize)->(out:Option<HostStatus<E>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).work_state()==old(self).work_state(),final(self).cleanup_state()==old(self).cleanup_state(),
            final(self).value_state()==old(self).value_state(),final(self).capture()==old(self).capture(),final(self).effect_state()==old(self).effect_state(),
            final(self).checked_out()==old(self).checked_out(),final(self).value_attempts()==old(self).value_attempts(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).execution_journal()==old(self).execution_journal(),
            out.is_some()==(id!=0 && !old(self).status_links().contains_key(id)
                && old(self).execution_journal().is_some() && old(self).cleanup_state().live(id)),
            out.is_some() ==> out.unwrap().wf() && out.unwrap().owned_by(final(self),id) && out.unwrap().bound(final(self))
                && out.unwrap().kind()==(Kind::Effect {group:id,domain:final(self).cleanup_state().domain_ids()[id]})
                && !out.unwrap().last_observed().state().finished && !out.unwrap().last_observed().state().initialized
                && final(self).status_links()==old(self).status_links().insert(id,out.unwrap().binding()),
            out.is_none() ==> *final(self)==*old(self),
    {
        proof {self.representation();self.groups.execution_link();}
        if id==0 || self.statuses.contains_key(&id) {return None;}
        let journal=self.groups.execution_domain()?;let queue=self.groups.get(id)?;
        let status=HostStatus::new(journal,Kind::Effect {group:id,domain:queue.domain()},Some(EpisodeIdentity {origin:self.lifecycle_ticket(),work_domain:self.work().domain()}),Ghost(Some(self.cleanup_state().link().unwrap().1)));
        self.statuses.insert(id,status.link.clone());proof {self.representation();}Some(status)
    }
    /// The only input selecting status is this Execution's own group ID. Every
    /// Journal/group relation follows from its stored link invariant.
    pub fn initialize_effect_status(&self,id:usize)->(out:Option<Observation>)
        requires self.wf(),
        ensures out.is_some() ==> self.status_links().contains_key(id)
            && self.status_links()[id].observed(&out.unwrap()) && out.unwrap().state().initialized,
    {
        proof {self.representation();self.groups.execution_link();}
        let link=self.statuses.get(&id)?;let queue=self.groups.get(id)?;
        if !queue.is_settled() || queue.is_pending() {return None;}
        let (mut cell,guard)=link.inner.acquire_write();
        if !cell.initialized {
            let journal=cell.member.domain();let view=journal.write();
            self.groups.certify_membership(&view);queue.certify_write(&view);
            cell.initialized=true;
            proof {reveal(joint::changes);reveal(joint::host::step);reveal(joint::host::guard);}
            let view=cell.member.update_guarded(view,Ghost(joint::Record::Host {state:cell.state()}),Ghost(joint::Change::Host {event:Event::EffectInitialized}));view.finish();
        }
        let observation=cell.observe();guard.release_write(cell);Some(observation)
    }
    /// Shared implementation for raw and observed retirement. A status, when
    /// installed, always completes here; no entry can be silently abandoned.
    pub(crate) fn retire_with_status(&mut self,run:EffectRun<G>)->(out:Result<(G,Option<Observation>),EffectRun<G>>)
        requires old(self).wf(),run.wf(),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),final(self).value_attempts()==old(self).value_attempts(),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),final(self).effect_state()==old(self).effect_state(),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),run.identity().group_id()),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==run,
            out.is_ok() ==> out->Ok_0.0==run.payload() && !final(self).cleanup_state().live(run.identity().group_id())
                && run.identity().group_id()<final(self).cleanup_state().next_id()
                && final(self).checked_out()==old(self).checked_out().remove(run.identity().group_id())
                && final(self).status_links()==old(self).status_links().remove(run.identity().group_id())
                && out->Ok_0.1.is_some()==old(self).status_links().contains_key(run.identity().group_id()),
            out.is_ok() && final(self).cleanup_state().link().is_some() ==> final(self).cleanup_state().membership_trace().last().event.change
                ==(joint::Change::Groups {event:joint::groups::Event::Remove {id:run.identity().group_id()}}),
            out.is_ok() && out->Ok_0.1.is_some() ==> old(self).status_links()[run.identity().group_id()].observed(&out->Ok_0.1.unwrap())
                && out->Ok_0.1.unwrap().state().initialized && out->Ok_0.1.unwrap().state().finished
                && out->Ok_0.1.unwrap().retirement_recorded()
                && out->Ok_0.1.unwrap().history().last().event.change==(joint::Change::Host {event:Event::EffectFinished}),
    {
        proof {self.representation();self.groups.execution_link();}
        let id=run.id();
        if !self.checked_out.contains_key(&id) || !run.belongs(&self.groups) {return Err(run);}
        if !self.groups.remove(id) {return Err(run);}
        self.checked_out.remove(&id);
        let link=self.statuses.remove(&id);
        proof {self.representation();self.groups.execution_link();}
        let observation=match link {
            Some(link)=>{
                let (mut cell,guard)=link.inner.acquire_write();
                let journal=cell.member.domain();let view=journal.write();self.groups.certify_membership(&view);
                let ghost retirement=(self.cleanup_state().membership_trace().len()-1) as int;
                assert(view.events()[retirement]==self.cleanup_state().membership_trace().last());
                cell.initialized=true;cell.finished=true;
                proof {reveal(joint::changes);reveal(joint::host::step);reveal(joint::host::guard);}
                let view=cell.member.update_guarded(view,Ghost(joint::Record::Host {state:cell.state()}),Ghost(joint::Change::Host {event:Event::EffectFinished}));view.finish();
                let observation=cell.observe();
                assert(observation.history()[retirement].event.change==(joint::Change::Groups {event:joint::groups::Event::Remove {id}}));
                assert(observation.retirement_recorded());
                guard.release_write(cell);Some(observation)
            },
            None=>None,
        };
        Ok((run.into_payload(),observation))
    }
    pub fn retire_observed_effect(&mut self,run:EffectRun<G>)->(out:Result<(G,Observation),EffectRun<G>>)
        requires old(self).wf(),run.wf(),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),final(self).capture()==old(self).capture(),
            final(self).phase_spec()==old(self).phase_spec(),final(self).value_attempts()==old(self).value_attempts(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==run,
            out.is_ok() ==> out->Ok_0.0==run.payload() && !final(self).cleanup_state().live(run.identity().group_id())
                && final(self).status_links()==old(self).status_links().remove(run.identity().group_id())
                && old(self).status_links().contains_key(run.identity().group_id())
                && old(self).status_links()[run.identity().group_id()].observed(&out->Ok_0.1)
                && out->Ok_0.1.state().initialized && out->Ok_0.1.state().finished && out->Ok_0.1.retirement_recorded(),
    {
        proof {self.representation();}
        if !self.statuses.contains_key(&run.id()) {return Err(run);}
        let (payload,observation)=self.retire_with_status(run)?;Ok((payload,observation.unwrap()))
    }
}
} // verus!
