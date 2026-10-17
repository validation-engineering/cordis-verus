//! Production polling state. Native Begin/retry/Unload own the reset paths;
//! callback error payloads are retained exactly and dropped outside Journal locks.
use crate::action_ledger::ActionTicket;
use crate::execution::Execution;
use crate::lifecycle_actions::CleanupOutcome;
use crate::lifecycle_state::native::runtime::NativeRuntime;
use crate::lifecycle_state::services::ReleasedNativeValues;
use crate::reversible_value::joint::control::{Event, State};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint::Journal;
use crate::reversible_value::joint::{self, Member};
#[cfg(verus_keep_ghost)]
use crate::Kernel;
use crate::{Error, Phase};
use vstd::prelude::*;
verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct PollFlags {pub failed:bool,pub restart:bool}
pub struct PollControl<E> {
    owner:usize,episode:Option<ActionTicket>,work_domain:u64,
    failed:Option<E>,cleanup_failure:Option<E>,restart:bool,
    #[allow(dead_code)] native:Ghost<nat>,
    #[allow(dead_code)] groups:Ghost<Option<nat>>,
    member:Member,
}
impl<E> PollControl<E> {
    pub closed spec fn state(&self)->State {State {native:self.native@,owner:self.owner,episode:self.episode,
        work_domain:self.work_domain,groups:self.groups@,failed:self.failed.is_some(),cleanup_failure:self.cleanup_failure.is_some(),restart:self.restart}}
    pub closed spec fn setup_error(&self)->Option<E> {self.failed}
    pub closed spec fn cleanup_error(&self)->Option<E> {self.cleanup_failure}
    pub closed spec fn journal(&self)->Journal {self.member.journal()}
    pub closed spec fn key(&self)->nat {self.member.key()}
    pub closed spec fn history(&self)->Seq<joint::Frame> {self.member.events()}
    pub closed spec fn wf(&self)->bool {self.member.wf() && self.member.record()==(joint::Record::Control {state:self.state()})}
    pub open spec fn bound<R,H,V>(&self,native:&NativeRuntime<R,H,V>)->bool {
        self.journal()==native.journal_spec() && self.state().native==native.joint_key()
    }
    pub open spec fn matches<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->bool {
        self.state().episode.is_some() && self.state().episode==execution.origin()
            && self.state().work_domain==execution.work_state().domain_id()
    }
    pub fn matches_execution<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->(out:bool)
        ensures out==self.matches(execution),
    {self.episode.is_some() && self.episode==execution.lifecycle_ticket() && self.work_domain==execution.work().domain()}
    pub fn owner(&self)->(out:usize) ensures out==self.state().owner, {self.owner}
    pub fn failed(&self)->(out:Option<&E>) ensures out.is_some()==self.setup_error().is_some(),out.is_some() ==> *out.unwrap()==self.setup_error().unwrap(), {self.failed.as_ref()}
    pub fn cleanup_failure(&self)->(out:Option<&E>) ensures out.is_some()==self.cleanup_error().is_some(),out.is_some() ==> *out.unwrap()==self.cleanup_error().unwrap(), {self.cleanup_failure.as_ref()}
    /// These are the actual inputs consumed by the native polling decision.
    /// Availability is an external predicate, supplied separately by the host.
    pub fn poll_flags(&self)->(out:PollFlags)
        ensures out.failed==(self.state().failed || self.state().cleanup_failure),out.restart==self.state().restart,
    {PollFlags {failed:self.failed.is_some() || self.cleanup_failure.is_some(),restart:self.restart}}
    pub fn restart_requested(&self)->(out:bool) ensures out==self.state().restart, {self.restart}
    fn commit(&mut self,view:joint::WriteView,Ghost(before):Ghost<State>,Ghost(event):Ghost<Event>)
        requires old(self).member.wf(),old(self).member.record()==(joint::Record::Control {state:before}),
            view.wf(),view.journal_spec()==old(self).journal(),joint::control::step(before,old(self).state(),event),
            joint::control::guard(view.state(),before,event),
        ensures final(self).wf(),final(self).state()==old(self).state(),final(self).setup_error()==old(self).setup_error(),
            final(self).cleanup_error()==old(self).cleanup_error(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).history().last().event.change==(joint::Change::Control {event}),
    {
        proof {reveal(joint::changes);}
        let view=self.member.update_guarded(view,Ghost(joint::Record::Control {state:self.state()}),Ghost(joint::Change::Control {event}));view.finish();
    }
    /// Reported callback errors are opaque inputs, not a proof about callbacks.
    /// The first payload is retained; a later payload is returned to its caller.
    pub fn record_setup_failure(&mut self,error:E)->(unused:Option<E>)
        requires old(self).wf(),ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).state()==(State {failed:true,..old(self).state()}),final(self).cleanup_error()==old(self).cleanup_error(),
            final(self).setup_error()==if old(self).setup_error().is_some() {old(self).setup_error()} else {Some(error)},
            unused==if old(self).setup_error().is_some() {Some(error)} else {None},
    {
        if self.failed.is_some() {return Some(error);}
        let ghost before=self.state();self.failed=Some(error);let journal=self.member.domain();let view=journal.write();
        proof {reveal(joint::control::step);reveal(joint::control::guard);}self.commit(view,Ghost(before),Ghost(Event::SetupFailure));None
    }
    pub fn record_cleanup_failure(&mut self,error:E)->(unused:Option<E>)
        requires old(self).wf(),ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).state()==(State {cleanup_failure:true,..old(self).state()}),final(self).setup_error()==old(self).setup_error(),
            final(self).cleanup_error()==if old(self).cleanup_error().is_some() {old(self).cleanup_error()} else {Some(error)},
            unused==if old(self).cleanup_error().is_some() {Some(error)} else {None},
    {
        if self.cleanup_failure.is_some() {return Some(error);}
        let ghost before=self.state();self.cleanup_failure=Some(error);let journal=self.member.domain();let view=journal.write();
        proof {reveal(joint::control::step);reveal(joint::control::guard);}self.commit(view,Ghost(before),Ghost(Event::CleanupFailure));None
    }
    pub open spec fn observed(&self,snapshot:&joint::Snapshot)->bool {
        snapshot.certified() && snapshot.journal_spec()==self.journal()
            && snapshot.last().contains_pair(self.key(),joint::Record::Control {state:self.state()})
    }
    pub(crate) fn certify(&self,view:&joint::ReadView)
        requires self.wf(),view.wf(),view.journal_spec()==self.journal(),
        ensures view.state().contains_pair(self.key(),joint::Record::Control {state:self.state()}),
    {self.member.certify(view);}
    pub fn execution_snapshot(&self)->(out:joint::Snapshot)
        requires self.wf(),ensures out.certified(),out.journal_spec()==self.journal(),
            out.last().contains_pair(self.key(),joint::Record::Control {state:self.state()}),
            self.history().len()<=out.events().len(),out.events().take(self.history().len() as int)==self.history(),
    {self.member.observe()}
}
impl<R,H,V> NativeRuntime<R,H,V> {
    pub fn poll_control<E>(&self,id:usize)->(out:Option<PollControl<E>>)
        requires self.wf(),ensures out.is_some()==self.state().control().registered(id),
            out.is_some() ==> out.unwrap().wf() && out.unwrap().bound(self) && out.unwrap().state().owner==id
                && out.unwrap().state().episode.is_none() && !out.unwrap().state().failed && !out.unwrap().state().cleanup_failure && !out.unwrap().state().restart,
    {
        if !self.kernel().contains(id) {return None;}
        let journal=self.execution_journal();
        let ghost state=State {native:self.joint_key(),owner:id,episode:None,work_domain:0,groups:None,failed:false,cleanup_failure:false,restart:false};
        let member=journal.allocate(Ghost(joint::Record::Control {state}));
        Some(PollControl {owner:id,episode:None,work_domain:0,failed:None,cleanup_failure:None,restart:false,native:Ghost(self.joint_key()),groups:Ghost(None),member})
    }
    /// Restart is only intent: it clears setup failure, never retained cleanup.
    pub fn request_restart<E>(&self,control:&mut PollControl<E>)->(out:Result<Option<E>,Error>)
        requires self.wf(),old(control).wf(),old(control).bound(self),
        ensures final(control).wf(),final(control).bound(self),final(control).key()==old(control).key(),
            final(control).cleanup_error()==old(control).cleanup_error(),
            out.is_err() ==> *final(control)==*old(control),
            out.is_ok() ==> final(control).setup_error().is_none() && out->Ok_0==old(control).setup_error()
                && final(control).state()==(State {failed:false,restart:self.state().control().phase_of(old(control).state().owner)!=Some(Phase::Inactive),..old(control).state()}),
    {
        let id=control.owner;
        if self.kernel().retired(id) {return Err(Error::InvalidState);}
        let phase=match self.kernel().phase(id) {Some(phase)=>phase,None=>return Err(Error::InvalidState)};
        let running=phase!=Phase::Inactive;let ghost before=control.state();let discarded=control.failed.take();control.restart=running;
        let journal=control.member.domain();let view=journal.write();self.certify_poll_control(&view);
        proof {reveal(Kernel::phase_of);reveal(Kernel::registered);reveal(Kernel::is_retired);reveal(Kernel::paper);reveal(joint::control::step);reveal(joint::control::guard);}
        control.commit(view,Ghost(before),Ghost(Event::Restart {running}));Ok(discarded)
    }
    #[allow(clippy::type_complexity)]
    pub fn begin_controlled_execution<C,G,I,E>(&mut self,id:usize,domain:u64,control:&mut PollControl<E>)
        ->(out:Result<(Execution<V,C,G,I>,Option<E>),Error>)
        requires old(self).wf(),old(control).wf(),old(control).bound(old(self)),
        ensures final(self).wf(),final(control).wf(),final(control).bound(final(self)),final(control).key()==old(control).key(),
            final(control).setup_error()==old(control).setup_error(),final(control).state().restart==old(control).state().restart,
            out.is_err() ==> *final(control)==*old(control),
            out.is_ok() ==> out->Ok_0.0.wf() && final(self).owns_execution(id,&out->Ok_0.0)
                && out->Ok_0.0.execution_journal()==Some(final(self).journal_spec()) && final(control).matches(&out->Ok_0.0)
                && final(control).state().groups==Some(out->Ok_0.0.cleanup_state().link().unwrap().1)
                && out->Ok_0.0.capture().is_some()
                && out->Ok_0.0.capture().unwrap().realms==final(self).registry().entries()[id].recipe().realms()
                && out->Ok_0.0.capture().unwrap().anchor==final(self).registry().entries()[id].recipe().anchor_port()
                && final(control).cleanup_error().is_none() && out->Ok_0.1==old(control).cleanup_error(),
    {
        if id!=control.owner || control.episode.is_some() || control.failed.is_some() || control.cleanup_failure.is_some() {return Err(Error::InvalidState);}
        let execution=self.begin_managed_execution(id,domain)?;
        let ghost before=control.state();let discarded=control.cleanup_failure.take();
        control.episode=execution.lifecycle_ticket();control.work_domain=domain;
        proof {execution.representation();execution.groups.execution_link();}
        control.groups=Ghost(Some(execution.cleanup_state().link().unwrap().1));
        let journal=control.member.domain();let view=journal.write();self.certify_poll_control(&view);
        proof {reveal(joint::control::step);reveal(joint::control::guard);}
        execution.groups.certify_membership(&view);
        control.commit(view,Ghost(before),Ghost(Event::Begin {episode:execution.origin().unwrap(),work_domain:domain,groups:execution.cleanup_state().link().unwrap().1}));Ok((execution,discarded))
    }
    pub fn retry_controlled_execution<C,G,I,E>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>,control:&mut PollControl<E>)
        ->(out:Result<(ActionTicket,Option<E>),Error>)
        requires old(self).wf(),old(execution).wf(),old(control).wf(),old(control).bound(old(self)),
        ensures final(self).wf(),final(execution).wf(),final(control).wf(),final(control).bound(final(self)),final(control).key()==old(control).key(),
            final(control).setup_error()==old(control).setup_error(),
            out.is_err() ==> *final(control)==*old(control),
            out.is_ok() ==> final(control).matches(final(execution)) && final(control).cleanup_error().is_none()
                && final(control).state()==(State {cleanup_failure:false,..old(control).state()}) && out->Ok_0.1==old(control).cleanup_error()
                && out->Ok_0.0.id==id && out->Ok_0.0.generation==old(execution).origin().unwrap().generation
                && out->Ok_0.0.action==old(self).state().protocol().next_id()
                && !final(execution).cleanup_state().any_failed()
                && final(self).state().protocol().cleanup_reply_enabled(out->Ok_0.0),
            final(execution).capture()==old(execution).capture(),final(execution).phase_spec()==old(execution).phase_spec(),
            out.is_err() ==> *final(execution)==*old(execution) && final(self).state().same(&old(self).state()),
            final(execution).status_links()==old(execution).status_links(),
    {
        proof {self.state().same_reflexive();}
        if id!=control.owner || control.cleanup_failure.is_none() || !control.matches_execution(execution) {return Err(Error::InvalidState);}
        let ticket=self.retry_managed_execution(id,execution)?;
        let ghost before=control.state();let discarded=control.cleanup_failure.take();let journal=control.member.domain();let view=journal.write();
        proof {reveal(joint::control::step);reveal(joint::control::guard);}
        control.commit(view,Ghost(before),Ghost(Event::Retry {ticket}));Ok((ticket,discarded))
    }
    pub fn release_controlled_execution<C,G,I,E>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>,control:&mut PollControl<E>)
        ->(out:Result<(CleanupOutcome,ReleasedNativeValues<V>),Error>)
        requires old(self).wf(),old(execution).wf(),old(control).wf(),old(control).bound(old(self)),
        ensures final(self).wf(),final(execution).wf(),final(control).wf(),final(control).bound(final(self)),final(control).key()==old(control).key(),
            final(control).setup_error()==old(control).setup_error(),final(control).cleanup_error()==old(control).cleanup_error(),
            out.is_err() ==> *final(control)==*old(control),
            out.is_ok() ==> !final(self).episode_owners().contains_key(id)
                && final(control).state()==(State {episode:None,groups:None,restart:false,..old(control).state()}),
            final(execution).status_links()==old(execution).status_links(),
    {
        if id!=control.owner || !control.matches_execution(execution) {return Err(Error::InvalidState);}
        let released=self.release_managed_execution(id,execution)?;
        let ghost before=control.state();control.episode=None;control.groups=Ghost(None);control.restart=false;
        let journal=control.member.domain();let view=journal.write();self.certify_poll_control(&view);
        proof {reveal(joint::control::step);reveal(joint::control::guard);}
        control.commit(view,Ghost(before),Ghost(Event::Release));Ok(released)
    }
}
}
