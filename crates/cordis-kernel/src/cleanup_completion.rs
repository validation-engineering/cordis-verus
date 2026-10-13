//! Actual awaited outputs authorize queue completion without a host-supplied
//! success flag. Foreign I/O truth is not inferred from a callback's return.
use super::CleanupQueue;
use crate::async_completion::Completion;
use crate::cleanup_journal::{RestoreOutcome, RestoreTicket};
use vstd::prelude::*;

verus! {

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum CleanupPolicy { RetainFailure, DrainConsumed }

pub struct CleanupReport<E,T> {
    pub result:Result<(),E>,
    pub outcome:RestoreOutcome,
    /// Dropping user factories can reenter the host. Return them to the caller
    /// so destruction happens after its bookkeeping lock is released.
    pub discarded:Option<T>,
}

pub open spec fn outcome<E,T>(result:Result<(),E>,retry:Option<T>,policy:CleanupPolicy)->RestoreOutcome {
    if result.is_ok() {RestoreOutcome::Succeeded}
    else if retry.is_some() || policy==CleanupPolicy::RetainFailure {RestoreOutcome::Failed} else {RestoreOutcome::Drained}
}
pub open spec fn retained<E,T>(result:Result<(),E>,retry:Option<T>)->Option<T> {
    if result.is_err() {retry} else {None}
}

impl<T> CleanupQueue<T> {
    fn reply_pending(&self,ticket:RestoreTicket)->(out:bool)
        requires self.wf(),
        ensures out==(self.issued() && self.protocol().selected()==Some(ticket) && !self.protocol().failed_spec()),
    {self.in_flight && self.journal.current()==Some(ticket)}

    fn accept_result<E>(&mut self,ticket:RestoreTicket,result:Result<(),E>,retry:Option<T>,policy:CleanupPolicy)
        ->(out:CleanupReport<E,T>)
        requires old(self).wf(),old(self).issued(),old(self).protocol().selected()==Some(ticket),!old(self).protocol().failed_spec(),
        ensures final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),out.result==result,out.outcome==outcome(result,retry,policy),
            out.discarded==if result.is_ok() {retry} else {None},
            !final(self).issued(),final(self).protocol().waiting()==old(self).protocol().waiting(),
            final(self).slots()==old(self).slots().update(ticket.token as int,retained(result,retry)),
            final(self).protocol().failed_spec()==(out.outcome==RestoreOutcome::Failed),
            final(self).protocol().selected()==if out.outcome==RestoreOutcome::Failed {Some(ticket)} else {None},
    {
        let selected=if result.is_ok() {RestoreOutcome::Succeeded}
            else if retry.is_some() || policy==CleanupPolicy::RetainFailure {RestoreOutcome::Failed} else {RestoreOutcome::Drained};
        let (retained,discarded)=if result.is_ok() {(None,retry)} else {(retry,None)};
        let _accepted=self.complete(ticket,selected,retained);
        assert(_accepted.is_ok());
        CleanupReport {result,outcome:selected,discarded}
    }

    /// Synchronous adapter results use the same outcome policy as Futures.
    /// The caller still owns the obligation to execute the actual operation.
    #[allow(clippy::type_complexity)]
    pub fn complete_result<E>(&mut self,ticket:RestoreTicket,result:Result<(),E>,retry:Option<T>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,T>,(RestoreTicket,Result<(),E>,Option<T>)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),
            out.is_ok()==(old(self).issued() && old(self).protocol().selected()==Some(ticket) && !old(self).protocol().failed_spec()),
            out.is_err() ==> final(self).same(old(self)) && out->Err_0==(ticket,result,retry),
            out.is_ok() ==> out->Ok_0.result==result && out->Ok_0.outcome==outcome(result,retry,policy)
                && out->Ok_0.discarded==if result.is_ok() {retry} else {None} && !final(self).issued(),
    {
        if !self.reply_pending(ticket) {return Err((ticket,result,retry));}
        Ok(self.accept_result(ticket,result,retry,policy))
    }

    /// A real Future's output and the captured request arrive as one owned
    /// value. Rejection returns both the completion and retry payload unchanged.
    #[allow(clippy::type_complexity)]
    pub fn complete_future<E>(&mut self,completion:Completion<RestoreTicket,Result<(),E>>,retry:Option<T>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,T>,(Completion<RestoreTicket,Result<(),E>>,Option<T>)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),
            out.is_ok()==(old(self).issued() && old(self).protocol().selected()==Some(completion.argument()) && !old(self).protocol().failed_spec()),
            out.is_err() ==> final(self).same(old(self)) && out->Err_0==(completion,retry),
            out.is_ok() ==> out->Ok_0.result==completion.result()
                && out->Ok_0.outcome==outcome(completion.result(),retry,policy)
                && out->Ok_0.discarded==if completion.result().is_ok() {retry} else {None}
                && final(self).slots()==old(self).slots().update(completion.argument().token as int,retained(completion.result(),retry))
                && !final(self).issued()
                && final(self).protocol().waiting()==old(self).protocol().waiting()
                && final(self).protocol().failed_spec()==(outcome(completion.result(),retry,policy)==RestoreOutcome::Failed)
                && final(self).protocol().selected()==if outcome(completion.result(),retry,policy)==RestoreOutcome::Failed {Some(completion.argument())} else {None},
    {
        let ticket=*completion.argument_ref();
        if !self.reply_pending(ticket) {return Err((completion,retry));}
        let (ticket,result)=completion.into_parts();
        Ok(self.accept_result(ticket,result,retry,policy))
    }

    /// Factory/poll panics are explicitly failures. This entry point cannot
    /// forge an awaited success; the existing nonretryable Drained policy stays
    /// distinct from successful restoration.
    #[allow(clippy::type_complexity)]
    pub fn complete_failure<E>(&mut self,ticket:RestoreTicket,error:E,retry:Option<T>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,T>,(RestoreTicket,E,Option<T>)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),
            out.is_ok()==(old(self).issued() && old(self).protocol().selected()==Some(ticket) && !old(self).protocol().failed_spec()),
            out.is_err() ==> final(self).same(old(self)) && out->Err_0==(ticket,error,retry),
            out.is_ok() ==> out->Ok_0.result==Err(error) && out->Ok_0.outcome!=RestoreOutcome::Succeeded
                && out->Ok_0.outcome==outcome::<E,T>(Err(error),retry,policy)
                && out->Ok_0.discarded.is_none()
                && final(self).slots()==old(self).slots().update(ticket.token as int,retry)
                && !final(self).issued(),
    {
        if !self.reply_pending(ticket) {return Err((ticket,error,retry));}
        Ok(self.accept_result(ticket,Err(error),retry,policy))
    }
}

pub struct ValueCleanupReport<C,X> {
    pub report:CleanupReport<crate::reversible_value::ValueError,crate::lifecycle_state::registration::shared_child::ChildCleanup<C,X>>,
    pub restored:Option<crate::reversible_value::Snapshot>,
}
impl<C,X> ValueCleanupReport<C,X> {
    pub open spec fn corresponds(&self,inverse:crate::reversible_value::Inverse)->bool {
        &&& self.report.result.is_ok()==self.restored.is_some()
        &&& self.report.outcome==if self.restored.is_some() {RestoreOutcome::Succeeded} else {RestoreOutcome::Failed}
        &&& self.report.discarded.is_none()
        &&& self.restored.is_some() ==> self.restored.unwrap().certified() && self.restored.unwrap().state()==inverse.state().before
    }
}
impl<C,X> CleanupQueue<crate::lifecycle_state::registration::shared_child::ChildCleanup<C,X>> {
    /// The callback result is derived here from the real guarded write. A
    /// wrong/stale ticket is rejected before that write can execute.
    pub(crate) fn restore_value(&mut self,ticket:RestoreTicket,inverse:crate::reversible_value::Inverse)
        ->(out:Result<ValueCleanupReport<C,X>,(RestoreTicket,crate::reversible_value::Inverse)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),
            out.is_ok()==(old(self).issued() && old(self).protocol().selected()==Some(ticket) && !old(self).protocol().failed_spec()),
            out.is_err() ==> final(self).same(old(self)) && out->Err_0==(ticket,inverse),
            out.is_ok() ==> out->Ok_0.corresponds(inverse) && !final(self).issued()
                && final(self).slots()==old(self).slots().update(ticket.token as int,if out->Ok_0.restored.is_some() {None}
                    else {Some(crate::lifecycle_state::registration::shared_child::ChildCleanup::Value(inverse))})
                && final(self).protocol().failed_spec()==out->Ok_0.restored.is_none(),
    {
        if !self.reply_pending(ticket) {return Err((ticket,inverse));}
        match inverse.restore() {
            Ok(snapshot)=>{
                let report=self.accept_result(ticket,Ok(()),None,CleanupPolicy::RetainFailure);
                Ok(ValueCleanupReport {report,restored:Some(snapshot)})
            },
            Err(inverse)=>{
                let report=self.accept_result(ticket,Err(crate::reversible_value::ValueError::Interference),
                    Some(crate::lifecycle_state::registration::shared_child::ChildCleanup::Value(inverse)),CleanupPolicy::RetainFailure);
                Ok(ValueCleanupReport {report,restored:None})
            },
        }
    }
}

pub enum CleanupDispatch<C,X> {
    Host {ticket:RestoreTicket,action:crate::lifecycle_state::registration::shared_child::ChildCleanup<C,X>},
    Value {ticket:RestoreTicket,completion:ValueCleanupReport<C,X>},
}
impl<C,X> CleanupDispatch<C,X> {
    pub open spec fn from_slot(&self,slots:Seq<Option<crate::lifecycle_state::registration::shared_child::ChildCleanup<C,X>>>)->bool {
        match self {
            Self::Host {ticket,action}=>ticket.token<slots.len() && slots[ticket.token as int]==Some(*action)
                && !(*action is Value),
            Self::Value {ticket,completion}=>ticket.token<slots.len() && slots[ticket.token as int].is_some()
                && slots[ticket.token as int].unwrap() is Value && completion.corresponds(slots[ticket.token as int].unwrap()->Value_0),
        }
    }
}
impl<C,X> CleanupQueue<crate::lifecycle_state::registration::shared_child::ChildCleanup<C,X>> {
    /// Select, execute and acknowledge the actual stored inverse in one checked
    /// call. Ordinary host code cannot replace it between these operations.
    pub fn dispatch(&mut self)->(out:Result<Option<CleanupDispatch<C,X>>,crate::cleanup_journal::RestoreError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().from_slot(old(self).slots()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap() is Value ==> {
                let report=out->Ok_0.unwrap();let ticket=report->Value_ticket;let completion=report->Value_completion;
                &&& final(self).slots()==old(self).slots().update(ticket.token as int,
                    if completion.restored.is_some() {None} else {old(self).slots()[ticket.token as int]})
                &&& final(self).protocol().failed_spec()==completion.restored.is_none()
            },
    {
        let ghost before=*self;
        let (ticket,action)=match self.pop()? {None=>return Ok(None),Some(pair)=>pair};
        match action {
            crate::lifecycle_state::registration::shared_child::ChildCleanup::Value(inverse)=>{
                let completion=match self.restore_value(ticket,inverse) {Ok(report)=>report,Err(_)=>{assert(false);return Err(crate::cleanup_journal::RestoreError::InvalidState);}};
                assert(self.slots()==before.slots().update(ticket.token as int,
                    if completion.restored.is_some() {None} else {before.slots()[ticket.token as int]}));
                Ok(Some(CleanupDispatch::Value {ticket,completion}))
            },
            action=>Ok(Some(CleanupDispatch::Host {ticket,action})),
        }
    }
}

}
