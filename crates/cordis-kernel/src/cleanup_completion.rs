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
        ensures final(self).wf(),out.result==result,out.outcome==outcome(result,retry,policy),
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

    /// A real Future's output and the captured request arrive as one owned
    /// value. Rejection returns both the completion and retry payload unchanged.
    #[allow(clippy::type_complexity)]
    pub fn complete_future<E>(&mut self,completion:Completion<RestoreTicket,Result<(),E>>,retry:Option<T>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,T>,(Completion<RestoreTicket,Result<(),E>>,Option<T>)>)
        requires old(self).wf(),
        ensures final(self).wf(),
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
        ensures final(self).wf(),
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

}
