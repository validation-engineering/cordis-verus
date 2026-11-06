//! Actual root invocation tickets and their queued/running Futures.
//! Only this owner constructs their pairing. Scheduling remains a host boundary;
//! admission, first poll, cancellation and completion use the checked work owner.
use super::*;

/// Only a queued future may be discarded on withdrawal. Once its first poll
/// begins, the runtime owns it until it lands and can register its inverse.
type RootFuture = Pin<Box<dyn Future<Output = WorkReceipt<CallbackResult>> + Send>>;
pub(super) struct RootSetup(RootState);

enum RootState {
    Dormant,
    Queued(WorkTicket, RootFuture),
    Running(WorkTicket, RootFuture),
    Done,
}
impl RootSetup {
    pub(super) fn dormant() -> Self {
        Self(RootState::Dormant)
    }
    pub(super) fn done() -> Self {
        Self(RootState::Done)
    }
    pub(super) fn is_pending(&self) -> bool {
        matches!(self.0, RootState::Queued(..) | RootState::Running(..))
    }
    pub(super) fn is_done(&self) -> bool {
        matches!(self.0, RootState::Done)
    }
    pub(super) fn poll(
        &mut self,
        withdrawing: bool,
        episode: &AsyncSetup,
        cx: &mut TaskContext<'_>,
    ) -> Option<Poll<CallbackResult>> {
        match std::mem::replace(&mut self.0, RootState::Done) {
            RootState::Queued(ticket, future) if withdrawing => {
                {
                    let mut state = lock(&episode.state);
                    state.execution.withdraw_work();
                    assert!(
                        state.execution.cancel_queued_root(ticket),
                        "only an unpolled root is discarded"
                    );
                }
                drop(future);
                None
            }
            RootState::Queued(ticket, mut future) | RootState::Running(ticket, mut future) => {
                assert!(
                    lock(&episode.state).execution.start_root(ticket),
                    "exact admitted root"
                );
                Some(
                    match normalize_poll(poll_catching_unwind(future.as_mut(), cx), |panic| {
                        CallbackError::panic(panic_message(panic))
                    }) {
                        Poll::Pending => {
                            self.0 = RootState::Running(ticket, future);
                            Poll::Pending
                        }
                        Poll::Ready(Ok(receipt)) => {
                            let completed = lock(&episode.state).execution.complete_root(receipt);
                            Poll::Ready(completed.ok().expect("actual root completion"))
                        }
                        Poll::Ready(Err(error)) => {
                            let failed = lock(&episode.state).execution.fail_root(ticket, error);
                            Poll::Ready(Err(failed.expect("exact failed root")))
                        }
                    },
                )
            }
            state => {
                self.0 = state;
                None
            }
        }
    }
}
pub(super) fn initialize_callback(
    callback: &mut RootBody,
    episode: &AsyncSetup,
) -> Result<RootSetup, CallbackError> {
    let item = lock(&episode.state)
        .execution
        .issue_root(episode.clone())
        .ok()
        .expect("one root invocation per episode");
    let ticket = item.ticket();
    let result = catch_unwind(AssertUnwindSafe(|| match callback {
        CheckedRootBody::Callback(callback) => item.run(callback),
        CheckedRootBody::Value(_) => item.run(|_| {
            RootOutput::Ready(Err(
                "native_value_program requires the native Runtime".into()
            ))
        }),
        CheckedRootBody::Managed(_) => item
            .run(|_| RootOutput::Ready(Err("native_function requires the native Runtime".into()))),
        CheckedRootBody::Services(_) => item.run(|_| {
            RootOutput::Ready(Err(
                "native_service_program requires the native Runtime".into()
            ))
        }),
    }));
    initialize_reply(episode, ticket, result)
}
pub(super) fn initialize_reply(
    episode: &AsyncSetup,
    ticket: WorkTicket,
    result: std::thread::Result<WorkReceipt<RootReply>>,
) -> Result<RootSetup, CallbackError> {
    match result {
        Ok(reply) => match reply.dispatch() {
            RootDispatch::Ready(receipt) => {
                let completed = lock(&episode.state).execution.complete_root(receipt);
                completed.ok().expect("actual synchronous root result")?;
                Ok(RootSetup::done())
            }
            RootDispatch::Pending(pending) => Ok(RootSetup(RootState::Queued(
                ticket,
                Box::pin(pending.complete()),
            ))),
        },
        Err(panic) => {
            let error = CallbackError::panic(panic_message(panic));
            Err(lock(&episode.state)
                .execution
                .fail_root(ticket, error)
                .expect("issued factory failed"))
        }
    }
}
