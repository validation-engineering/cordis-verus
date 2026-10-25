//! Ordinary-host ownership of one cleanup invocation.
//!
//! A completion carries the retry factory from the same attempt. Callers cannot
//! construct or split that pair; the verified queue still checks its receipt.
//! Keep the completed attempt alive until acknowledgement has left the Episode
//! lock, because dropping its Future may execute user code.
use super::super::{
    panic_message, CallbackError, CallbackResult, CleanupAction, CleanupCallback, Cleanups,
    RetryCleanup,
};
use crate::future_support::poll_catching_unwind;
use cordis_kernel::async_completion::{invoke_future, Completion};
use cordis_kernel::cleanup_journal::RestoreTicket;
use cordis_kernel::cleanup_queue::completion::{CleanupPolicy, CleanupReport};
use cordis_kernel::poll_result::normalize_poll;
use cordis_kernel::reversible_value::managed::interleaving::history::lifecycle::callbacks::HostAction;
use std::future::Future;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::Pin;
use std::task::{Context as TaskContext, Poll};

type CompletionFuture =
    Pin<Box<dyn Future<Output = Completion<RestoreTicket, CallbackResult>> + Send>>;

enum CleanupReply {
    Awaited(Completion<RestoreTicket, CallbackResult>),
    Failed(RestoreTicket, CallbackError),
}

pub(in crate::runtime) struct CleanupCompletion {
    reply: CleanupReply,
    retry: Option<RetryCleanup>,
}

pub(in crate::runtime) enum RejectedCleanup {
    Awaited(
        Completion<RestoreTicket, CallbackResult>,
        Option<CleanupAction>,
    ),
    Failed(RestoreTicket, CallbackError, Option<CleanupAction>),
}

impl RejectedCleanup {
    pub(in crate::runtime) fn discard(self) {
        match self {
            Self::Awaited(completion, retry) => drop((completion, retry)),
            Self::Failed(ticket, error, retry) => drop((ticket, error, retry)),
        }
    }
}

pub(in crate::runtime) struct RunningCleanup {
    ticket: RestoreTicket,
    future: CompletionFuture,
    retry: Option<RetryCleanup>,
}

impl RunningCleanup {
    pub(in crate::runtime) fn start(
        ticket: RestoreTicket,
        cleanup: CleanupCallback,
    ) -> Result<Self, CleanupCompletion> {
        let (result, retry) = match cleanup {
            CleanupCallback::Payload { .. } => {
                unreachable!("typed inverse runs inside the checked dispatcher")
            }
            CleanupCallback::Once(cleanup) => (
                catch_unwind(AssertUnwindSafe(|| {
                    invoke_future(ticket, (), |()| cleanup())
                })),
                None,
            ),
            CleanupCallback::Retryable(mut cleanup) => {
                let result = catch_unwind(AssertUnwindSafe(|| {
                    invoke_future(ticket, (), |()| cleanup())
                }));
                (result, Some(cleanup))
            }
        };
        match result {
            Ok(future) => Ok(Self {
                ticket,
                future: Box::pin(future.complete()),
                retry,
            }),
            Err(panic) => Err(CleanupCompletion {
                reply: CleanupReply::Failed(ticket, CallbackError::panic(panic_message(panic))),
                retry,
            }),
        }
    }

    /// Pending retains the Future and factory. On Ready, the caller removes
    /// this attempt, acknowledges the paired result, then drops this Future.
    pub(in crate::runtime) fn poll(&mut self, cx: &mut TaskContext<'_>) -> Poll<CleanupCompletion> {
        let reply = match normalize_poll(poll_catching_unwind(self.future.as_mut(), cx), |panic| {
            CallbackError::panic(panic_message(panic))
        }) {
            Poll::Pending => return Poll::Pending,
            Poll::Ready(Ok(completion)) => CleanupReply::Awaited(completion),
            Poll::Ready(Err(error)) => CleanupReply::Failed(self.ticket, error),
        };
        Poll::Ready(CleanupCompletion {
            reply,
            retry: self.retry.take(),
        })
    }
}

impl Cleanups {
    pub(in crate::runtime) fn complete_reply(
        &mut self,
        group: usize,
        completion: CleanupCompletion,
        policy: CleanupPolicy,
    ) -> Result<CleanupReport<CallbackError, CleanupAction>, RejectedCleanup> {
        let retry = completion.retry.map(HostAction::Retryable);
        match completion.reply {
            CleanupReply::Awaited(completion) => self
                .protocol
                .complete_future(group, completion, retry, policy)
                .map_err(|(completion, retry)| RejectedCleanup::Awaited(completion, retry)),
            CleanupReply::Failed(ticket, error) => self
                .protocol
                .complete_failure(group, ticket, error, retry, policy)
                .map_err(|(ticket, error, retry)| RejectedCleanup::Failed(ticket, error, retry)),
        }
    }
}
