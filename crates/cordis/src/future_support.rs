//! Shared host-side polling boundary. The caller owns and retains the future,
//! interprets its output, and decides whether other work must still be polled.
use std::future::Future;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::Pin;
use std::task::{Context, Poll};

/// Catch a user future's polling panic without consuming the future or changing
/// Pending into completion. Future construction and destruction are separate
/// boundaries handled by their owners.
pub(crate) fn poll_catching_unwind<F: Future + ?Sized>(
    future: Pin<&mut F>,
    cx: &mut Context<'_>,
) -> std::thread::Result<Poll<F::Output>> {
    catch_unwind(AssertUnwindSafe(|| future.poll(cx)))
}
