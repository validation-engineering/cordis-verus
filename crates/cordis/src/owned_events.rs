//! Lifecycle-aware admission and draining for event subscriptions.
//!
//! `close` prevents new invocations, including listeners in older snapshots.
//! `drain` additionally waits for invocations that already started. Async work
//! belongs to the dispatch future: dropping that future cancels it. Retained
//! async waterfall continuations extend that invocation until dropped or settled.
//! Nothing is detached or forcibly interrupted.

use crate::events::EventSubscription;
use crate::runtime::{AsyncSetup, Setup};
use std::collections::BTreeMap;
use std::future::Future;
use std::pin::Pin;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Waker};

/// An episode-bound context usable for automatic listener cleanup.
/// Implemented for both synchronous `Setup` and owned `AsyncSetup` handles.
pub trait EventOwner {
    fn event_owner(&self) -> AsyncSetup;
}
impl EventOwner for AsyncSetup {
    fn event_owner(&self) -> AsyncSetup {
        self.clone()
    }
}
impl EventOwner for Setup<'_> {
    fn event_owner(&self) -> AsyncSetup {
        self.to_async()
    }
}

struct State {
    accepting: bool,
    closed: bool,
    active: usize,
    next_waiter: u64,
    waiters: BTreeMap<u64, Waker>,
}
pub(crate) struct Gate(Mutex<State>);
impl Gate {
    pub(crate) fn new(accepting: bool) -> Arc<Self> {
        Arc::new(Self(Mutex::new(State {
            accepting,
            closed: false,
            active: 0,
            next_waiter: 0,
            waiters: BTreeMap::new(),
        })))
    }
    fn activate(&self) -> bool {
        let mut state = self.0.lock().unwrap();
        if state.closed {
            return false;
        }
        state.accepting = true;
        true
    }
    pub(crate) fn enter(self: &Arc<Self>) -> Option<Invocation> {
        let mut state = self.0.lock().unwrap();
        if !state.accepting {
            return None;
        }
        state.active = state
            .active
            .checked_add(1)
            .expect("too many event invocations");
        Some(Invocation(Some(self.clone())))
    }
    fn close(self: &Arc<Self>) -> (bool, Invocation) {
        let mut state = self.0.lock().unwrap();
        let changed = !state.closed;
        state.closed = true;
        state.accepting = false;
        // Each closer keeps callback destruction in the drain boundary. A
        // concurrent closer can take the last callback while this one observes
        // an empty slot, so every close needs its own lease.
        state.active = state
            .active
            .checked_add(1)
            .expect("too many event invocations");
        (changed, Invocation(Some(self.clone())))
    }
}

pub(crate) struct Invocation(Option<Arc<Gate>>);
impl Invocation {
    pub(crate) fn untracked() -> Self {
        Self(None)
    }
}
impl Drop for Invocation {
    fn drop(&mut self) {
        let Some(gate) = &self.0 else { return };
        let waiters = {
            let mut state = gate.0.lock().unwrap();
            state.active -= 1;
            if state.active == 0 {
                std::mem::take(&mut state.waiters)
            } else {
                BTreeMap::new()
            }
        };
        // Waking may synchronously reenter the subscription.
        for waker in waiters.into_values() {
            waker.wake();
        }
    }
}

pub(crate) fn track<F: Future + ?Sized, L>(future: Pin<Box<F>>, lease: L) -> Tracked<F, L> {
    Tracked {
        future: Some(future),
        lease: Some(lease),
    }
}

pub(crate) struct Tracked<F: Future + ?Sized, L> {
    // Fields drop in this order, including when a user destructor panics.
    future: Option<Pin<Box<F>>>,
    lease: Option<L>,
}
impl<F: Future + ?Sized, L> Unpin for Tracked<F, L> {}
impl<F: Future + ?Sized, L> Future for Tracked<F, L> {
    type Output = F::Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();
        let result = this
            .future
            .as_mut()
            .expect("completed listener polled again")
            .as_mut()
            .poll(cx);
        if result.is_ready() {
            drop(this.future.take());
            drop(this.lease.take());
        }
        result
    }
}

struct Owned<C: ?Sized> {
    subscription: EventSubscription<C>,
    gate: Arc<Gate>,
}
impl<C: ?Sized> Drop for Owned<C> {
    fn drop(&mut self) {
        let (_, _closing) = self.gate.close();
        self.subscription.dispose();
        self.subscription.clear_owned_callback();
    }
}

/// Cloneable subscription with admission control. Dropping the last handle
/// closes it; an owner-bound registration retains a handle until owner cleanup.
/// Closing does not wait for admitted callbacks and cannot interrupt them.
/// Callback captures are dropped synchronously; their destructors may block.
pub struct OwnedSubscription<C: ?Sized> {
    inner: Arc<Owned<C>>,
}
impl<C: ?Sized> Clone for OwnedSubscription<C> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}
impl<C: ?Sized> OwnedSubscription<C> {
    pub(crate) fn new(subscription: EventSubscription<C>, gate: Arc<Gate>) -> Self {
        Self {
            inner: Arc::new(Owned { subscription, gate }),
        }
    }
    /// Stop admitting invocations. Returns true only on the first close.
    pub fn close(&self) -> bool {
        let (changed, _closing) = self.inner.gate.close();
        self.inner.subscription.dispose();
        self.inner.subscription.clear_owned_callback();
        changed
    }
    pub fn is_closed(&self) -> bool {
        self.inner.gate.0.lock().unwrap().closed
    }
    /// Outstanding callback/continuation leases, including concurrent closure
    /// teardown during `close`.
    pub fn in_flight(&self) -> usize {
        self.inner.gate.0.lock().unwrap().active
    }
    /// Close immediately, then wait for all admitted callbacks, retained async
    /// continuations, and owned callback/future destructors. Cancelling this
    /// future keeps the subscription closed.
    /// Never await this from this subscription's own callback: it includes that
    /// callback and would wait for itself. Call `close` there instead.
    pub fn drain(&self) -> Drain {
        self.close();
        Drain {
            gate: self.inner.gate.clone(),
            waiter: None,
        }
    }
}
impl<C: ?Sized + Send + Sync + 'static> OwnedSubscription<C> {
    /// Attach a dormant registration to an episode before accepting callbacks.
    pub(crate) fn attach(self, owner: &AsyncSetup) -> Result<Self, String> {
        owner.ensure_active()?;
        let cleanup = self.clone();
        owner.on_cleanup_async(move || async move {
            cleanup.drain().await;
            Ok(())
        })?;
        if let Err(error) = owner.ensure_active() {
            self.close();
            return Err(error);
        }
        if !self.inner.gate.activate() {
            return Err("event owner has begun cleanup".into());
        }
        Ok(self)
    }
}

/// A cancellation-safe wait for a closed subscription's admitted invocations.
#[must_use = "poll or await drain to wait for callbacks"]
pub struct Drain {
    gate: Arc<Gate>,
    waiter: Option<u64>,
}
impl Future for Drain {
    type Output = ();
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        let this = self.get_mut();
        // A custom waker may run code from clone/drop too.
        let mut waker = Some(cx.waker().clone());
        let (ready, previous) = {
            let mut state = this.gate.0.lock().unwrap();
            if state.active == 0 {
                (
                    true,
                    this.waiter.take().and_then(|id| state.waiters.remove(&id)),
                )
            } else {
                let id = *this.waiter.get_or_insert_with(|| {
                    let id = state.next_waiter;
                    state.next_waiter =
                        id.checked_add(1).expect("event drain identities exhausted");
                    id
                });
                (false, state.waiters.insert(id, waker.take().unwrap()))
            }
        };
        drop(previous);
        if ready {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}
impl Drop for Drain {
    fn drop(&mut self) {
        let removed = self
            .waiter
            .take()
            .and_then(|id| self.gate.0.lock().unwrap().waiters.remove(&id));
        drop(removed);
    }
}
