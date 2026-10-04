//! Typed Cordis event dispatch in the ordinary Rust host (outside Verus).
//!
//! Dispatch uses a snapshot and never holds the registry lock while calling user
//! code. Removal affects subsequent snapshots; once registrations are atomically
//! claimed before invocation. `Some` is the typed bail decision (including
//! `Some(false)`). Synchronous dispatch and `AsyncWaterfall` propagate panics.
//! `AsyncEvent` catches factory/poll panics alongside callback errors; user-defined
//! destructor panics are not guaranteed to be intercepted. Async dispatch does
//! not detach work: the returned future must be polled to completion.

//!
//! Use `on_in` for callbacks that borrow an episode's services. It installs a
//! cleanup which closes admission and waits for in-flight dispatches. The
//! returned handle may be dropped: the episode retains it until cleanup.
//!
//! ```
//! use cordis::{Context, Plugin, Runtime};
//! use cordis::events::{Event, EventScope};
//! let event = Event::<String>::new();
//! let mut runtime = Runtime::new();
//! runtime.mount(&Context::new(), None, Plugin::new("logger", move |setup| {
//!     event.on_in(setup, EventScope::Global, |message| {
//!         println!("{message}");
//!     })?;
//!     Ok(())
//! })).unwrap();
//! ```
//!
//! Standalone applications can explicitly close and drain subscriptions:
//!
//! ```
//! # async fn example() {
//! use cordis::events::{AsyncEvent, EventScope};
//! use std::sync::Arc;
//! let event = AsyncEvent::<u32>::new();
//! let subscription = event.on_owned(EventScope::Global, |value| async move {
//!     assert_eq!(*value, 7);
//!     Ok(())
//! });
//! event.emit(EventScope::Global, Arc::new(7)).await.unwrap();
//! subscription.drain().await;
//! assert_eq!(event.listener_count(), 0);
//! # }
//! ```

use crate::owned_events::{track, EventOwner, Gate, Invocation, OwnedSubscription};
use cordis_kernel::Port;
use std::any::Any;
use std::future::Future;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, Weak};
use std::task::{Context, Poll};

/// Global dispatch reaches every listener; global listeners bypass filtering.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EventScope {
    Global,
    Relevant(Port),
    /// Application-defined context identity, optionally selected by a predicate.
    Custom(u64),
}
impl EventScope {
    fn matches(self, listener: Self) -> bool {
        self == Self::Global || listener == Self::Global || self == listener
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct EventOptions {
    pub prepend: bool,
    pub once: bool,
}

struct Listener<C: ?Sized> {
    id: u64,
    scope: EventScope,
    once: bool,
    claimed: AtomicBool,
    callback: Mutex<Option<Arc<C>>>,
    gate: Option<Arc<Gate>>,
}
struct Registry<C: ?Sized> {
    next_id: u64,
    listeners: Vec<Arc<Listener<C>>>,
}
struct Channel<C: ?Sized> {
    registry: Arc<Mutex<Registry<C>>>,
}
impl<C: ?Sized> Clone for Channel<C> {
    fn clone(&self) -> Self {
        Self {
            registry: self.registry.clone(),
        }
    }
}
impl<C: ?Sized> Channel<C> {
    fn new() -> Self {
        Self {
            registry: Arc::new(Mutex::new(Registry {
                next_id: 0,
                listeners: Vec::new(),
            })),
        }
    }
    fn register(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: Arc<C>,
    ) -> EventSubscription<C> {
        self.register_gated(scope, options, callback, None)
    }
    fn register_owned(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: Arc<C>,
        accepting: bool,
    ) -> OwnedSubscription<C> {
        let gate = Gate::new(accepting);
        let subscription = self.register_gated(scope, options, callback, Some(gate.clone()));
        OwnedSubscription::new(subscription, gate)
    }
    fn register_gated(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: Arc<C>,
        gate: Option<Arc<Gate>>,
    ) -> EventSubscription<C> {
        let mut registry = self.registry.lock().expect("event registry lock poisoned");
        let id = registry.next_id;
        registry.next_id = id
            .checked_add(1)
            .expect("event listener identities exhausted");
        let listener = Arc::new(Listener {
            id,
            scope,
            once: options.once,
            claimed: AtomicBool::new(false),
            callback: Mutex::new(Some(callback)),
            gate,
        });
        let weak_listener = Arc::downgrade(&listener);
        if options.prepend {
            registry.listeners.insert(0, listener);
        } else {
            registry.listeners.push(listener);
        }
        EventSubscription {
            registry: Arc::downgrade(&self.registry),
            listener: weak_listener,
            id,
        }
    }
    fn snapshot(&self, filter: impl Fn(EventScope) -> bool) -> Vec<Arc<Listener<C>>> {
        // Predicates are user code too: evaluate them after releasing the lock.
        let listeners = self
            .registry
            .lock()
            .expect("event registry lock poisoned")
            .listeners
            .clone();
        listeners
            .into_iter()
            .filter(|listener| listener.scope == EventScope::Global || filter(listener.scope))
            .collect()
    }
    fn claim(&self, listener: &Listener<C>) -> Option<Claimed<C>> {
        let invocation = match &listener.gate {
            Some(gate) => gate.enter()?,
            None => Invocation::untracked(),
        };
        if listener.once {
            if listener.claimed.swap(true, Ordering::AcqRel) {
                return None;
            }
            remove(&self.registry, listener.id);
        }
        let callback = listener
            .callback
            .lock()
            .expect("event callback slot poisoned")
            .clone()?;
        Some(Claimed(Arc::new(CallbackLease {
            callback,
            _invocation: Arc::new(invocation),
        })))
    }
    fn count(&self) -> usize {
        self.registry
            .lock()
            .expect("event registry lock poisoned")
            .listeners
            .len()
    }
    fn off(&self, subscription: &EventSubscription<C>) -> bool {
        Weak::ptr_eq(&Arc::downgrade(&self.registry), &subscription.registry)
            && subscription.dispose()
    }
}

// A claimed callback environment drops before its admission permit. Shared
// leases also cover async continuations which escape their calling future.
struct CallbackLease<C: ?Sized> {
    callback: Arc<C>,
    _invocation: Arc<Invocation>,
}
struct Claimed<C: ?Sized>(Arc<CallbackLease<C>>);
impl<C: ?Sized> Clone for Claimed<C> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<C: ?Sized> Claimed<C> {
    fn callback(&self) -> &C {
        &self.0.callback
    }
}

/// Explicit cancellation token; dropping it does not unsubscribe. Ordinary
/// listeners already captured by a dispatch are still invoked after disposal.
pub struct EventSubscription<C: ?Sized> {
    registry: Weak<Mutex<Registry<C>>>,
    listener: Weak<Listener<C>>,
    id: u64,
}
impl<C: ?Sized> Clone for EventSubscription<C> {
    fn clone(&self) -> Self {
        Self {
            registry: self.registry.clone(),
            listener: self.listener.clone(),
            id: self.id,
        }
    }
}
impl<C: ?Sized> EventSubscription<C> {
    pub(crate) fn clear_owned_callback(&self) {
        if let Some(listener) = self.listener.upgrade() {
            if listener.gate.is_some() {
                let callback = listener
                    .callback
                    .lock()
                    .expect("event callback slot poisoned")
                    .take();
                drop(callback);
            }
        }
    }
    pub fn dispose(&self) -> bool {
        self.registry
            .upgrade()
            .is_some_and(|registry| remove(&registry, self.id))
    }
}
fn remove<C: ?Sized>(registry: &Mutex<Registry<C>>, id: u64) -> bool {
    let removed = {
        let mut registry = registry.lock().expect("event registry lock poisoned");
        let Some(index) = registry
            .listeners
            .iter()
            .position(|listener| listener.id == id)
        else {
            return false;
        };
        registry.listeners.remove(index)
    };
    drop(removed);
    true
}

type SyncCallback<T, R> = dyn Fn(&T) -> R + Send + Sync + 'static;
pub type Subscription<T, R = ()> = EventSubscription<SyncCallback<T, R>>;
pub type OwnedEventSubscription<T, R = ()> = OwnedSubscription<SyncCallback<T, R>>;

pub struct Event<T, R = ()> {
    channel: Channel<SyncCallback<T, R>>,
}
impl<T, R> Clone for Event<T, R> {
    fn clone(&self) -> Self {
        Self {
            channel: self.channel.clone(),
        }
    }
}
impl<T, R> Default for Event<T, R> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T, R> Event<T, R> {
    pub fn new() -> Self {
        Self {
            channel: Channel::new(),
        }
    }
    pub fn on(
        &self,
        scope: EventScope,
        callback: impl Fn(&T) -> R + Send + Sync + 'static,
    ) -> Subscription<T, R> {
        self.on_with_options(scope, EventOptions::default(), callback)
    }
    pub fn once(
        &self,
        scope: EventScope,
        callback: impl Fn(&T) -> R + Send + Sync + 'static,
    ) -> Subscription<T, R> {
        self.on_with_options(
            scope,
            EventOptions {
                once: true,
                prepend: false,
            },
            callback,
        )
    }
    pub fn prepend(
        &self,
        scope: EventScope,
        callback: impl Fn(&T) -> R + Send + Sync + 'static,
    ) -> Subscription<T, R> {
        self.on_with_options(
            scope,
            EventOptions {
                once: false,
                prepend: true,
            },
            callback,
        )
    }
    pub fn on_with_options(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: impl Fn(&T) -> R + Send + Sync + 'static,
    ) -> Subscription<T, R> {
        self.channel.register(scope, options, Arc::new(callback))
    }
    /// Register a listener with explicit admission control and draining.
    pub fn on_owned(
        &self,
        scope: EventScope,
        callback: impl Fn(&T) -> R + Send + Sync + 'static,
    ) -> OwnedSubscription<SyncCallback<T, R>> {
        self.on_owned_with_options(scope, EventOptions::default(), callback)
    }
    pub fn on_owned_with_options(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: impl Fn(&T) -> R + Send + Sync + 'static,
    ) -> OwnedSubscription<SyncCallback<T, R>> {
        self.channel
            .register_owned(scope, options, Arc::new(callback), true)
    }
    /// Register a listener whose owner cleanup closes and drains it. Use
    /// `setup` from synchronous setup or `&setup` from async setup. Register resource cleanup
    /// before this listener so LIFO restoration drains before releasing it.
    pub fn on_in(
        &self,
        owner: &impl EventOwner,
        scope: EventScope,
        callback: impl Fn(&T) -> R + Send + Sync + 'static,
    ) -> Result<OwnedSubscription<SyncCallback<T, R>>, String>
    where
        T: 'static,
        R: 'static,
    {
        self.on_in_with_options(owner, scope, EventOptions::default(), callback)
    }
    pub fn on_in_with_options(
        &self,
        owner: &impl EventOwner,
        scope: EventScope,
        options: EventOptions,
        callback: impl Fn(&T) -> R + Send + Sync + 'static,
    ) -> Result<OwnedSubscription<SyncCallback<T, R>>, String>
    where
        T: 'static,
        R: 'static,
    {
        self.channel
            .register_owned(scope, options, Arc::new(callback), false)
            .attach(&owner.event_owner())
    }
    pub fn off(&self, subscription: &Subscription<T, R>) -> bool {
        self.channel.off(subscription)
    }
    pub fn listener_count(&self) -> usize {
        self.channel.count()
    }
    pub fn emit(&self, scope: EventScope, payload: &T) {
        self.emit_filtered(|listener| scope.matches(listener), payload);
    }
    /// The predicate selects listener contexts; global listeners always run.
    pub fn emit_filtered(&self, filter: impl Fn(EventScope) -> bool, payload: &T) {
        for listener in self.channel.snapshot(filter) {
            if let Some(invocation) = self.channel.claim(&listener) {
                (invocation.callback())(payload);
            }
        }
    }
}
impl<T, R> Event<T, Option<R>> {
    pub fn bail(&self, scope: EventScope, payload: &T) -> Option<R> {
        self.bail_filtered(|listener| scope.matches(listener), payload)
    }
    pub fn bail_filtered(&self, filter: impl Fn(EventScope) -> bool, payload: &T) -> Option<R> {
        for listener in self.channel.snapshot(filter) {
            if let Some(invocation) = self.channel.claim(&listener) {
                if let Some(result) = (invocation.callback())(payload) {
                    return Some(result);
                }
            }
        }
        None
    }
}

pub type EventFuture<R, E = String> = Pin<Box<dyn Future<Output = Result<R, E>> + Send + 'static>>;
type AsyncCallback<T, R, E> = dyn Fn(Arc<T>) -> EventFuture<R, E> + Send + Sync + 'static;
pub type AsyncSubscription<T, R = (), E = String> = EventSubscription<AsyncCallback<T, R, E>>;
pub type OwnedAsyncSubscription<T, R = (), E = String> = OwnedSubscription<AsyncCallback<T, R, E>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ListenerError<E> {
    Callback(E),
    Panicked(String),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DispatchFailure<E> {
    /// Position in the eligible snapshot, not the completion order.
    pub index: usize,
    pub error: ListenerError<E>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AggregateError<E> {
    pub failures: Vec<DispatchFailure<E>>,
}
fn panic_message(panic: Box<dyn Any + Send>) -> String {
    if let Some(message) = panic.downcast_ref::<String>() {
        message.clone()
    } else if let Some(message) = panic.downcast_ref::<&str>() {
        (*message).to_owned()
    } else {
        "non-string callback panic".to_owned()
    }
}

/// Owned payloads let async listeners borrow their own `Arc<T>` across awaits.
pub struct AsyncEvent<T, R = (), E = String> {
    channel: Channel<AsyncCallback<T, R, E>>,
}
impl<T, R, E> Clone for AsyncEvent<T, R, E> {
    fn clone(&self) -> Self {
        Self {
            channel: self.channel.clone(),
        }
    }
}
impl<T: 'static, R: 'static, E: 'static> Default for AsyncEvent<T, R, E> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T: 'static, R: 'static, E: 'static> AsyncEvent<T, R, E> {
    pub fn new() -> Self {
        Self {
            channel: Channel::new(),
        }
    }
    pub fn on<F, Fut>(&self, scope: EventScope, callback: F) -> AsyncSubscription<T, R, E>
    where
        F: Fn(Arc<T>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, E>> + Send + 'static,
    {
        self.on_with_options(scope, EventOptions::default(), callback)
    }
    pub fn once<F, Fut>(&self, scope: EventScope, callback: F) -> AsyncSubscription<T, R, E>
    where
        F: Fn(Arc<T>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, E>> + Send + 'static,
    {
        self.on_with_options(
            scope,
            EventOptions {
                once: true,
                prepend: false,
            },
            callback,
        )
    }
    pub fn prepend<F, Fut>(&self, scope: EventScope, callback: F) -> AsyncSubscription<T, R, E>
    where
        F: Fn(Arc<T>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, E>> + Send + 'static,
    {
        self.on_with_options(
            scope,
            EventOptions {
                once: false,
                prepend: true,
            },
            callback,
        )
    }
    pub fn on_with_options<F, Fut>(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: F,
    ) -> AsyncSubscription<T, R, E>
    where
        F: Fn(Arc<T>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, E>> + Send + 'static,
    {
        self.channel.register(
            scope,
            options,
            Arc::new(move |payload| Box::pin(callback(payload))),
        )
    }
    /// Register an async listener with close/drain control.
    pub fn on_owned<F, Fut>(
        &self,
        scope: EventScope,
        callback: F,
    ) -> OwnedSubscription<AsyncCallback<T, R, E>>
    where
        F: Fn(Arc<T>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, E>> + Send + 'static,
    {
        self.on_owned_with_options(scope, EventOptions::default(), callback)
    }
    pub fn on_owned_with_options<F, Fut>(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: F,
    ) -> OwnedSubscription<AsyncCallback<T, R, E>>
    where
        F: Fn(Arc<T>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, E>> + Send + 'static,
    {
        self.channel.register_owned(
            scope,
            options,
            Arc::new(move |payload| Box::pin(callback(payload))),
            true,
        )
    }
    /// Install episode cleanup before accepting callbacks. The cleanup waits
    /// until all admitted dispatch futures complete or are cancelled.
    pub fn on_in<F, Fut>(
        &self,
        owner: &impl EventOwner,
        scope: EventScope,
        callback: F,
    ) -> Result<OwnedSubscription<AsyncCallback<T, R, E>>, String>
    where
        T: 'static,
        R: 'static,
        E: 'static,
        F: Fn(Arc<T>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, E>> + Send + 'static,
    {
        self.on_in_with_options(owner, scope, EventOptions::default(), callback)
    }
    pub fn on_in_with_options<F, Fut>(
        &self,
        owner: &impl EventOwner,
        scope: EventScope,
        options: EventOptions,
        callback: F,
    ) -> Result<OwnedSubscription<AsyncCallback<T, R, E>>, String>
    where
        T: 'static,
        R: 'static,
        E: 'static,
        F: Fn(Arc<T>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<R, E>> + Send + 'static,
    {
        self.channel
            .register_owned(
                scope,
                options,
                Arc::new(move |payload| Box::pin(callback(payload))),
                false,
            )
            .attach(&owner.event_owner())
    }
    pub fn off(&self, subscription: &AsyncSubscription<T, R, E>) -> bool {
        self.channel.off(subscription)
    }
    pub fn listener_count(&self) -> usize {
        self.channel.count()
    }
    /// Start every eligible listener, poll them concurrently, and await every
    /// result even when some fail. Successful output keeps registration order.
    /// Dropping the returned future cancels pending work by dropping its futures.
    pub fn parallel(&self, scope: EventScope, payload: Arc<T>) -> Parallel<R, E> {
        self.parallel_filtered(|listener| scope.matches(listener), payload)
    }
    pub fn parallel_filtered(
        &self,
        filter: impl Fn(EventScope) -> bool,
        payload: Arc<T>,
    ) -> Parallel<R, E> {
        let mut slots = Vec::new();
        for (index, listener) in self.channel.snapshot(filter).into_iter().enumerate() {
            let Some(invocation) = self.channel.claim(&listener) else {
                continue;
            };
            let slot = match catch_unwind(AssertUnwindSafe(|| {
                (invocation.callback())(payload.clone())
            })) {
                Ok(future) => Slot::Pending(Box::pin(track(future, invocation))),
                Err(panic) => Slot::Done(Some(Err(ListenerError::Panicked(panic_message(panic))))),
            };
            slots.push((index, slot));
        }
        Parallel {
            slots,
            completed: false,
        }
    }
    /// Await the same all-settled dispatch as `parallel`, discarding values.
    pub async fn emit(&self, scope: EventScope, payload: Arc<T>) -> Result<(), AggregateError<E>> {
        self.parallel(scope, payload).await.map(|_| ())
    }
}
impl<T: 'static, R: 'static, E: 'static> AsyncEvent<T, Option<R>, E> {
    /// Await in order; stop on the first `Some` or error. Later once listeners
    /// remain registered. Unlike parallel, no later callback is even constructed.
    pub fn serial(
        &self,
        scope: EventScope,
        payload: Arc<T>,
    ) -> impl Future<Output = Result<Option<R>, ListenerError<E>>> {
        self.serial_filtered(move |listener| scope.matches(listener), payload)
    }
    pub fn serial_filtered(
        &self,
        filter: impl Fn(EventScope) -> bool,
        payload: Arc<T>,
    ) -> impl Future<Output = Result<Option<R>, ListenerError<E>>> {
        let snapshot = self.channel.snapshot(filter);
        let channel = self.channel.clone();
        async move {
            for listener in snapshot {
                let Some(invocation) = channel.claim(&listener) else {
                    continue;
                };
                let future = catch_unwind(AssertUnwindSafe(|| {
                    (invocation.callback())(payload.clone())
                }))
                .map_err(|panic| ListenerError::Panicked(panic_message(panic)))?;
                let mut result = Parallel {
                    slots: vec![(0, Slot::Pending(Box::pin(track(future, invocation))))],
                    completed: false,
                }
                .await
                .map_err(|aggregate| aggregate.failures.into_iter().next().unwrap().error)?;
                if let Some(result) = result.pop().unwrap() {
                    return Ok(Some(result));
                }
            }
            Ok(None)
        }
    }
}
enum Slot<R, E> {
    Pending(EventFuture<R, E>),
    Done(Option<Result<R, ListenerError<E>>>),
}
#[must_use = "async dispatch must be polled to complete"]
pub struct Parallel<R, E> {
    slots: Vec<(usize, Slot<R, E>)>,
    completed: bool,
}
// Only boxed futures are pinned; moving results never moves a pinned future.
impl<R, E> Unpin for Parallel<R, E> {}
impl<R, E> Future for Parallel<R, E> {
    type Output = Result<Vec<R>, AggregateError<E>>;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();
        assert!(!this.completed, "completed event dispatch polled again");
        let mut pending = false;
        for (_, slot) in &mut this.slots {
            if let Slot::Pending(future) = slot {
                let result = crate::future_support::poll_catching_unwind(future.as_mut(), cx);
                match result {
                    Ok(Poll::Pending) => pending = true,
                    Ok(Poll::Ready(result)) => {
                        *slot = Slot::Done(Some(result.map_err(ListenerError::Callback)))
                    }
                    Err(panic) => {
                        *slot = Slot::Done(Some(Err(ListenerError::Panicked(panic_message(panic)))))
                    }
                }
            }
        }
        if pending {
            return Poll::Pending;
        }
        this.completed = true;
        let mut results = Vec::new();
        let mut failures = Vec::new();
        for (index, slot) in &mut this.slots {
            if let Slot::Done(result) = slot {
                match result.take().unwrap() {
                    Ok(value) => results.push(value),
                    Err(error) => failures.push(DispatchFailure {
                        index: *index,
                        error,
                    }),
                }
            }
        }
        Poll::Ready(if failures.is_empty() {
            Ok(results)
        } else {
            Err(AggregateError { failures })
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WaterfallError<E = String> {
    Callback(E),
    NextCalledTwice,
}
pub type WaterfallResult<R, E = String> = Result<R, WaterfallError<E>>;
/// Middleware continuation: invoking it more than once returns an explicit error.
pub struct Next<'a, R, E = String> {
    continuation: Option<Box<dyn FnOnce() -> WaterfallResult<R, E> + 'a>>,
}
impl<R, E> Next<'_, R, E> {
    pub fn call(&mut self) -> WaterfallResult<R, E> {
        self.continuation
            .take()
            .ok_or(WaterfallError::NextCalledTwice)?()
    }
}
type AroundCallback<T, R, E> =
    dyn Fn(&T, &mut Next<'_, R, E>) -> WaterfallResult<R, E> + Send + Sync;
type AroundListener<T, R, E> = Arc<Listener<AroundCallback<T, R, E>>>;
pub type WaterfallSubscription<T, R, E = String> = EventSubscription<AroundCallback<T, R, E>>;
pub type OwnedWaterfallSubscription<T, R, E = String> = OwnedSubscription<AroundCallback<T, R, E>>;
/// Around middleware may run before and after `next`, transform its result, or
/// short-circuit by returning without calling `next`. Panics propagate.
pub struct Waterfall<T, R, E = String> {
    channel: Channel<AroundCallback<T, R, E>>,
}
impl<T, R, E> Clone for Waterfall<T, R, E> {
    fn clone(&self) -> Self {
        Self {
            channel: self.channel.clone(),
        }
    }
}
impl<T, R, E> Default for Waterfall<T, R, E> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T, R, E> Waterfall<T, R, E> {
    pub fn new() -> Self {
        Self {
            channel: Channel::new(),
        }
    }
    pub fn on(
        &self,
        scope: EventScope,
        callback: impl Fn(&T, &mut Next<'_, R, E>) -> WaterfallResult<R, E> + Send + Sync + 'static,
    ) -> WaterfallSubscription<T, R, E> {
        self.on_with_options(scope, EventOptions::default(), callback)
    }
    pub fn on_with_options(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: impl Fn(&T, &mut Next<'_, R, E>) -> WaterfallResult<R, E> + Send + Sync + 'static,
    ) -> WaterfallSubscription<T, R, E> {
        self.channel.register(scope, options, Arc::new(callback))
    }
    pub fn on_owned(
        &self,
        scope: EventScope,
        callback: impl Fn(&T, &mut Next<'_, R, E>) -> WaterfallResult<R, E> + Send + Sync + 'static,
    ) -> OwnedSubscription<AroundCallback<T, R, E>> {
        self.on_owned_with_options(scope, EventOptions::default(), callback)
    }
    pub fn on_owned_with_options(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: impl Fn(&T, &mut Next<'_, R, E>) -> WaterfallResult<R, E> + Send + Sync + 'static,
    ) -> OwnedSubscription<AroundCallback<T, R, E>> {
        self.channel
            .register_owned(scope, options, Arc::new(callback), true)
    }
    pub fn on_in(
        &self,
        owner: &impl EventOwner,
        scope: EventScope,
        callback: impl Fn(&T, &mut Next<'_, R, E>) -> WaterfallResult<R, E> + Send + Sync + 'static,
    ) -> Result<OwnedSubscription<AroundCallback<T, R, E>>, String>
    where
        T: 'static,
        R: 'static,
        E: 'static,
    {
        self.on_in_with_options(owner, scope, EventOptions::default(), callback)
    }
    pub fn on_in_with_options(
        &self,
        owner: &impl EventOwner,
        scope: EventScope,
        options: EventOptions,
        callback: impl Fn(&T, &mut Next<'_, R, E>) -> WaterfallResult<R, E> + Send + Sync + 'static,
    ) -> Result<OwnedSubscription<AroundCallback<T, R, E>>, String>
    where
        T: 'static,
        R: 'static,
        E: 'static,
    {
        self.channel
            .register_owned(scope, options, Arc::new(callback), false)
            .attach(&owner.event_owner())
    }
    pub fn off(&self, subscription: &WaterfallSubscription<T, R, E>) -> bool {
        self.channel.off(subscription)
    }
    pub fn listener_count(&self) -> usize {
        self.channel.count()
    }
    pub fn run(
        &self,
        scope: EventScope,
        payload: &T,
        inner: impl FnOnce() -> WaterfallResult<R, E>,
    ) -> WaterfallResult<R, E> {
        self.run_filtered(|listener| scope.matches(listener), payload, inner)
    }
    pub fn run_filtered(
        &self,
        filter: impl Fn(EventScope) -> bool,
        payload: &T,
        inner: impl FnOnce() -> WaterfallResult<R, E>,
    ) -> WaterfallResult<R, E> {
        let snapshot = self.channel.snapshot(filter);
        self.dispatch(&snapshot, payload, Box::new(inner))
    }
    fn dispatch<'a>(
        &'a self,
        listeners: &'a [AroundListener<T, R, E>],
        payload: &'a T,
        inner: Box<dyn FnOnce() -> WaterfallResult<R, E> + 'a>,
    ) -> WaterfallResult<R, E> {
        let Some((listener, rest)) = listeners.split_first() else {
            return inner();
        };
        let Some(invocation) = self.channel.claim(listener) else {
            return self.dispatch(rest, payload, inner);
        };
        let mut next = Next {
            continuation: Some(Box::new(move || self.dispatch(rest, payload, inner))),
        };
        (invocation.callback())(payload, &mut next)
    }
}

pub type WaterfallFuture<R, E = String> = EventFuture<R, WaterfallError<E>>;
type AsyncContinuation<R, E> = Box<dyn FnOnce() -> WaterfallFuture<R, E> + Send>;
/// Cloneable async continuation with a shared, atomic at-most-once claim.
pub struct AsyncNext<R, E = String> {
    continuation: Arc<Mutex<Option<AsyncContinuation<R, E>>>>,
}
impl<R, E> Clone for AsyncNext<R, E> {
    fn clone(&self) -> Self {
        Self {
            continuation: self.continuation.clone(),
        }
    }
}
impl<R: Send + 'static, E: Send + 'static> AsyncNext<R, E> {
    pub fn call(&self) -> WaterfallFuture<R, E> {
        let continuation = self
            .continuation
            .lock()
            .expect("waterfall continuation lock poisoned")
            .take();
        match continuation {
            Some(next) => next(),
            None => Box::pin(async { Err(WaterfallError::NextCalledTwice) }),
        }
    }
}
type AsyncAroundCallback<T, R, E> =
    dyn Fn(Arc<T>, AsyncNext<R, E>) -> WaterfallFuture<R, E> + Send + Sync;
pub type AsyncWaterfallSubscription<T, R, E = String> =
    EventSubscription<AsyncAroundCallback<T, R, E>>;
pub type OwnedAsyncWaterfallSubscription<T, R, E = String> =
    OwnedSubscription<AsyncAroundCallback<T, R, E>>;
pub struct AsyncWaterfall<T, R, E = String> {
    channel: Channel<AsyncAroundCallback<T, R, E>>,
}
impl<T, R, E> Clone for AsyncWaterfall<T, R, E> {
    fn clone(&self) -> Self {
        Self {
            channel: self.channel.clone(),
        }
    }
}
impl<T: Send + Sync + 'static, R: Send + 'static, E: Send + 'static> Default
    for AsyncWaterfall<T, R, E>
{
    fn default() -> Self {
        Self::new()
    }
}
impl<T: Send + Sync + 'static, R: Send + 'static, E: Send + 'static> AsyncWaterfall<T, R, E> {
    pub fn new() -> Self {
        Self {
            channel: Channel::new(),
        }
    }
    pub fn on<F, Fut>(&self, scope: EventScope, callback: F) -> AsyncWaterfallSubscription<T, R, E>
    where
        F: Fn(Arc<T>, AsyncNext<R, E>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = WaterfallResult<R, E>> + Send + 'static,
    {
        self.on_with_options(scope, EventOptions::default(), callback)
    }
    pub fn on_with_options<F, Fut>(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: F,
    ) -> AsyncWaterfallSubscription<T, R, E>
    where
        F: Fn(Arc<T>, AsyncNext<R, E>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = WaterfallResult<R, E>> + Send + 'static,
    {
        self.channel.register(
            scope,
            options,
            Arc::new(move |payload, next| Box::pin(callback(payload, next))),
        )
    }
    pub fn on_owned<F, Fut>(
        &self,
        scope: EventScope,
        callback: F,
    ) -> OwnedSubscription<AsyncAroundCallback<T, R, E>>
    where
        F: Fn(Arc<T>, AsyncNext<R, E>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = WaterfallResult<R, E>> + Send + 'static,
    {
        self.on_owned_with_options(scope, EventOptions::default(), callback)
    }
    pub fn on_owned_with_options<F, Fut>(
        &self,
        scope: EventScope,
        options: EventOptions,
        callback: F,
    ) -> OwnedSubscription<AsyncAroundCallback<T, R, E>>
    where
        F: Fn(Arc<T>, AsyncNext<R, E>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = WaterfallResult<R, E>> + Send + 'static,
    {
        self.channel.register_owned(
            scope,
            options,
            Arc::new(move |payload, next| Box::pin(callback(payload, next))),
            true,
        )
    }
    pub fn on_in<F, Fut>(
        &self,
        owner: &impl EventOwner,
        scope: EventScope,
        callback: F,
    ) -> Result<OwnedSubscription<AsyncAroundCallback<T, R, E>>, String>
    where
        F: Fn(Arc<T>, AsyncNext<R, E>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = WaterfallResult<R, E>> + Send + 'static,
    {
        self.on_in_with_options(owner, scope, EventOptions::default(), callback)
    }
    pub fn on_in_with_options<F, Fut>(
        &self,
        owner: &impl EventOwner,
        scope: EventScope,
        options: EventOptions,
        callback: F,
    ) -> Result<OwnedSubscription<AsyncAroundCallback<T, R, E>>, String>
    where
        F: Fn(Arc<T>, AsyncNext<R, E>) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = WaterfallResult<R, E>> + Send + 'static,
    {
        self.channel
            .register_owned(
                scope,
                options,
                Arc::new(move |payload, next| Box::pin(callback(payload, next))),
                false,
            )
            .attach(&owner.event_owner())
    }
    pub fn off(&self, subscription: &AsyncWaterfallSubscription<T, R, E>) -> bool {
        self.channel.off(subscription)
    }
    pub fn listener_count(&self) -> usize {
        self.channel.count()
    }
    /// Middleware panics propagate, like synchronous waterfall; explicit errors
    /// pass through unchanged. Dropping a continuation short-circuits the chain.
    pub fn run<Fut>(
        &self,
        scope: EventScope,
        payload: Arc<T>,
        inner: impl FnOnce() -> Fut + Send + 'static,
    ) -> WaterfallFuture<R, E>
    where
        Fut: Future<Output = WaterfallResult<R, E>> + Send + 'static,
    {
        self.run_filtered(|listener| scope.matches(listener), payload, inner)
    }
    pub fn run_filtered<Fut>(
        &self,
        filter: impl Fn(EventScope) -> bool,
        payload: Arc<T>,
        inner: impl FnOnce() -> Fut + Send + 'static,
    ) -> WaterfallFuture<R, E>
    where
        Fut: Future<Output = WaterfallResult<R, E>> + Send + 'static,
    {
        Self::dispatch(
            self.channel.clone(),
            self.channel.snapshot(filter).into_iter(),
            payload,
            Box::new(move || Box::pin(inner())),
        )
    }
    fn dispatch(
        channel: Channel<AsyncAroundCallback<T, R, E>>,
        mut listeners: std::vec::IntoIter<Arc<Listener<AsyncAroundCallback<T, R, E>>>>,
        payload: Arc<T>,
        inner: Box<dyn FnOnce() -> WaterfallFuture<R, E> + Send>,
    ) -> WaterfallFuture<R, E> {
        Box::pin(async move {
            for listener in listeners.by_ref() {
                let Some(invocation) = channel.claim(&listener) else {
                    continue;
                };
                let remaining_payload = payload.clone();
                // A continuation retains the episode permit, not the callback
                // environment: the callback may itself capture the slot where
                // application code stores `next`.
                let continuation_lease = invocation.0._invocation.clone();
                let next = AsyncNext {
                    continuation: Arc::new(Mutex::new(Some(Box::new(move || {
                        Box::pin(track(
                            Self::dispatch(channel, listeners, remaining_payload, inner),
                            continuation_lease,
                        ))
                    })))),
                };
                return track((invocation.callback())(payload, next), invocation).await;
            }
            inner().await
        })
    }
}

impl<E: std::fmt::Display> std::fmt::Display for ListenerError<E> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Callback(error) => write!(formatter, "event callback failed: {error}"),
            Self::Panicked(message) => write!(formatter, "event callback panicked: {message}"),
        }
    }
}
impl<E: std::error::Error + 'static> std::error::Error for ListenerError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Callback(error) => Some(error),
            Self::Panicked(_) => None,
        }
    }
}
impl<E: std::fmt::Display> std::fmt::Display for AggregateError<E> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "{} event listener(s) failed",
            self.failures.len()
        )?;
        for failure in &self.failures {
            write!(formatter, "; listener {}: {}", failure.index, failure.error)?;
        }
        Ok(())
    }
}
impl<E: std::error::Error + 'static> std::error::Error for AggregateError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.failures.first().map(|failure| &failure.error as _)
    }
}
impl<E: std::fmt::Display> std::fmt::Display for WaterfallError<E> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Callback(error) => write!(formatter, "waterfall callback failed: {error}"),
            Self::NextCalledTwice => formatter.write_str("waterfall continuation already called"),
        }
    }
}
impl<E: std::error::Error + 'static> std::error::Error for WaterfallError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Callback(error) => Some(error),
            Self::NextCalledTwice => None,
        }
    }
}
