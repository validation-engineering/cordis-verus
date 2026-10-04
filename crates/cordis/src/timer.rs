//! Cancellable, owner-bound timers in the ordinary Rust host adapter.
//!
//! Each real-time service uses one worker, so callbacks never overlap. Intervals
//! use fixed delay and skip missed ticks. `cancel` prevents new callback starts;
//! `cancel_and_join` additionally waits for an in-flight callback. Cancellation
//! from inside any callback of the same service never waits for other callbacks:
//! this prevents mutual shutdown deadlocks. An external join provides the barrier.
//! Owner cleanup shuts down and joins the worker before dependency providers may
//! be cleaned. Callbacks remain ordinary Rust and are outside the Verus proof.

use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::future::Future;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex, Weak};
use std::task::{Context, Poll, Waker};
use std::thread::{self, JoinHandle, ThreadId};
use std::time::{Duration, Instant};

thread_local! {
    static CALLBACK_SERVICES: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}
struct CallbackScope(usize);
impl CallbackScope {
    fn enter(service: usize) -> Self {
        CALLBACK_SERVICES.with(|services| services.borrow_mut().push(service));
        Self(service)
    }
    fn contains(service: usize) -> bool {
        CALLBACK_SERVICES.with(|services| services.borrow().contains(&service))
    }
}
impl Drop for CallbackScope {
    fn drop(&mut self) {
        CALLBACK_SERVICES.with(|services| {
            let removed = services.borrow_mut().pop();
            debug_assert_eq!(removed, Some(self.0));
        });
    }
}

type Callback = Box<dyn FnMut() + Send + 'static>;
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TimerError {
    Cancelled,
    ZeroInterval,
    ReentrantCallback,
    Panicked(String),
}
impl std::fmt::Display for TimerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cancelled => f.write_str(crate::CANCELLED),
            Self::ZeroInterval => f.write_str("interval period must be positive"),
            Self::ReentrantCallback => f.write_str("recursive throttle callback invocation"),
            Self::Panicked(message) => write!(f, "timer callback panicked: {message}"),
        }
    }
}
impl std::error::Error for TimerError {}

enum Clock {
    Real(Instant),
    Manual(Mutex<Duration>),
}
struct JobState {
    deadline: Duration,
    period: Option<Duration>,
    callback: Option<Callback>,
    running: Option<ThreadId>,
    cancelled: bool,
    finished: bool,
    error: Option<TimerError>,
}
struct Job {
    id: u64,
    state: Mutex<JobState>,
    settled: Condvar,
}
impl Job {
    fn cancel(&self) -> bool {
        let (changed, callback) = {
            let mut state = self.state.lock().expect("timer job lock poisoned");
            let changed = !state.cancelled && !state.finished;
            state.cancelled = true;
            (changed, state.callback.take())
        };
        // A captured resource may re-enter the service while it is dropped.
        drop(callback);
        self.settled.notify_all();
        changed
    }
    fn join(&self) -> Result<(), TimerError> {
        let mut state = self.state.lock().expect("timer job lock poisoned");
        while state
            .running
            .is_some_and(|runner| runner != thread::current().id())
        {
            state = self.settled.wait(state).expect("timer job lock poisoned");
        }
        state.error.clone().map_or(Ok(()), Err)
    }
}
struct Schedule {
    next_id: u64,
    stopped: bool,
    jobs: BTreeMap<u64, Arc<Job>>,
    errors: Vec<TimerError>,
    finalizers: Vec<Arc<dyn Fn() + Send + Sync>>,
}
struct Scheduler {
    clock: Clock,
    schedule: Mutex<Schedule>,
    changed: Condvar,
    driving: AtomicBool,
    scopes: Mutex<Vec<crate::AsyncSetup>>,
}
impl Scheduler {
    fn identity(&self) -> usize {
        self as *const Self as usize
    }
    fn inside_callback(&self) -> bool {
        CallbackScope::contains(self.identity())
    }
    fn owner_cancelled(&self) -> bool {
        let scopes = self
            .scopes
            .lock()
            .expect("timer owner lock poisoned")
            .clone();
        scopes.iter().any(crate::AsyncSetup::is_cancelled)
    }
    fn now(&self) -> Duration {
        match &self.clock {
            Clock::Real(start) => start.elapsed(),
            Clock::Manual(now) => *now.lock().expect("manual clock lock poisoned"),
        }
    }
    fn remove(&self, id: u64) {
        let removed = self
            .schedule
            .lock()
            .expect("timer schedule lock poisoned")
            .jobs
            .remove(&id);
        drop(removed);
        self.changed.notify_all();
    }
    fn run_due(&self) -> usize {
        // A reentrant manual advance changes time, but never nests callbacks.
        if self.driving.swap(true, Ordering::AcqRel) {
            return 0;
        }
        struct Driving<'a>(&'a AtomicBool);
        impl Drop for Driving<'_> {
            fn drop(&mut self) {
                self.0.store(false, Ordering::Release);
            }
        }
        let _driving = Driving(&self.driving);
        let now = self.now();
        let mut jobs: Vec<_> = self
            .schedule
            .lock()
            .expect("timer schedule lock poisoned")
            .jobs
            .values()
            .filter_map(|job| {
                let state = job.state.lock().expect("timer job lock poisoned");
                (!state.cancelled && !state.finished && state.deadline <= now)
                    .then(|| (state.deadline, job.id, job.clone()))
            })
            .collect();
        jobs.sort_by_key(|(deadline, id, _)| (*deadline, *id));
        let mut called = 0;
        for (_, _, job) in jobs {
            let callback = {
                let mut state = job.state.lock().expect("timer job lock poisoned");
                if state.cancelled || state.finished || state.running.is_some() {
                    continue;
                }
                state.running = Some(thread::current().id());
                state.callback.take()
            };
            let Some(mut callback) = callback else {
                continue;
            };
            called += 1;
            let _callback_scope = CallbackScope::enter(self.identity());
            let result = catch_unwind(AssertUnwindSafe(&mut callback));
            let error = result.err().map(|panic| {
                let message = panic
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| {
                        panic
                            .downcast_ref::<&str>()
                            .map(|message| (*message).to_owned())
                    })
                    .unwrap_or_else(|| "non-string panic".to_owned());
                TimerError::Panicked(message)
            });
            let finished = {
                let mut state = job.state.lock().expect("timer job lock poisoned");
                state.error = error.clone();
                if !state.cancelled && error.is_none() && state.period.is_some() {
                    state.deadline = self.now().saturating_add(state.period.unwrap());
                    state.callback = Some(callback);
                    state.running = None;
                    false
                } else {
                    state.finished = true;
                    // Callback destruction must also happen outside the job lock.
                    drop(state);
                    drop(callback);
                    job.state.lock().expect("timer job lock poisoned").running = None;
                    true
                }
            };
            if let Some(error) = error {
                self.schedule
                    .lock()
                    .expect("timer schedule lock poisoned")
                    .errors
                    .push(error);
            }
            job.settled.notify_all();
            if finished {
                self.remove(job.id);
            }
        }
        called
    }
    fn stop(&self) {
        let (jobs, finalizers) = {
            let mut schedule = self.schedule.lock().expect("timer schedule lock poisoned");
            schedule.stopped = true;
            (schedule.jobs.clone(), schedule.finalizers.clone())
        };
        self.changed.notify_all();
        for job in jobs.values() {
            job.cancel();
        }
        for finalizer in finalizers {
            finalizer();
        }
        if !self.inside_callback() {
            for job in jobs.values() {
                let _ = job.join();
            }
        }
        let removed = {
            let mut schedule = self.schedule.lock().expect("timer schedule lock poisoned");
            let ids: Vec<_> = schedule
                .jobs
                .iter()
                .filter_map(|(id, job)| {
                    job.state
                        .lock()
                        .expect("timer job lock poisoned")
                        .running
                        .is_none()
                        .then_some(*id)
                })
                .collect();
            ids.into_iter()
                .filter_map(|id| schedule.jobs.remove(&id))
                .collect::<Vec<_>>()
        };
        drop(removed);
    }
    fn worker(self: Arc<Self>) {
        loop {
            self.run_due();
            let schedule = self.schedule.lock().expect("timer schedule lock poisoned");
            if schedule.stopped {
                break;
            }
            let deadline = schedule
                .jobs
                .values()
                .filter_map(|job| {
                    let state = job.state.lock().expect("timer job lock poisoned");
                    (!state.cancelled && !state.finished).then_some(state.deadline)
                })
                .min();
            if let Some(deadline) = deadline {
                let wait = deadline.saturating_sub(self.now());
                drop(
                    self.changed
                        .wait_timeout(schedule, wait)
                        .expect("timer schedule lock poisoned"),
                );
            } else {
                drop(
                    self.changed
                        .wait(schedule)
                        .expect("timer schedule lock poisoned"),
                );
            }
        }
    }
}
struct Owner {
    scheduler: Arc<Scheduler>,
    worker: Mutex<Option<JoinHandle<()>>>,
}
impl Owner {
    fn stop(&self) {
        self.scheduler.stop();
        if self.scheduler.inside_callback() {
            return;
        }
        let worker = {
            let mut worker = self.worker.lock().expect("timer worker lock poisoned");
            if worker
                .as_ref()
                .is_some_and(|worker| worker.thread().id() == thread::current().id())
            {
                None
            } else {
                worker.take()
            }
        };
        if let Some(worker) = worker {
            let _ = worker.join();
        }
    }
}
impl Drop for Owner {
    fn drop(&mut self) {
        self.stop();
    }
}

/// Clones share one scheduler and its lifetime. Dropping the last service stops
/// it. Handles are explicit cancellation tokens and do not keep the service alive.
#[derive(Clone)]
pub struct TimerService {
    owner: Arc<Owner>,
}
impl Default for TimerService {
    fn default() -> Self {
        Self::new()
    }
}
impl TimerService {
    pub fn new() -> Self {
        Self::build(Clock::Real(Instant::now()))
    }
    fn build(clock: Clock) -> Self {
        let real = matches!(clock, Clock::Real(_));
        let scheduler = Arc::new(Scheduler {
            clock,
            schedule: Mutex::new(Schedule {
                next_id: 0,
                stopped: false,
                jobs: BTreeMap::new(),
                errors: Vec::new(),
                finalizers: Vec::new(),
            }),
            changed: Condvar::new(),
            driving: AtomicBool::new(false),
            scopes: Mutex::new(Vec::new()),
        });
        let worker = if real {
            let scheduler = scheduler.clone();
            Some(
                thread::Builder::new()
                    .name("cordis-timer".to_owned())
                    .spawn(move || scheduler.worker())
                    .expect("cannot start timer worker"),
            )
        } else {
            None
        };
        Self {
            owner: Arc::new(Owner {
                scheduler,
                worker: Mutex::new(worker),
            }),
        }
    }
    /// No sleeping or background thread. Advancing the clock executes due jobs
    /// in deadline/registration order and at most one tick per interval.
    pub fn manual() -> (Self, ManualClock) {
        let service = Self::build(Clock::Manual(Mutex::new(Duration::ZERO)));
        let clock = ManualClock {
            scheduler: Arc::downgrade(&service.owner.scheduler),
        };
        (service, clock)
    }
    pub fn now(&self) -> Duration {
        self.owner.scheduler.now()
    }
    pub fn is_shutdown(&self) -> bool {
        self.owner
            .scheduler
            .schedule
            .lock()
            .expect("timer schedule lock poisoned")
            .stopped
    }
    pub fn pending_count(&self) -> usize {
        self.owner
            .scheduler
            .schedule
            .lock()
            .expect("timer schedule lock poisoned")
            .jobs
            .len()
    }
    /// Idempotently cancel and join all callbacks. Errors include all callback
    /// panics observed by the service, retained for subsequent shutdown calls.
    pub fn shutdown(&self) -> Result<(), Vec<TimerError>> {
        self.owner.stop();
        let errors = self
            .owner
            .scheduler
            .schedule
            .lock()
            .expect("timer schedule lock poisoned")
            .errors
            .clone();
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
    fn schedule(
        &self,
        delay: Duration,
        period: Option<Duration>,
        callback: Callback,
    ) -> Result<TimerHandle, TimerError> {
        let scheduler = &self.owner.scheduler;
        let mut schedule = scheduler
            .schedule
            .lock()
            .expect("timer schedule lock poisoned");
        if schedule.stopped {
            return Err(TimerError::Cancelled);
        }
        let id = schedule.next_id;
        schedule.next_id = id.checked_add(1).expect("timer identities exhausted");
        let job = Arc::new(Job {
            id,
            state: Mutex::new(JobState {
                deadline: scheduler.now().saturating_add(delay),
                period,
                callback: Some(callback),
                running: None,
                cancelled: false,
                finished: false,
                error: None,
            }),
            settled: Condvar::new(),
        });
        schedule.jobs.insert(id, job.clone());
        drop(schedule);
        scheduler.changed.notify_all();
        Ok(TimerHandle {
            scheduler: Arc::downgrade(scheduler),
            job,
        })
    }
    pub fn timeout(
        &self,
        delay: Duration,
        callback: impl FnOnce() + Send + 'static,
    ) -> Result<TimerHandle, TimerError> {
        let mut callback = Some(callback);
        self.schedule(delay, None, Box::new(move || callback.take().unwrap()()))
    }
    pub fn interval(
        &self,
        period: Duration,
        callback: impl FnMut() + Send + 'static,
    ) -> Result<TimerHandle, TimerError> {
        if period.is_zero() {
            return Err(TimerError::ZeroInterval);
        }
        self.schedule(period, Some(period), Box::new(callback))
    }
    pub fn set_timeout(
        &self,
        callback: impl FnOnce() + Send + 'static,
        delay: Duration,
    ) -> Result<TimerHandle, TimerError> {
        self.timeout(delay, callback)
    }
    pub fn set_interval(
        &self,
        callback: impl FnMut() + Send + 'static,
        period: Duration,
    ) -> Result<TimerHandle, TimerError> {
        self.interval(period, callback)
    }
    pub fn sleep(&self, delay: Duration) -> Sleep {
        let state = Arc::new(WaitState::new());
        let completion = Completion(state.clone());
        let handle = self.timeout(delay, move || completion.finish(Ok(()))).ok();
        Sleep { state, handle }
    }
    pub fn ticks(&self, period: Duration) -> Result<Interval, TimerError> {
        let state = Arc::new(TicksState {
            waiting: Mutex::new((false, VecDeque::new())),
        });
        let completion = TicksCompletion(state.clone());
        let handle = self.interval(period, move || completion.tick())?;
        Ok(Interval { state, handle })
    }
    fn finalize(&self, finalizer: impl Fn() + Send + Sync + 'static) {
        let mut schedule = self
            .owner
            .scheduler
            .schedule
            .lock()
            .expect("timer schedule lock poisoned");
        if schedule.stopped {
            drop(schedule);
            finalizer();
        } else {
            schedule.finalizers.push(Arc::new(finalizer));
        }
    }
    pub fn debounce<T: Send + 'static>(
        &self,
        delay: Duration,
        callback: impl FnMut(T) + Send + 'static,
    ) -> Debounced<T> {
        let callback = Arc::new(CallbackGate::new(self.owner.scheduler.identity(), callback));
        let weak = Arc::downgrade(&callback);
        self.finalize(move || {
            if let Some(callback) = weak.upgrade() {
                callback.close();
            }
        });
        Debounced {
            inner: Arc::new(DebounceState {
                service: self.clone(),
                delay,
                callback,
                pending: Mutex::new(DebouncePending {
                    disposed: false,
                    generation: 0,
                    timer: None,
                }),
            }),
        }
    }
    pub fn throttle<T: Send + 'static>(
        &self,
        delay: Duration,
        no_trailing: bool,
        callback: impl FnMut(T) + Send + 'static,
    ) -> Throttled<T> {
        let callback = Arc::new(CallbackGate::new(self.owner.scheduler.identity(), callback));
        let weak = Arc::downgrade(&callback);
        self.finalize(move || {
            if let Some(callback) = weak.upgrade() {
                callback.close();
            }
        });
        Throttled {
            inner: Arc::new(ThrottleState {
                service: self.clone(),
                delay,
                no_trailing,
                callback,
                pending: Mutex::new(ThrottlePending {
                    disposed: false,
                    last: None,
                    generation: 0,
                    timer: None,
                }),
            }),
        }
    }
    /// Attach this service's whole lifetime, including future registrations, to
    /// an owner. Timers stop and join at this position in the owner's LIFO cleanup.
    pub fn bind(&self, setup: &mut crate::Setup<'_>) {
        self.bind_async(&setup.to_async())
            .expect("live synchronous setup");
    }
    pub fn bind_async(&self, setup: &crate::AsyncSetup) -> Result<(), String> {
        setup.ensure_active()?;
        let service = self.clone();
        if let Err(error) = setup.on_cleanup(move || {
            service.shutdown().map_err(|errors| {
                errors
                    .into_iter()
                    .map(|error| error.to_string())
                    .collect::<Vec<_>>()
                    .join("; ")
            })
        }) {
            let _ = self.shutdown();
            return Err(error);
        }
        self.owner
            .scheduler
            .scopes
            .lock()
            .expect("timer owner lock poisoned")
            .push(setup.clone());
        Ok(())
    }
    pub fn owned_async(setup: &crate::AsyncSetup) -> Result<Self, String> {
        setup.ensure_active()?;
        let service = Self::new();
        service.bind_async(setup)?;
        Ok(service)
    }
    pub fn owned(setup: &mut crate::Setup<'_>) -> Self {
        let service = Self::new();
        service.bind(setup);
        service
    }
}

#[derive(Clone)]
pub struct ManualClock {
    scheduler: Weak<Scheduler>,
}
impl ManualClock {
    /// Due callbacks run synchronously; an advance from within a callback only
    /// changes the clock. Jobs created by a callback wait until the next advance.
    pub fn advance(&self, duration: Duration) -> usize {
        let Some(scheduler) = self.scheduler.upgrade() else {
            return 0;
        };
        if let Clock::Manual(now) = &scheduler.clock {
            let mut now = now.lock().expect("manual clock lock poisoned");
            *now = now.saturating_add(duration);
        }
        scheduler.run_due()
    }
}

#[derive(Clone)]
pub struct TimerHandle {
    scheduler: Weak<Scheduler>,
    job: Arc<Job>,
}
impl TimerHandle {
    pub fn cancel(&self) -> bool {
        let changed = self.job.cancel();
        if self
            .job
            .state
            .lock()
            .expect("timer job lock poisoned")
            .running
            .is_none()
        {
            if let Some(scheduler) = self.scheduler.upgrade() {
                scheduler.remove(self.job.id);
            }
        }
        changed
    }
    pub fn cancel_and_join(&self) -> Result<bool, TimerError> {
        let changed = self.cancel();
        if self
            .scheduler
            .upgrade()
            .is_some_and(|scheduler| scheduler.inside_callback())
        {
            return Ok(changed);
        }
        self.job.join().map(|()| changed)
    }
    pub fn is_finished(&self) -> bool {
        let state = self.job.state.lock().expect("timer job lock poisoned");
        (state.finished || state.cancelled) && state.running.is_none()
    }
}

type WaitValue = (Option<Result<(), TimerError>>, Option<Waker>);
struct WaitState {
    value: Mutex<WaitValue>,
}
impl WaitState {
    fn new() -> Self {
        Self {
            value: Mutex::new((None, None)),
        }
    }
    fn complete(&self, result: Result<(), TimerError>) -> bool {
        let waker = {
            let mut value = self.value.lock().expect("timer future lock poisoned");
            if value.0.is_some() {
                return false;
            }
            value.0 = Some(result);
            value.1.take()
        };
        if let Some(waker) = waker {
            waker.wake();
        }
        true
    }
    fn poll(&self, cx: &mut Context<'_>) -> Poll<Result<(), TimerError>> {
        let mut value = self.value.lock().expect("timer future lock poisoned");
        if let Some(result) = &value.0 {
            Poll::Ready(result.clone())
        } else {
            value.1 = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}
struct Completion(Arc<WaitState>);
impl Completion {
    fn finish(self, result: Result<(), TimerError>) {
        self.0.complete(result);
    }
}
impl Drop for Completion {
    fn drop(&mut self) {
        self.0.complete(Err(TimerError::Cancelled));
    }
}
#[must_use = "sleep must be polled or awaited"]
pub struct Sleep {
    state: Arc<WaitState>,
    handle: Option<TimerHandle>,
}
impl Sleep {
    pub fn cancel(&self) -> bool {
        self.handle.as_ref().is_some_and(TimerHandle::cancel)
    }
    pub fn handle(&self) -> Option<TimerHandle> {
        self.handle.clone()
    }
}
impl Future for Sleep {
    type Output = Result<(), TimerError>;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self
            .handle
            .as_ref()
            .and_then(|handle| handle.scheduler.upgrade())
            .is_some_and(|scheduler| scheduler.owner_cancelled())
        {
            self.cancel();
        }
        self.state.poll(cx)
    }
}
impl Drop for Sleep {
    fn drop(&mut self) {
        self.cancel();
    }
}

struct TicksState {
    waiting: Mutex<(bool, VecDeque<Arc<WaitState>>)>,
}
impl TicksState {
    fn close(&self) {
        let waiting = {
            let mut state = self.waiting.lock().expect("interval queue lock poisoned");
            state.0 = true;
            std::mem::take(&mut state.1)
        };
        for waiter in waiting {
            waiter.complete(Err(TimerError::Cancelled));
        }
    }
}
struct TicksCompletion(Arc<TicksState>);
impl TicksCompletion {
    fn tick(&self) {
        loop {
            let next = self
                .0
                .waiting
                .lock()
                .expect("interval queue lock poisoned")
                .1
                .pop_front();
            let Some(next) = next else {
                break;
            };
            if next.complete(Ok(())) {
                break;
            }
        }
    }
}
impl Drop for TicksCompletion {
    fn drop(&mut self) {
        self.0.close();
    }
}
/// Async-iterator equivalent: each `next()` future waits for one tick. Ticks are
/// dropped when nobody is waiting; cancellation rejects all pending/future nexts.
pub struct Interval {
    state: Arc<TicksState>,
    handle: TimerHandle,
}
impl Interval {
    pub fn next(&self) -> Tick {
        let state = Arc::new(WaitState::new());
        let mut queue = self
            .state
            .waiting
            .lock()
            .expect("interval queue lock poisoned");
        if queue.0 {
            state.complete(Err(TimerError::Cancelled));
        } else {
            queue.1.push_back(state.clone());
        }
        Tick {
            state,
            scheduler: self.handle.scheduler.clone(),
        }
    }
    pub fn close(&self) -> Result<bool, TimerError> {
        self.state.close();
        self.handle.cancel_and_join()
    }
}
impl Drop for Interval {
    fn drop(&mut self) {
        let _ = self.close();
    }
}
#[must_use = "interval tick must be polled or awaited"]
pub struct Tick {
    state: Arc<WaitState>,
    scheduler: Weak<Scheduler>,
}
impl Future for Tick {
    type Output = Result<(), TimerError>;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self
            .scheduler
            .upgrade()
            .is_some_and(|scheduler| scheduler.owner_cancelled())
        {
            self.state.complete(Err(TimerError::Cancelled));
        }
        self.state.poll(cx)
    }
}
impl Drop for Tick {
    fn drop(&mut self) {
        self.state.complete(Err(TimerError::Cancelled));
    }
}

// Also guards synchronous throttle leading calls, which must finish before
// service shutdown returns. Closing from inside the callback never self-joins.
struct GateState<T> {
    callback: Option<Box<dyn FnMut(T) + Send>>,
    runner: Option<ThreadId>,
    closed: bool,
}
struct CallbackGate<T> {
    service: usize,
    state: Mutex<GateState<T>>,
    settled: Condvar,
}
impl<T> CallbackGate<T> {
    fn new(service: usize, callback: impl FnMut(T) + Send + 'static) -> Self {
        Self {
            service,
            state: Mutex::new(GateState {
                callback: Some(Box::new(callback)),
                runner: None,
                closed: false,
            }),
            settled: Condvar::new(),
        }
    }
    fn run(&self, payload: T) -> Result<(), TimerError> {
        let mut state = self.state.lock().expect("timer callback gate poisoned");
        loop {
            if state.closed {
                return Err(TimerError::Cancelled);
            }
            match state.runner {
                Some(runner) if runner == thread::current().id() => {
                    return Err(TimerError::ReentrantCallback)
                }
                Some(_) => {
                    state = self
                        .settled
                        .wait(state)
                        .expect("timer callback gate poisoned")
                }
                None => break,
            }
        }
        state.runner = Some(thread::current().id());
        let mut callback = state.callback.take().unwrap();
        drop(state);
        let _callback_scope = CallbackScope::enter(self.service);
        let result = catch_unwind(AssertUnwindSafe(|| callback(payload)));
        let mut state = self.state.lock().expect("timer callback gate poisoned");
        if state.closed {
            drop(state);
            drop(callback);
            state = self.state.lock().expect("timer callback gate poisoned");
        } else {
            state.callback = Some(callback);
        }
        state.runner = None;
        drop(state);
        self.settled.notify_all();
        if let Err(panic) = result {
            std::panic::resume_unwind(panic);
        }
        Ok(())
    }
    fn close(&self) {
        let mut state = self.state.lock().expect("timer callback gate poisoned");
        state.closed = true;
        let callback = state.callback.take();
        while !CallbackScope::contains(self.service) && state.runner.is_some() {
            state = self
                .settled
                .wait(state)
                .expect("timer callback gate poisoned");
        }
        drop(state);
        drop(callback);
    }
}
struct DebouncePending {
    disposed: bool,
    generation: u64,
    timer: Option<TimerHandle>,
}
struct DebounceState<T> {
    service: TimerService,
    delay: Duration,
    callback: Arc<CallbackGate<T>>,
    pending: Mutex<DebouncePending>,
}
impl<T> Drop for DebounceState<T> {
    fn drop(&mut self) {
        if let Some(timer) = self
            .pending
            .get_mut()
            .expect("debounce lock poisoned")
            .timer
            .take()
        {
            let _ = timer.cancel_and_join();
        }
    }
}
pub struct Debounced<T> {
    inner: Arc<DebounceState<T>>,
}
impl<T> Clone for Debounced<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}
impl<T: Send + 'static> Debounced<T> {
    pub fn call(&self, payload: T) -> Result<(), TimerError> {
        let (generation, old) = {
            let mut pending = self.inner.pending.lock().expect("debounce lock poisoned");
            if pending.disposed {
                return Err(TimerError::Cancelled);
            }
            pending.generation = pending
                .generation
                .checked_add(1)
                .expect("debounce identities exhausted");
            (pending.generation, pending.timer.take())
        };
        if let Some(timer) = old {
            timer.cancel();
        }
        let inner = Arc::downgrade(&self.inner);
        let timer = self.inner.service.timeout(self.inner.delay, move || {
            let Some(inner) = inner.upgrade() else {
                return;
            };
            let pending = inner.pending.lock().expect("debounce lock poisoned");
            if pending.disposed || pending.generation != generation {
                return;
            }
            drop(pending);
            let _ = inner.callback.run(payload);
        })?;
        let mut pending = self.inner.pending.lock().expect("debounce lock poisoned");
        if pending.disposed || pending.generation != generation {
            drop(pending);
            timer.cancel();
        } else {
            pending.timer = Some(timer);
        }
        Ok(())
    }
    pub fn dispose(&self) -> Result<(), TimerError> {
        let timer = {
            let mut pending = self.inner.pending.lock().expect("debounce lock poisoned");
            pending.disposed = true;
            pending.timer.take()
        };
        self.inner.callback.close();
        if let Some(timer) = timer {
            timer.cancel_and_join()?;
        }
        Ok(())
    }
}
struct ThrottlePending {
    disposed: bool,
    last: Option<Duration>,
    generation: u64,
    timer: Option<TimerHandle>,
}
struct ThrottleState<T> {
    service: TimerService,
    delay: Duration,
    no_trailing: bool,
    callback: Arc<CallbackGate<T>>,
    pending: Mutex<ThrottlePending>,
}
impl<T> Drop for ThrottleState<T> {
    fn drop(&mut self) {
        if let Some(timer) = self
            .pending
            .get_mut()
            .expect("throttle lock poisoned")
            .timer
            .take()
        {
            let _ = timer.cancel_and_join();
        }
    }
}
pub struct Throttled<T> {
    inner: Arc<ThrottleState<T>>,
}
impl<T> Clone for Throttled<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}
impl<T: Send + 'static> Throttled<T> {
    /// Leading calls execute synchronously, trailing calls on the timer worker.
    /// Callback access is serialized. `no_trailing` drops intervening payloads.
    pub fn call(&self, payload: T) -> Result<(), TimerError> {
        let (generation, remaining, old) = {
            let mut pending = self.inner.pending.lock().expect("throttle lock poisoned");
            if pending.disposed || self.inner.service.is_shutdown() {
                return Err(TimerError::Cancelled);
            }
            pending.generation = pending
                .generation
                .checked_add(1)
                .expect("throttle identities exhausted");
            let now = self.inner.service.now();
            let remaining = pending
                .last
                .map(|last| last.saturating_add(self.inner.delay).saturating_sub(now))
                .unwrap_or_default();
            if remaining.is_zero() {
                pending.last = Some(now);
            }
            (pending.generation, remaining, pending.timer.take())
        };
        if let Some(timer) = old {
            timer.cancel();
        }
        if remaining.is_zero() {
            self.inner.callback.run(payload)?;
        } else if !self.inner.no_trailing {
            let inner = Arc::downgrade(&self.inner);
            let timer = self.inner.service.timeout(remaining, move || {
                let Some(inner) = inner.upgrade() else {
                    return;
                };
                let mut pending = inner.pending.lock().expect("throttle lock poisoned");
                if pending.disposed || pending.generation != generation {
                    return;
                }
                pending.last = Some(inner.service.now());
                drop(pending);
                let _ = inner.callback.run(payload);
            })?;
            let mut pending = self.inner.pending.lock().expect("throttle lock poisoned");
            if pending.disposed || pending.generation != generation {
                drop(pending);
                timer.cancel();
            } else {
                pending.timer = Some(timer);
            }
        }
        Ok(())
    }
    pub fn dispose(&self) -> Result<(), TimerError> {
        let timer = {
            let mut pending = self.inner.pending.lock().expect("throttle lock poisoned");
            pending.disposed = true;
            pending.timer.take()
        };
        self.inner.callback.close();
        if let Some(timer) = timer {
            timer.cancel_and_join()?;
        }
        Ok(())
    }
}

impl crate::Setup<'_> {
    pub fn timer(&mut self) -> TimerService {
        TimerService::owned(self)
    }
    pub fn timeout(
        &mut self,
        delay: Duration,
        callback: impl FnOnce() + Send + 'static,
    ) -> Result<TimerHandle, TimerError> {
        self.timer().timeout(delay, callback)
    }
    pub fn interval(
        &mut self,
        period: Duration,
        callback: impl FnMut() + Send + 'static,
    ) -> Result<TimerHandle, TimerError> {
        self.timer().interval(period, callback)
    }
    pub fn set_timeout(
        &mut self,
        callback: impl FnOnce() + Send + 'static,
        delay: Duration,
    ) -> Result<TimerHandle, TimerError> {
        self.timeout(delay, callback)
    }
    pub fn set_interval(
        &mut self,
        callback: impl FnMut() + Send + 'static,
        period: Duration,
    ) -> Result<TimerHandle, TimerError> {
        self.interval(period, callback)
    }
    pub fn sleep(&mut self, delay: Duration) -> Sleep {
        self.timer().sleep(delay)
    }
    pub fn ticks(&mut self, period: Duration) -> Result<Interval, TimerError> {
        self.timer().ticks(period)
    }
    pub fn debounce<T: Send + 'static>(
        &mut self,
        delay: Duration,
        callback: impl FnMut(T) + Send + 'static,
    ) -> Debounced<T> {
        self.timer().debounce(delay, callback)
    }
    pub fn throttle<T: Send + 'static>(
        &mut self,
        delay: Duration,
        no_trailing: bool,
        callback: impl FnMut(T) + Send + 'static,
    ) -> Throttled<T> {
        self.timer().throttle(delay, no_trailing, callback)
    }
}
impl crate::AsyncSetup {
    pub fn timer(&self) -> Result<TimerService, String> {
        TimerService::owned_async(self)
    }
    pub fn timeout(
        &self,
        delay: Duration,
        callback: impl FnOnce() + Send + 'static,
    ) -> Result<TimerHandle, String> {
        self.timer()?
            .timeout(delay, callback)
            .map_err(|error| error.to_string())
    }
    pub fn interval(
        &self,
        period: Duration,
        callback: impl FnMut() + Send + 'static,
    ) -> Result<TimerHandle, String> {
        self.timer()?
            .interval(period, callback)
            .map_err(|error| error.to_string())
    }
    pub fn set_timeout(
        &self,
        callback: impl FnOnce() + Send + 'static,
        delay: Duration,
    ) -> Result<TimerHandle, String> {
        self.timeout(delay, callback)
    }
    pub fn set_interval(
        &self,
        callback: impl FnMut() + Send + 'static,
        period: Duration,
    ) -> Result<TimerHandle, String> {
        self.interval(period, callback)
    }
    pub fn sleep(&self, delay: Duration) -> Result<Sleep, String> {
        Ok(self.timer()?.sleep(delay))
    }
    pub fn ticks(&self, period: Duration) -> Result<Interval, String> {
        self.timer()?
            .ticks(period)
            .map_err(|error| error.to_string())
    }
    pub fn debounce<T: Send + 'static>(
        &self,
        delay: Duration,
        callback: impl FnMut(T) + Send + 'static,
    ) -> Result<Debounced<T>, String> {
        Ok(self.timer()?.debounce(delay, callback))
    }
    pub fn throttle<T: Send + 'static>(
        &self,
        delay: Duration,
        no_trailing: bool,
        callback: impl FnMut(T) + Send + 'static,
    ) -> Result<Throttled<T>, String> {
        Ok(self.timer()?.throttle(delay, no_trailing, callback))
    }
}
