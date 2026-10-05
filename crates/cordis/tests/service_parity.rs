use cordis::{
    AsyncSetup, Context, Phase, Plugin, Runtime, RuntimeError, ServiceHandle, ServiceKey,
};
use serde_json::json;
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Wake, Waker};

struct ThreadWake(std::thread::Thread);
impl Wake for ThreadWake {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.0.unpark();
    }
}
fn block_on<F: Future>(future: F) -> F::Output {
    let waker = Waker::from(Arc::new(ThreadWake(std::thread::current())));
    let mut cx = TaskContext::from_waker(&waker);
    let mut future = std::pin::pin!(future);
    loop {
        match future.as_mut().poll(&mut cx) {
            Poll::Ready(result) => return result,
            Poll::Pending => std::thread::park_timeout(std::time::Duration::from_secs(1)),
        }
    }
}
fn poll(runtime: &mut Runtime) -> Poll<Result<(), RuntimeError>> {
    let waker = Waker::from(Arc::new(ThreadWake(std::thread::current())));
    let mut cx = TaskContext::from_waker(&waker);
    Pin::new(&mut runtime.settle()).poll(&mut cx)
}
#[derive(Default)]
struct Gate {
    ready: AtomicBool,
    waker: Mutex<Option<Waker>>,
}
impl Gate {
    fn release(&self) {
        self.ready.store(true, Ordering::SeqCst);
        if let Some(waker) = self.waker.lock().unwrap().take() {
            waker.wake();
        }
    }
}
struct Wait(Arc<Gate>);
impl Future for Wait {
    type Output = ();
    fn poll(self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<()> {
        *self.0.waker.lock().unwrap() = Some(cx.waker().clone());
        if self.0.ready.load(Ordering::SeqCst) {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

#[test]
fn subsequent_committed_reads_share_updates_but_keep_provider_identity_during_cleanup() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("shared");
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |setup| {
                setup.provide(key, 1)?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let escaped: Arc<Mutex<Option<AsyncSetup>>> = Arc::default();
    let saved = escaped.clone();
    let cleanup = Arc::new(Gate::default());
    let gate = cleanup.clone();
    let observed = Arc::new(AtomicUsize::new(0));
    let seen = observed.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |setup| {
                *saved.lock().unwrap() = Some(setup.to_async());
                let setup = setup.to_async();
                let gate = gate.clone();
                let seen = seen.clone();
                setup.clone().on_cleanup_async(move || async move {
                    Wait(gate).await;
                    seen.store(*setup.get(key)?, Ordering::SeqCst);
                    Ok(())
                })?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let episode = escaped.lock().unwrap().clone().unwrap();
    let earlier = episode.get(key).unwrap();
    runtime.set(provider, key, 2).unwrap();
    assert_eq!(*earlier, 1);
    assert_eq!(*episode.get(key).unwrap(), 2);
    assert_eq!(runtime.committed(consumer)[0].provider, provider);
    runtime.dispose(provider).unwrap();
    assert!(poll(&mut runtime).is_pending());
    assert!(runtime.get(&context, key).is_none());
    assert_eq!(*episode.get(key).unwrap(), 2);
    cleanup.release();
    block_on(runtime.settle()).unwrap();
    assert_eq!(observed.load(Ordering::SeqCst), 2);
    let next = runtime
        .mount(
            &context,
            None,
            Plugin::new("replacement", move |setup| {
                setup.provide(key, 99)?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(*runtime.get(&context, key).unwrap(), 99);
    assert_eq!(runtime.committed(consumer)[0].provider, next);
    assert!(episode.get(key).is_err());
}

#[test]
fn owner_cleanup_waits_for_dynamic_service_and_its_consumers() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("dynamic");
    let handle: Arc<Mutex<Option<ServiceHandle<usize>>>> = Arc::default();
    let saved = handle.clone();
    let owner_alive = Arc::new(AtomicBool::new(true));
    let alive = owner_alive.clone();
    let owner = runtime
        .mount(
            &context,
            None,
            Plugin::new("owner", move |setup| {
                let alive = alive.clone();
                setup.on_cleanup(move || {
                    alive.store(false, Ordering::SeqCst);
                    Ok(())
                });
                *saved.lock().unwrap() = Some(setup.publish(key, 7)?);
                Ok(())
            }),
        )
        .unwrap();
    let cleanup = Arc::new(Gate::default());
    let gate = cleanup.clone();
    let alive = owner_alive.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |setup| {
                assert_eq!(*setup.get(key)?, 7);
                let gate = gate.clone();
                let alive = alive.clone();
                let setup = setup.to_async();
                setup.clone().on_cleanup_async(move || async move {
                    assert!(alive.load(Ordering::SeqCst));
                    Wait(gate).await;
                    assert!(alive.load(Ordering::SeqCst));
                    assert_eq!(*setup.get(key)?, 7);
                    Ok(())
                })?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let handle = handle.lock().unwrap().clone().unwrap();
    assert!(handle.initialized());
    assert_ne!(handle.id(), Some(owner));
    runtime.dispose(owner).unwrap();
    assert!(poll(&mut runtime).is_pending());
    assert!(owner_alive.load(Ordering::SeqCst));
    assert!(!handle.finished());
    cleanup.release();
    block_on(runtime.settle()).unwrap();
    assert!(!owner_alive.load(Ordering::SeqCst));
    assert!(!runtime.contains(owner));
    assert_eq!(runtime.phase(consumer), Some(Phase::Inactive));
    assert!(handle.finished());
    block_on(handle.join()).unwrap();
}

#[test]
fn independent_revoke_and_republish_preserves_owner() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("optional");
    let owner = runtime
        .mount(&context, None, Plugin::new("owner", |_| Ok(())))
        .unwrap();
    let seen = Arc::new(AtomicUsize::new(0));
    let observed = seen.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |setup| {
                observed.store(*setup.get(key)?, Ordering::SeqCst);
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let setup = runtime.owner_context(owner).unwrap();
    let first = setup.publish(key, 1).unwrap();
    block_on(runtime.settle()).unwrap();
    let first_id = first.id().unwrap();
    first.set(2).unwrap();
    assert_eq!(
        *runtime.owner_context(consumer).unwrap().get(key).unwrap(),
        2
    );
    first.dispose();
    first.dispose();
    block_on(runtime.settle()).unwrap();
    block_on(first.join()).unwrap();
    assert_eq!(runtime.phase(owner), Some(Phase::Active));
    assert_eq!(runtime.phase(consumer), Some(Phase::Inactive));
    assert!(first.set(3).is_err());
    let second = setup.publish(key, 4).unwrap();
    block_on(runtime.settle()).unwrap();
    assert!(second.id().unwrap() > first_id);
    assert_eq!(seen.load(Ordering::SeqCst), 4);
}

#[test]
fn revocation_retains_in_flight_setup_until_it_registers_cleanup() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("pending");
    let owner = runtime
        .mount(&context, None, Plugin::new("owner", |_| Ok(())))
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let service = runtime
        .owner_context(owner)
        .unwrap()
        .publish(key, 3)
        .unwrap();
    let gate = Arc::new(Gate::default());
    let wait = gate.clone();
    let cleaned = Arc::new(AtomicBool::new(false));
    let done = cleaned.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new_async("consumer", move |setup| {
                let wait = wait.clone();
                let done = done.clone();
                async move {
                    Wait(wait).await;
                    assert_eq!(*setup.get(key)?, 3);
                    setup.on_cleanup(move || {
                        done.store(true, Ordering::SeqCst);
                        Ok(())
                    })?;
                    Ok(())
                }
            })
            .requires(key),
        )
        .unwrap();
    assert!(poll(&mut runtime).is_pending());
    service.dispose();
    assert!(poll(&mut runtime).is_pending());
    assert!(!service.finished());
    assert!(!cleaned.load(Ordering::SeqCst));
    gate.release();
    block_on(runtime.settle()).unwrap();
    assert!(service.finished());
    assert!(cleaned.load(Ordering::SeqCst));
    assert_eq!(runtime.phase(consumer), Some(Phase::Inactive));
}

#[test]
fn consumer_specific_checks_refresh_without_changing_committed_reads() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("checked");
    let available = Arc::new(AtomicBool::new(true));
    let enabled = available.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |setup| {
                let enabled = enabled.clone();
                setup.provide_checked(key, 10, move |value, _, config| {
                    enabled.load(Ordering::SeqCst) && config.as_u64() == Some(*value as u64)
                })?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let accepted = runtime
        .mount(
            &context,
            None,
            Plugin::new("accepted", |_| Ok(())).requires_with_config(key, json!(10)),
        )
        .unwrap();
    let rejected = runtime
        .mount(
            &context,
            None,
            Plugin::new("rejected", |_| Ok(())).requires_with_config(key, json!(20)),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.phase(accepted), Some(Phase::Active));
    assert_eq!(runtime.phase(rejected), Some(Phase::Inactive));
    let episode = runtime.owner_context(accepted).unwrap();
    available.store(false, Ordering::SeqCst);
    assert_eq!(*episode.get(key).unwrap(), 10);
    runtime.owner_context(provider).unwrap().refresh().unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.phase(accepted), Some(Phase::Inactive));
    available.store(true, Ordering::SeqCst);
    runtime.set(provider, key, 20).unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.phase(accepted), Some(Phase::Inactive));
    assert_eq!(runtime.phase(rejected), Some(Phase::Active));
}

#[test]
fn predicate_panics_are_unavailable_and_cancelled_queued_publication_never_mounts() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("panic");
    let owner = runtime
        .mount(&context, None, Plugin::new("owner", |_| Ok(())))
        .unwrap();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", |_| Ok(())).requires(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let setup = runtime.owner_context(owner).unwrap();
    let cancelled = setup.publish(key, 1).unwrap();
    cancelled.dispose();
    block_on(runtime.settle()).unwrap();
    assert!(cancelled.finished());
    assert_eq!(cancelled.id(), None);
    let service = setup
        .publish_checked(key, 2, |_, _, _| panic!("predicate failure"))
        .unwrap();
    block_on(runtime.settle()).unwrap();
    assert!(service.initialized());
    assert_eq!(runtime.phase(consumer), Some(Phase::Inactive));
    service.dispose();
    block_on(runtime.settle()).unwrap();
    assert!(service.finished());
}

#[test]
fn duplicate_dynamic_publication_reports_handle_error_without_failing_owner() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("exclusive");
    let owner = runtime
        .mount(&context, None, Plugin::new("owner", |_| Ok(())))
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let setup = runtime.owner_context(owner).unwrap();
    let first = setup.publish(key, 1).unwrap();
    block_on(runtime.settle()).unwrap();
    let duplicate = setup.publish(key, 2).unwrap();
    block_on(runtime.settle()).unwrap();
    assert!(duplicate.finished());
    assert_eq!(duplicate.id(), None);
    assert!(block_on(duplicate.join()).is_err());
    assert!(duplicate.errors()[0].contains("Conflict"));
    assert_eq!(runtime.phase(owner), Some(Phase::Active));
    assert_eq!(*runtime.get(&context, key).unwrap(), 1);
    assert!(!first.finished());
    runtime.dispose(owner).unwrap();
    block_on(runtime.settle()).unwrap();
    assert!(first.finished());
}

#[test]
fn checks_receive_inherited_config_and_snapshots_do_not_invoke_user_predicates() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("inherited");
    let checks = Arc::new(AtomicUsize::new(0));
    let count = checks.clone();
    runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |setup| {
                let count = count.clone();
                setup.provide_checked(key, 10, move |_, _, config| {
                    count.fetch_add(1, Ordering::SeqCst);
                    config == &json!({"tenant": "a"})
                })?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let child_started = Arc::new(AtomicBool::new(false));
    let child = child_started.clone();
    runtime
        .mount(
            &context,
            None,
            Plugin::new("parent", move |setup| {
                let child = child.clone();
                setup.mount(Plugin::new("child", move |setup| {
                    assert_eq!(*setup.get(key)?, 10);
                    child.store(true, Ordering::SeqCst);
                    Ok(())
                }))?;
                Ok(())
            })
            .requires_with_config(key, json!({"tenant": "a"})),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    assert!(child_started.load(Ordering::SeqCst));
    let before = checks.load(Ordering::SeqCst);
    assert!(before > 0);
    assert_eq!(runtime.snapshot().plugins.len(), 3);
    assert_eq!(*runtime.get(&context, key).unwrap(), 10);
    assert_eq!(checks.load(Ordering::SeqCst), before);
}
