use cordis::{Context, Plugin, Runtime, RuntimeError, ServiceKey};
use cordis_kernel::Phase;
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
            Poll::Ready(value) => return value,
            Poll::Pending => std::thread::park_timeout(std::time::Duration::from_secs(2)),
        }
    }
}
fn poll_once(runtime: &mut Runtime) -> Poll<Result<(), RuntimeError>> {
    let waker = Waker::from(Arc::new(ThreadWake(std::thread::current())));
    let mut cx = TaskContext::from_waker(&waker);
    let mut settle = runtime.settle();
    Pin::new(&mut settle).poll(&mut cx)
}

#[derive(Default)]
struct Gate {
    open: AtomicBool,
    waker: Mutex<Option<Waker>>,
}
impl Gate {
    fn release(&self) {
        self.open.store(true, Ordering::SeqCst);
        if let Some(waker) = self.waker.lock().unwrap().take() {
            waker.wake();
        }
    }
}
struct WaitGate(Arc<Gate>);
impl Future for WaitGate {
    type Output = ();
    fn poll(self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<()> {
        *self.0.waker.lock().unwrap() = Some(cx.waker().clone());
        if self.0.open.load(Ordering::SeqCst) {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

#[test]
fn missing_dependency_activates_later_and_uses_a_typed_service() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let service = ServiceKey::<usize>::new("answer");
    let observed = Arc::new(AtomicUsize::new(0));
    let seen = observed.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |ctx| {
                seen.store(*ctx.get(service)?, Ordering::SeqCst);
                Ok(())
            })
            .requires(service),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.phase(consumer), Some(Phase::Inactive));
    assert_eq!(observed.load(Ordering::SeqCst), 0);
    runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |ctx| {
                ctx.provide(service, 42)?;
                Ok(())
            })
            .provides(service),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.phase(consumer), Some(Phase::Active));
    assert_eq!(observed.load(Ordering::SeqCst), 42);
    assert_eq!(*runtime.get(&context, service).unwrap(), 42);
}

#[test]
fn isolated_realms_do_not_cross_and_can_be_shared_explicitly() {
    let mut runtime = Runtime::new();
    let root = Context::new();
    let service = ServiceKey::<u32>::new("database");
    let isolated = root.isolate(service);
    let shared = root.share(service, &isolated);
    for (ctx, value) in [(&root, 1), (&isolated, 2)] {
        runtime
            .mount(
                ctx,
                None,
                Plugin::new("provider", move |setup| {
                    setup.provide(service, value)?;
                    Ok(())
                })
                .provides(service),
            )
            .unwrap();
    }
    block_on(runtime.settle()).unwrap();
    assert_eq!(*runtime.get(&root, service).unwrap(), 1);
    assert_eq!(*runtime.get(&isolated, service).unwrap(), 2);
    assert_eq!(*runtime.get(&shared, service).unwrap(), 2);
    let conflict = runtime.mount(
        &shared,
        None,
        Plugin::new("duplicate", |_| Ok(())).provides(service),
    );
    assert!(matches!(conflict, Err(RuntimeError::Kernel(_))));
}

fn teardown_case(retire_everything: bool) {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let resource = ServiceKey::<Arc<AtomicBool>>::new("resource");
    let live = Arc::new(AtomicBool::new(true));
    let provider_live = live.clone();
    let log = Arc::new(Mutex::new(Vec::new()));
    let provider_log = log.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |ctx| {
                ctx.provide(resource, provider_live.clone())?;
                let live = provider_live.clone();
                let log = provider_log.clone();
                ctx.on_cleanup(move || {
                    live.store(false, Ordering::SeqCst);
                    log.lock().unwrap().push("provider-cleanup");
                    Ok(())
                });
                Ok(())
            })
            .provides(resource),
        )
        .unwrap();
    let gate = Arc::new(Gate::default());
    let consumer_gate = gate.clone();
    let consumer_log = log.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |ctx| {
                let bound = ctx.get(resource)?;
                let gate = consumer_gate.clone();
                let log = consumer_log.clone();
                ctx.on_cleanup_async(move || async move {
                    assert!(bound.load(Ordering::SeqCst));
                    log.lock().unwrap().push("consumer-start");
                    WaitGate(gate).await;
                    assert!(bound.load(Ordering::SeqCst));
                    log.lock().unwrap().push("consumer-finish");
                    Ok(())
                });
                Ok(())
            })
            .requires(resource),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    if retire_everything {
        runtime.dispose_all().unwrap();
    } else {
        runtime.dispose(provider).unwrap();
    }
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert!(live.load(Ordering::SeqCst));
    assert!(
        runtime.contains(consumer),
        "retired cleanup must remain discoverable"
    );
    assert_eq!(runtime.phase(consumer), Some(Phase::Unloading));
    assert!(!runtime.cleanup_started(provider));
    assert_eq!(runtime.committed(consumer)[0].provider, provider);
    assert_eq!(*log.lock().unwrap(), vec!["consumer-start"]);
    gate.release();
    block_on(runtime.settle()).unwrap();
    assert!(!live.load(Ordering::SeqCst));
    assert!(!runtime.contains(provider));
    assert_eq!(
        *log.lock().unwrap(),
        vec!["consumer-start", "consumer-finish", "provider-cleanup"]
    );
    assert_eq!(runtime.contains(consumer), !retire_everything);
}

#[test]
fn provider_waits_for_async_consumer_cleanup() {
    teardown_case(false);
}

#[test]
fn concurrent_root_disposal_keeps_retired_consumer_discoverable() {
    teardown_case(true);
}

#[test]
fn replacement_has_a_fresh_provider_identity_and_rebinds_consumer() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let service = ServiceKey::<u32>::new("provider");
    let seen = Arc::new(Mutex::new(Vec::new()));
    let output = seen.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |ctx| {
                output.lock().unwrap().push(*ctx.get(service)?);
                Ok(())
            })
            .requires(service),
        )
        .unwrap();
    let make_provider = |value| {
        Plugin::new("provider", move |ctx| {
            ctx.provide(service, value)?;
            Ok(())
        })
        .provides(service)
    };
    let first = runtime.mount(&context, None, make_provider(1)).unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.committed(consumer)[0].provider, first);
    runtime.dispose(first).unwrap();
    block_on(runtime.settle()).unwrap();
    let replacement = runtime.mount(&context, None, make_provider(2)).unwrap();
    assert!(replacement > first);
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.committed(consumer)[0].provider, replacement);
    assert_eq!(*seen.lock().unwrap(), vec![1, 2]);
}

#[test]
fn cleanup_is_lifo_and_errors_do_not_skip_remaining_inverses() {
    let mut runtime = Runtime::new();
    let log = Arc::new(Mutex::new(Vec::new()));
    let output = log.clone();
    let id = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("effects", move |ctx| {
                for number in 1..=3 {
                    let output = output.clone();
                    ctx.on_cleanup(move || {
                        output.lock().unwrap().push(number);
                        if number == 2 {
                            Err("cleanup failed".into())
                        } else {
                            Ok(())
                        }
                    });
                }
                Ok(())
            }),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    runtime.dispose(id).unwrap();
    runtime.dispose(id).unwrap();
    block_on(runtime.settle()).unwrap();
    runtime.dispose(id).unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(*log.lock().unwrap(), vec![3, 2, 1]);
    assert_eq!(
        runtime.take_cleanup_errors(),
        vec![RuntimeError::Cleanup {
            plugin: id,
            message: "cleanup failed".into()
        }]
    );
}

#[test]
fn setup_failure_rolls_back_and_latches_until_update() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<u32>::new("value");
    let runs = Arc::new(AtomicUsize::new(0));
    let cleanups = Arc::new(AtomicUsize::new(0));
    let count = runs.clone();
    let inverse = cleanups.clone();
    let id = runtime
        .mount(
            &context,
            None,
            Plugin::new("fails", move |ctx| {
                count.fetch_add(1, Ordering::SeqCst);
                ctx.provide(key, 1)?;
                let inverse = inverse.clone();
                ctx.on_cleanup(move || {
                    inverse.fetch_add(1, Ordering::SeqCst);
                    Ok(())
                });
                Err("setup failed".into())
            })
            .provides(key),
        )
        .unwrap();
    assert!(matches!(
        block_on(runtime.settle()),
        Err(RuntimeError::Setup { .. })
    ));
    assert_eq!(runtime.phase(id), Some(Phase::Inactive));
    assert!(runtime.get(&context, key).is_none());
    assert_eq!(cleanups.load(Ordering::SeqCst), 1);
    assert!(block_on(runtime.settle()).is_err());
    assert_eq!(runs.load(Ordering::SeqCst), 1);
    runtime
        .update(id, move |ctx| {
            ctx.provide(key, 2)?;
            Ok(())
        })
        .unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(*runtime.get(&context, key).unwrap(), 2);
    assert!(runtime.failure(id).is_none());
}

#[test]
fn restart_unloads_dependents_before_running_new_setup() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("counter");
    let generation = Arc::new(AtomicUsize::new(0));
    let counter = generation.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |ctx| {
                ctx.provide(key, counter.fetch_add(1, Ordering::SeqCst) + 1)?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let log = Arc::new(Mutex::new(Vec::new()));
    let output = log.clone();
    runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |ctx| {
                let value = *ctx.get(key)?;
                output.lock().unwrap().push(value);
                let output = output.clone();
                ctx.on_cleanup(move || {
                    output.lock().unwrap().push(value * 10);
                    Ok(())
                });
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    runtime.restart(provider).unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(*log.lock().unwrap(), vec![1, 10, 2]);
}

#[test]
fn owned_children_are_retired_and_removed_with_their_parent() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let root = runtime
        .mount(&context, None, Plugin::new("root", |_| Ok(())))
        .unwrap();
    let child = runtime
        .mount(&context, Some(root), Plugin::new("child", |_| Ok(())))
        .unwrap();
    let grandchild = runtime
        .mount(&context, Some(child), Plugin::new("grandchild", |_| Ok(())))
        .unwrap();
    block_on(runtime.settle()).unwrap();
    runtime.dispose(root).unwrap();
    block_on(runtime.settle()).unwrap();
    assert!(!runtime.contains(root));
    assert!(!runtime.contains(child));
    assert!(!runtime.contains(grandchild));
}

#[test]
fn an_undeclared_dependency_is_rejected_before_a_callback_can_use_it() {
    let mut runtime = Runtime::new();
    let key = ServiceKey::<usize>::new("private");
    let context = Context::new();
    runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |ctx| {
                ctx.provide(key, 7)?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |ctx| {
                let _ = ctx.get(key)?;
                Ok(())
            }),
        )
        .unwrap();
    let error = block_on(runtime.settle()).unwrap_err();
    assert!(
        matches!(error, RuntimeError::Setup { message, .. } if message.contains("undeclared dependency"))
    );
}

#[test]
fn a_declared_port_without_a_payload_never_becomes_available() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("missing-value");
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("incomplete-provider", |_| Ok(())).provides(key),
        )
        .unwrap();
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |_| {
                observed.fetch_add(1, Ordering::SeqCst);
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    assert!(
        matches!(block_on(runtime.settle()), Err(RuntimeError::Setup { plugin, .. }) if plugin == provider)
    );
    assert_eq!(runtime.phase(provider), Some(Phase::Inactive));
    assert_eq!(runtime.phase(consumer), Some(Phase::Inactive));
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert!(runtime.get(&context, key).is_none());
}

#[test]
fn replace_uses_retire_remove_reinsert_and_preserves_scope() {
    let mut runtime = Runtime::new();
    let key = ServiceKey::<u32>::new("version");
    let root = Context::new();
    let isolated = root.isolate(key);
    let make = |version| {
        Plugin::new("version", move |ctx| {
            ctx.provide(key, version)?;
            Ok(())
        })
        .provides(key)
    };
    let old = runtime.mount(&isolated, None, make(1)).unwrap();
    block_on(runtime.settle()).unwrap();
    let new = block_on(runtime.replace(old, make(2))).unwrap();
    assert!(new > old);
    assert!(!runtime.contains(old));
    assert_eq!(*runtime.get(&isolated, key).unwrap(), 2);
    assert!(runtime.get(&root, key).is_none());
}

#[test]
fn ownership_does_not_add_a_dependency_edge_against_declared_dependencies() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<u32>::new("child-service");
    let parent = runtime
        .mount(
            &context,
            None,
            Plugin::new("parent-consumer", move |ctx| {
                assert_eq!(*ctx.get(key)?, 9);
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    let child = runtime
        .mount(
            &context,
            Some(parent),
            Plugin::new("child-provider", move |ctx| {
                ctx.provide(key, 9)?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.phase(parent), Some(Phase::Active));
    runtime.dispose(parent).unwrap();
    block_on(runtime.settle()).unwrap();
    assert!(!runtime.contains(parent));
    assert!(!runtime.contains(child));
}

#[test]
fn mounting_a_child_during_owner_cleanup_is_rejected() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let gate = Arc::new(Gate::default());
    let cleanup_gate = gate.clone();
    let owner = runtime
        .mount(
            &context,
            None,
            Plugin::new("owner", move |ctx| {
                let gate = cleanup_gate.clone();
                ctx.on_cleanup_async(move || async move {
                    WaitGate(gate).await;
                    Ok(())
                });
                Ok(())
            }),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    runtime.restart(owner).unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert_eq!(runtime.phase(owner), Some(Phase::Unloading));
    assert!(!runtime.retired(owner));
    assert_eq!(
        runtime.mount(&context, Some(owner), Plugin::new("late-child", |_| Ok(()))),
        Err(RuntimeError::UnloadingOwner(owner))
    );
    gate.release();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.ids(), vec![owner]);
    runtime.dispose_all().unwrap();
    block_on(runtime.settle()).unwrap();
}

struct CountingWake(AtomicUsize);
impl Wake for CountingWake {
    fn wake(self: Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn cancelled_settle_preserves_cleanup_and_resumes_with_the_new_waker() {
    let mut runtime = Runtime::new();
    let gate = Arc::new(Gate::default());
    let starts = Arc::new(AtomicUsize::new(0));
    let finishes = Arc::new(AtomicUsize::new(0));
    let setup_gate = gate.clone();
    let setup_starts = starts.clone();
    let setup_finishes = finishes.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("owner", move |ctx| {
                let gate = setup_gate.clone();
                let starts = setup_starts.clone();
                let finishes = setup_finishes.clone();
                ctx.on_cleanup_async(move || async move {
                    starts.fetch_add(1, Ordering::SeqCst);
                    WaitGate(gate).await;
                    finishes.fetch_add(1, Ordering::SeqCst);
                    Ok(())
                });
                Ok(())
            }),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    runtime.dispose(owner).unwrap();

    let first = Arc::new(CountingWake(AtomicUsize::new(0)));
    let second = Arc::new(CountingWake(AtomicUsize::new(0)));
    {
        let waker = Waker::from(first.clone());
        let mut cx = TaskContext::from_waker(&waker);
        let mut cancelled = runtime.settle();
        assert_eq!(Pin::new(&mut cancelled).poll(&mut cx), Poll::Pending);
    }
    {
        let waker = Waker::from(second.clone());
        let mut cx = TaskContext::from_waker(&waker);
        let mut resumed = runtime.settle();
        assert_eq!(Pin::new(&mut resumed).poll(&mut cx), Poll::Pending);
        gate.release();
        assert_eq!(first.0.load(Ordering::SeqCst), 0);
        assert_eq!(second.0.load(Ordering::SeqCst), 1);
        assert_eq!(Pin::new(&mut resumed).poll(&mut cx), Poll::Ready(Ok(())));
    }
    assert_eq!(starts.load(Ordering::SeqCst), 1);
    assert_eq!(finishes.load(Ordering::SeqCst), 1);
    assert!(!runtime.contains(owner));
}

#[test]
fn set_keeps_provider_identity_but_previously_returned_arcs_are_snapshots() {
    let mut runtime = Runtime::new();
    let key = ServiceKey::<u32>::new("value");
    let context = Context::new();
    let previous = Arc::new(Mutex::new(None));
    let captured = previous.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |ctx| {
                *captured.lock().unwrap() = Some(ctx.provide(key, 1)?);
                ctx.set(key, 2)?;
                assert_eq!(*ctx.get(key)?, 2);
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |ctx| {
                assert_eq!(*ctx.get(key)?, 2);
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(**previous.lock().unwrap().as_ref().unwrap(), 1);
    assert_eq!(*runtime.get(&context, key).unwrap(), 2);
    assert_eq!(runtime.committed(consumer)[0].provider, provider);
}

#[test]
fn async_setup_keeps_payload_private_until_all_stages_finish() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("async-payload");
    let gate = Arc::new(Gate::default());
    let captured = gate.clone();
    let id = runtime
        .mount(
            &context,
            None,
            Plugin::new_async("async-provider", move |ctx| {
                let gate = captured.clone();
                async move {
                    ctx.provide(key, 73)?;
                    WaitGate(gate).await;
                    ctx.set(key, 74)?;
                    Ok(())
                }
            })
            .provides(key),
        )
        .unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert_eq!(runtime.phase(id), Some(Phase::Loading));
    assert!(runtime.get(&context, key).is_none());
    gate.release();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.phase(id), Some(Phase::Active));
    assert_eq!(*runtime.get(&context, key).unwrap(), 74);
}

#[test]
fn withdrawal_waits_for_pending_setup_landing_and_its_inverse() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<Arc<AtomicBool>>::new("provider-life");
    let live = Arc::new(AtomicBool::new(true));
    let provider_live = live.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |ctx| {
                ctx.provide(key, provider_live.clone())?;
                let live = provider_live.clone();
                ctx.on_cleanup(move || {
                    live.store(false, Ordering::SeqCst);
                    Ok(())
                });
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let gate = Arc::new(Gate::default());
    let setup_gate = gate.clone();
    let inverse_count = Arc::new(AtomicUsize::new(0));
    let cleaned = inverse_count.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new_async("consumer", move |ctx| {
                let gate = setup_gate.clone();
                let cleaned = cleaned.clone();
                async move {
                    let live = ctx.get(key)?;
                    WaitGate(gate).await;
                    assert!(live.load(Ordering::SeqCst));
                    ctx.on_cleanup(move || {
                        assert!(live.load(Ordering::SeqCst));
                        cleaned.fetch_add(1, Ordering::SeqCst);
                        Ok(())
                    })?;
                    Ok(())
                }
            })
            .requires(key),
        )
        .unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    runtime.dispose(provider).unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert_eq!(runtime.phase(consumer), Some(Phase::Unloading));
    assert!(!runtime.cleanup_started(consumer));
    assert!(!runtime.cleanup_started(provider));
    assert!(live.load(Ordering::SeqCst));
    gate.release();
    block_on(runtime.settle()).unwrap();
    assert_eq!(inverse_count.load(Ordering::SeqCst), 1);
    assert!(!live.load(Ordering::SeqCst));
    assert_eq!(runtime.phase(consumer), Some(Phase::Inactive));
}

#[test]
fn cancelled_iterator_lands_current_stage_but_never_starts_the_next() {
    use cordis::{Effect, Inverse};
    let mut runtime = Runtime::new();
    let gate = Arc::new(Gate::default());
    let started = Arc::new(AtomicUsize::new(0));
    let restored = Arc::new(AtomicUsize::new(0));
    let captured = Arc::new(Mutex::new(None));
    let output = captured.clone();
    let wait = gate.clone();
    let starts = started.clone();
    let restores = restored.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("iterator", move |ctx| {
                let gate = wait.clone();
                let started = starts.clone();
                let restored = restores.clone();
                let never = started.clone();
                *output.lock().unwrap() = Some(
                    ctx.effect(
                        Effect::new()
                            .step(move |_| async move {
                                started.fetch_add(1, Ordering::SeqCst);
                                WaitGate(gate).await;
                                Ok(Inverse::new(move || {
                                    restored.fetch_add(1, Ordering::SeqCst);
                                    Ok(())
                                }))
                            })
                            .step(move |_| async move {
                                never.fetch_add(100, Ordering::SeqCst);
                                Ok(Inverse::empty())
                            }),
                    )?,
                );
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    let handle = captured.lock().unwrap().clone().unwrap();
    handle.cancel();
    handle.cancel();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert!(!handle.finished());
    assert_eq!(restored.load(Ordering::SeqCst), 0);
    gate.release();
    block_on(runtime.settle()).unwrap();
    block_on(handle.join()).unwrap();
    block_on(handle.join()).unwrap();
    assert_eq!(started.load(Ordering::SeqCst), 1);
    assert_eq!(restored.load(Ordering::SeqCst), 1);
    assert_eq!(runtime.phase(owner), Some(Phase::Active));
    runtime.dispose(owner).unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(restored.load(Ordering::SeqCst), 1);
}

#[test]
fn independent_effect_groups_restore_concurrently_and_each_remains_lifo() {
    use cordis::{Effect, Inverse};
    let mut runtime = Runtime::new();
    let gate = Arc::new(Gate::default());
    let log = Arc::new(Mutex::new(Vec::new()));
    let wait = gate.clone();
    let output = log.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("groups", move |ctx| {
                for group in [1, 2] {
                    let first = output.clone();
                    let last = output.clone();
                    let gate = wait.clone();
                    ctx.effect(
                        Effect::new()
                            .inverse(Inverse::new(move || {
                                first.lock().unwrap().push((group, 1));
                                Ok(())
                            }))
                            .inverse(Inverse::new_async(move || async move {
                                last.lock().unwrap().push((group, 2));
                                WaitGate(gate).await;
                                last.lock().unwrap().push((group, 3));
                                Ok(())
                            })),
                    )?;
                }
                Ok(())
            }),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    runtime.dispose(owner).unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert_eq!(*log.lock().unwrap(), vec![(1, 2), (2, 2)]);
    gate.release();
    block_on(runtime.settle()).unwrap();
    let entries = log.lock().unwrap();
    for group in [1, 2] {
        assert_eq!(
            entries
                .iter()
                .filter(|(g, _)| *g == group)
                .map(|(_, value)| *value)
                .collect::<Vec<_>>(),
            vec![2, 3, 1]
        );
    }
}

#[test]
fn retiring_loading_iterator_does_not_restore_any_group_before_landing() {
    use cordis::{Effect, Inverse};
    let mut runtime = Runtime::new();
    let gate = Arc::new(Gate::default());
    let log = Arc::new(Mutex::new(Vec::new()));
    let wait = gate.clone();
    let output = log.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("pending-groups", move |ctx| {
                let root_log = output.clone();
                ctx.on_cleanup(move || {
                    root_log.lock().unwrap().push("root");
                    Ok(())
                });
                let gate = wait.clone();
                let log = output.clone();
                let never = output.clone();
                ctx.effect(
                    Effect::new()
                        .step(move |_| async move {
                            WaitGate(gate).await;
                            log.lock().unwrap().push("land");
                            Ok(Inverse::new(move || {
                                log.lock().unwrap().push("inverse");
                                Ok(())
                            }))
                        })
                        .step(move |_| async move {
                            never.lock().unwrap().push("wrong-next-stage");
                            Ok(Inverse::empty())
                        }),
                )?;
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    runtime.dispose(owner).unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert!(!runtime.cleanup_started(owner));
    assert!(log.lock().unwrap().is_empty());
    gate.release();
    block_on(runtime.settle()).unwrap();
    let entries = log.lock().unwrap();
    assert_eq!(entries[0], "land");
    assert_eq!(entries.len(), 3);
    assert!(entries.contains(&"inverse") && entries.contains(&"root"));
}

#[test]
fn setup_child_is_retired_at_its_owned_inverse_position() {
    let mut runtime = Runtime::new();
    let gate = Arc::new(Gate::default());
    let handle = Arc::new(Mutex::new(None));
    let output = handle.clone();
    let wait = gate.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("parent", move |ctx| {
                *output.lock().unwrap() = Some(ctx.mount(Plugin::new("child", |_| Ok(())))?);
                let gate = wait.clone();
                ctx.on_cleanup_async(move || async move {
                    WaitGate(gate).await;
                    Ok(())
                });
                Ok(())
            }),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let child = handle.lock().unwrap().as_ref().unwrap().id().unwrap();
    runtime.dispose(owner).unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert!(!runtime.retired(child));
    assert_eq!(runtime.phase(child), Some(Phase::Active));
    gate.release();
    block_on(runtime.settle()).unwrap();
    assert!(!runtime.contains(child));
    assert!(!runtime.contains(owner));
}

#[test]
fn inherited_dependency_keeps_external_provider_alive_for_child_cleanup() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<Arc<AtomicBool>>::new("inherited");
    let live = Arc::new(AtomicBool::new(true));
    let captured = live.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("external", move |ctx| {
                ctx.provide(key, captured.clone())?;
                let live = captured.clone();
                ctx.on_cleanup(move || {
                    live.store(false, Ordering::SeqCst);
                    Ok(())
                });
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let gate = Arc::new(Gate::default());
    let wait = gate.clone();
    let child_handle = Arc::new(Mutex::new(None));
    let output = child_handle.clone();
    runtime
        .mount(
            &context,
            None,
            Plugin::new("parent", move |ctx| {
                let gate = wait.clone();
                *output.lock().unwrap() = Some(ctx.mount(Plugin::new("child", move |child| {
                    let live = child.get(key)?; // inherited, without .requires(key)
                    let gate = gate.clone();
                    child.on_cleanup_async(move || async move {
                        WaitGate(gate).await;
                        assert!(live.load(Ordering::SeqCst));
                        Ok(())
                    });
                    Ok(())
                }))?);
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let child = child_handle.lock().unwrap().as_ref().unwrap().id().unwrap();
    assert_eq!(runtime.committed(child)[0].provider, provider);
    runtime.dispose(provider).unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert!(live.load(Ordering::SeqCst));
    assert!(!runtime.cleanup_started(provider));
    gate.release();
    block_on(runtime.settle()).unwrap();
    assert!(!live.load(Ordering::SeqCst));
    assert!(!runtime.contains(child));
}

#[test]
fn child_relying_on_parent_service_does_not_deadlock_owned_disposal() {
    let mut runtime = Runtime::new();
    let key = ServiceKey::<usize>::new("parent-owned");
    let parent = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("parent", move |ctx| {
                ctx.provide(key, 1)?;
                ctx.mount(
                    Plugin::new("child", move |child| {
                        assert_eq!(*child.get(key)?, 1);
                        Ok(())
                    })
                    .requires(key),
                )?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.ids().len(), 2);
    runtime.dispose(parent).unwrap();
    block_on(runtime.settle()).unwrap();
    assert!(runtime.ids().is_empty());
}

#[test]
fn panic_in_setup_poll_rolls_back_and_latches_until_explicit_restart() {
    let mut runtime = Runtime::new();
    let cleanup = Arc::new(AtomicUsize::new(0));
    let inverse = cleanup.clone();
    let calls = Arc::new(AtomicUsize::new(0));
    let count = calls.clone();
    let gate = Arc::new(Gate::default());
    let wait = gate.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new_async("panic", move |ctx| {
                let inverse = inverse.clone();
                let count = count.clone();
                let gate = wait.clone();
                async move {
                    let run = count.fetch_add(1, Ordering::SeqCst);
                    ctx.on_cleanup(move || {
                        inverse.fetch_add(1, Ordering::SeqCst);
                        Ok(())
                    })?;
                    WaitGate(gate).await;
                    if run == 0 {
                        panic!("setup poll failed");
                    }
                    Ok(())
                }
            }),
        )
        .unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    gate.release();
    assert!(
        matches!(block_on(runtime.settle()), Err(RuntimeError::Setup { message, .. }) if message.contains("setup poll failed"))
    );
    assert_eq!(cleanup.load(Ordering::SeqCst), 1);
    assert_eq!(runtime.phase(owner), Some(Phase::Inactive));
    assert!(block_on(runtime.settle()).is_err());
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    runtime.restart(owner).unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 2);
}

#[test]
fn panicking_cleanup_factory_and_poll_do_not_skip_older_inverses() {
    let mut runtime = Runtime::new();
    let hits = Arc::new(AtomicUsize::new(0));
    let count = hits.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("panic-cleanup", move |ctx| {
                let count = count.clone();
                ctx.on_cleanup(move || {
                    count.fetch_add(1, Ordering::SeqCst);
                    Ok(())
                });
                ctx.on_cleanup_async(|| async {
                    panic!("cleanup poll");
                    #[allow(unreachable_code)]
                    Ok(())
                });
                ctx.on_cleanup_async(|| -> std::future::Ready<Result<(), String>> {
                    panic!("cleanup factory")
                });
                Ok(())
            }),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    runtime.dispose(owner).unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(hits.load(Ordering::SeqCst), 1);
    let errors = runtime.take_cleanup_errors();
    assert_eq!(errors.len(), 2);
    assert!(
        matches!(&errors[0], RuntimeError::Cleanup { message, .. } if message.contains("factory"))
    );
    assert!(
        matches!(&errors[1], RuntimeError::Cleanup { message, .. } if message.contains("poll"))
    );
}

#[test]
fn stale_owned_context_cannot_register_resources_in_a_restarted_episode() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<usize>::new("version");
    let owner = runtime
        .mount(
            &context,
            None,
            Plugin::new("owner", move |ctx| {
                ctx.provide(key, 1)?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let old = runtime.owner_context(owner).unwrap();
    runtime.set(owner, key, 2).unwrap();
    assert_eq!(*runtime.get(&context, key).unwrap(), 2);
    runtime.restart(owner).unwrap();
    block_on(runtime.settle()).unwrap();
    assert!(old.on_cleanup(|| Ok(())).is_err());
    assert!(old.set(key, 3).is_err());
    assert!(old.get(key).is_err());
    assert_eq!(*runtime.get(&context, key).unwrap(), 1);
}

#[test]
fn inherited_dependency_respects_child_isolation_and_preserves_parent_guard() {
    let mut runtime = Runtime::new();
    let root = Context::new();
    let key = ServiceKey::<usize>::new("realm-dependency");
    let isolated = root.isolate(key);
    let first = runtime
        .mount(
            &root,
            None,
            Plugin::new("root-provider", move |ctx| {
                ctx.provide(key, 1)?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let second = runtime
        .mount(
            &isolated,
            None,
            Plugin::new("isolated-provider", move |ctx| {
                ctx.provide(key, 2)?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let parent = runtime
        .mount(&root, None, Plugin::new("parent", |_| Ok(())).requires(key))
        .unwrap();
    let child = runtime
        .mount(
            &isolated,
            Some(parent),
            Plugin::new("child", move |ctx| {
                assert_eq!(*ctx.get(key)?, 2);
                Ok(())
            }),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let bindings = runtime.committed(child);
    assert!(bindings.iter().any(|binding| binding.provider == first));
    assert!(bindings.iter().any(|binding| binding.provider == second));
    runtime.dispose(first).unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runtime.phase(parent), Some(Phase::Inactive));
    assert!(!runtime.contains(child));
}

#[test]
fn restart_during_pending_async_setup_finishes_old_inverse_before_new_setup() {
    let mut runtime = Runtime::new();
    let key = ServiceKey::<usize>::new("pending-version");
    let context = Context::new();
    let gate = Arc::new(Gate::default());
    let wait = gate.clone();
    let generation = Arc::new(AtomicUsize::new(0));
    let runs = generation.clone();
    let log = Arc::new(Mutex::new(Vec::new()));
    let output = log.clone();
    let owner = runtime
        .mount(
            &context,
            None,
            Plugin::new_async("restart", move |ctx| {
                let gate = wait.clone();
                let runs = runs.clone();
                let log = output.clone();
                async move {
                    let generation = runs.fetch_add(1, Ordering::SeqCst) + 1;
                    log.lock().unwrap().push(generation);
                    WaitGate(gate).await;
                    ctx.provide(key, generation)?;
                    ctx.on_cleanup(move || {
                        log.lock().unwrap().push(generation * 10);
                        Ok(())
                    })?;
                    Ok(())
                }
            })
            .provides(key),
        )
        .unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    runtime.restart(owner).unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert!(runtime.get(&context, key).is_none());
    gate.release();
    block_on(runtime.settle()).unwrap();
    assert_eq!(*log.lock().unwrap(), vec![1, 10, 2]);
    assert_eq!(*runtime.get(&context, key).unwrap(), 2);
}

#[test]
fn dynamic_effect_failure_rolls_back_owner_and_reports_join_error_once() {
    use cordis::{Effect, Inverse};
    let mut runtime = Runtime::new();
    let context = Context::new();
    let owner = runtime
        .mount(&context, None, Plugin::new("dynamic", |_| Ok(())))
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let gate = Arc::new(Gate::default());
    let wait = gate.clone();
    let cleanup = Arc::new(AtomicUsize::new(0));
    let inverse = cleanup.clone();
    let handle = runtime
        .effect(
            owner,
            Effect::new()
                .inverse(Inverse::new(move || {
                    inverse.fetch_add(1, Ordering::SeqCst);
                    Ok(())
                }))
                .step(move |_| async move {
                    WaitGate(wait).await;
                    Err("effect failed".into())
                }),
        )
        .unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert_eq!(runtime.phase(owner), Some(Phase::Active));
    gate.release();
    assert!(
        matches!(block_on(runtime.settle()), Err(RuntimeError::Setup { plugin, .. }) if plugin == owner)
    );
    assert_eq!(cleanup.load(Ordering::SeqCst), 1);
    assert_eq!(runtime.phase(owner), Some(Phase::Inactive));
    assert_eq!(block_on(handle.join()), Err("effect failed".into()));
    handle.dispose();
    handle.dispose();
    assert_eq!(cleanup.load(Ordering::SeqCst), 1);
}

#[test]
fn panicking_async_factory_restores_already_registered_inverse() {
    let mut runtime = Runtime::new();
    let count = Arc::new(AtomicUsize::new(0));
    let inverse = count.clone();
    runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new_async(
                "factory-panic",
                move |ctx| -> std::future::Ready<Result<(), String>> {
                    let inverse = inverse.clone();
                    ctx.on_cleanup(move || {
                        inverse.fetch_add(1, Ordering::SeqCst);
                        Ok(())
                    })
                    .unwrap();
                    panic!("async factory failed")
                },
            ),
        )
        .unwrap();
    assert!(
        matches!(block_on(runtime.settle()), Err(RuntimeError::Setup { message, .. }) if message.contains("factory failed"))
    );
    assert_eq!(count.load(Ordering::SeqCst), 1);
}

#[test]
fn targeted_join_finishes_even_while_unrelated_setup_is_pending() {
    let mut runtime = Runtime::new();
    let gate = Arc::new(Gate::default());
    let wait = gate.clone();
    let unrelated = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new_async("unrelated", move |_| {
                let gate = wait.clone();
                async move {
                    WaitGate(gate).await;
                    Ok(())
                }
            }),
        )
        .unwrap();
    let owner = runtime
        .mount(&Context::new(), None, Plugin::new("target", |_| Ok(())))
        .unwrap();
    block_on(runtime.join(owner)).unwrap();
    assert_eq!(runtime.phase(owner), Some(Phase::Active));
    assert_eq!(runtime.phase(unrelated), Some(Phase::Loading));
    runtime.cancel(owner).unwrap();
    runtime.cancel(owner).unwrap();
    block_on(runtime.join(owner)).unwrap();
    block_on(runtime.join(owner)).unwrap();
    assert!(!runtime.contains(owner));
    assert_eq!(runtime.phase(unrelated), Some(Phase::Loading));
    gate.release();
    block_on(runtime.settle()).unwrap();
}

#[test]
fn cooperative_abort_restarts_without_failure_and_preserves_registered_inverses() {
    let mut runtime = Runtime::new();
    let runs = Arc::new(AtomicUsize::new(0));
    let count = runs.clone();
    let restores = Arc::new(AtomicUsize::new(0));
    let inverse = restores.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new_async("cooperative", move |ctx| {
                let run = count.fetch_add(1, Ordering::SeqCst);
                let inverse = inverse.clone();
                async move {
                    ctx.on_cleanup(move || {
                        inverse.fetch_add(1, Ordering::SeqCst);
                        Ok(())
                    })?;
                    if run == 0 {
                        std::future::poll_fn(|_| {
                            if ctx.is_cancelled() {
                                Poll::Ready(Err(cordis::CANCELLED.to_owned()))
                            } else {
                                Poll::Pending
                            }
                        })
                        .await?;
                    }
                    Ok(())
                }
            }),
        )
        .unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    runtime.restart(owner).unwrap();
    block_on(runtime.settle()).unwrap();
    assert_eq!(runs.load(Ordering::SeqCst), 2);
    assert_eq!(restores.load(Ordering::SeqCst), 1);
    assert!(runtime.failure(owner).is_none());
}

#[test]
fn effect_cancellation_is_visible_inside_its_pending_stage() {
    use cordis::{Effect, Inverse};
    let mut runtime = Runtime::new();
    let owner = runtime
        .mount(&Context::new(), None, Plugin::new("owner", |_| Ok(())))
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let restores = Arc::new(AtomicUsize::new(0));
    let inverse = restores.clone();
    let handle = runtime
        .effect(
            owner,
            Effect::new().step(move |ctx| async move {
                ctx.on_cleanup(move || {
                    inverse.fetch_add(1, Ordering::SeqCst);
                    Ok(())
                })?;
                std::future::poll_fn(|_| {
                    if ctx.is_cancelled() {
                        Poll::Ready(Err::<Inverse, _>(cordis::CANCELLED.to_owned()))
                    } else {
                        Poll::Pending
                    }
                })
                .await
            }),
        )
        .unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    handle.cancel();
    block_on(runtime.settle()).unwrap();
    block_on(handle.join()).unwrap();
    assert_eq!(restores.load(Ordering::SeqCst), 1);
    assert_eq!(runtime.phase(owner), Some(Phase::Active));
    assert!(runtime.failure(owner).is_none());
}

#[test]
fn concurrent_inverse_registration_is_either_rejected_or_fully_restored() {
    let mut runtime = Runtime::new();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("registration-race", |_| Ok(())),
        )
        .unwrap();
    block_on(runtime.settle()).unwrap();
    let context = runtime.owner_context(owner).unwrap();
    let registered = Arc::new(AtomicUsize::new(0));
    let restored = Arc::new(AtomicUsize::new(0));
    let start = Arc::new(std::sync::Barrier::new(2));
    let counts = registered.clone();
    let inverses = restored.clone();
    let barrier = start.clone();
    let writer = std::thread::spawn(move || {
        // At least one registration is guaranteed before retirement; the rest
        // race the driver's closing of the episode under the same lock.
        let inverse = inverses.clone();
        context
            .on_cleanup(move || {
                inverse.fetch_add(1, Ordering::SeqCst);
                Ok(())
            })
            .unwrap();
        counts.fetch_add(1, Ordering::SeqCst);
        barrier.wait();
        for _ in 0..10_000 {
            let inverse = inverses.clone();
            if context
                .on_cleanup(move || {
                    inverse.fetch_add(1, Ordering::SeqCst);
                    Ok(())
                })
                .is_ok()
            {
                counts.fetch_add(1, Ordering::SeqCst);
            }
        }
    });
    start.wait();
    runtime.dispose(owner).unwrap();
    block_on(runtime.settle()).unwrap();
    writer.join().unwrap();
    assert_eq!(
        restored.load(Ordering::SeqCst),
        registered.load(Ordering::SeqCst)
    );
    assert!(!runtime.contains(owner));
}

struct ContextualValue {
    context: cordis::AsyncSetup,
    drops: Arc<AtomicUsize>,
    active_at_drop: Option<Arc<Mutex<Vec<bool>>>>,
}
impl Drop for ContextualValue {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
        if let Some(observed) = &self.active_at_drop {
            observed
                .lock()
                .unwrap()
                .push(self.context.ensure_active().is_ok());
        }
    }
}
fn run_bounded(action: impl FnOnce() + Send + 'static) {
    let (sender, receiver) = std::sync::mpsc::channel();
    let thread = std::thread::spawn(move || {
        action();
        sender.send(()).unwrap();
    });
    receiver
        .recv_timeout(std::time::Duration::from_secs(5))
        .expect("runtime operation deadlocked or panicked");
    thread.join().unwrap();
}

#[test]
fn closing_an_episode_releases_services_that_own_their_context() {
    run_bounded(|| {
        let mut runtime = Runtime::new();
        let key = ServiceKey::<ContextualValue>::new("context-owning service");
        let drops = Arc::new(AtomicUsize::new(0));
        let count = drops.clone();
        let owner = runtime
            .mount(
                &Context::new(),
                None,
                Plugin::new("provider", move |setup| {
                    setup.provide(
                        key,
                        ContextualValue {
                            context: setup.to_async(),
                            drops: count.clone(),
                            active_at_drop: None,
                        },
                    )?;
                    Ok(())
                })
                .provides(key),
            )
            .unwrap();
        block_on(runtime.settle()).unwrap();
        let retained_context = runtime.owner_context(owner).unwrap();
        runtime.dispose(owner).unwrap();
        block_on(runtime.settle()).unwrap();
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert!(retained_context.get(key).is_err());
    });
}

#[test]
fn replacing_a_private_service_drops_old_value_outside_the_context_lock() {
    run_bounded(|| {
        let mut runtime = Runtime::new();
        let key = ServiceKey::<ContextualValue>::new("private replacing service");
        let drops = Arc::new(AtomicUsize::new(0));
        let observed = Arc::new(Mutex::new(Vec::new()));
        let count = drops.clone();
        let phases = observed.clone();
        let owner = runtime
            .mount(
                &Context::new(),
                None,
                Plugin::new("provider", move |setup| {
                    setup.provide(
                        key,
                        ContextualValue {
                            context: setup.to_async(),
                            drops: count.clone(),
                            active_at_drop: Some(phases.clone()),
                        },
                    )?;
                    setup.set(
                        key,
                        ContextualValue {
                            context: setup.to_async(),
                            drops: count.clone(),
                            active_at_drop: Some(phases.clone()),
                        },
                    )?;
                    Ok(())
                })
                .provides(key),
            )
            .unwrap();
        block_on(runtime.settle()).unwrap();
        assert_eq!(*observed.lock().unwrap(), vec![true]);
        runtime.dispose(owner).unwrap();
        block_on(runtime.settle()).unwrap();
        assert_eq!(drops.load(Ordering::SeqCst), 2);
        assert_eq!(*observed.lock().unwrap(), vec![true, false]);
    });
}

#[test]
fn publishing_a_replacement_drops_old_value_outside_the_context_lock() {
    run_bounded(|| {
        let mut runtime = Runtime::new();
        let key = ServiceKey::<ContextualValue>::new("published replacing service");
        let drops = Arc::new(AtomicUsize::new(0));
        let observed = Arc::new(Mutex::new(Vec::new()));
        let count = drops.clone();
        let phases = observed.clone();
        let owner = runtime
            .mount(
                &Context::new(),
                None,
                Plugin::new("provider", move |setup| {
                    setup.provide(
                        key,
                        ContextualValue {
                            context: setup.to_async(),
                            drops: count.clone(),
                            active_at_drop: Some(phases.clone()),
                        },
                    )?;
                    Ok(())
                })
                .provides(key),
            )
            .unwrap();
        block_on(runtime.settle()).unwrap();
        runtime
            .set(
                owner,
                key,
                ContextualValue {
                    context: runtime.owner_context(owner).unwrap(),
                    drops: drops.clone(),
                    active_at_drop: Some(observed.clone()),
                },
            )
            .unwrap();
        assert_eq!(*observed.lock().unwrap(), vec![true]);
        runtime.dispose(owner).unwrap();
        block_on(runtime.settle()).unwrap();
        assert_eq!(drops.load(Ordering::SeqCst), 2);
        assert_eq!(*observed.lock().unwrap(), vec![true, false]);
    });
}

#[test]
fn only_committed_consumers_retain_values_until_their_cleanup_finishes() {
    run_bounded(|| {
        let mut runtime = Runtime::new();
        let context = Context::new();
        let key = ServiceKey::<ContextualValue>::new("retained dependency");
        let drops = Arc::new(AtomicUsize::new(0));
        let count = drops.clone();
        let provider = runtime
            .mount(
                &context,
                None,
                Plugin::new("provider", move |setup| {
                    setup.provide(
                        key,
                        ContextualValue {
                            context: setup.to_async(),
                            drops: count.clone(),
                            active_at_drop: None,
                        },
                    )?;
                    Ok(())
                })
                .provides(key),
            )
            .unwrap();
        block_on(runtime.settle()).unwrap();
        let unrelated = runtime
            .mount(&context, None, Plugin::new("unrelated", |_| Ok(())))
            .unwrap();
        let gate = Arc::new(Gate::default());
        let wait = gate.clone();
        let restored = Arc::new(AtomicBool::new(false));
        let did_restore = restored.clone();
        runtime
            .mount(
                &context,
                None,
                Plugin::new("consumer", move |setup| {
                    let context = setup.to_async();
                    let wait = wait.clone();
                    let restored = did_restore.clone();
                    setup.on_cleanup_async(move || async move {
                        WaitGate(wait).await;
                        assert!(context.get(key).is_ok());
                        restored.store(true, Ordering::SeqCst);
                        Ok(())
                    });
                    Ok(())
                })
                .requires(key),
            )
            .unwrap();
        block_on(runtime.settle()).unwrap();
        runtime.dispose(provider).unwrap();
        assert_eq!(poll_once(&mut runtime), Poll::Pending);
        assert_eq!(drops.load(Ordering::SeqCst), 0);
        assert!(!restored.load(Ordering::SeqCst));
        gate.release();
        block_on(runtime.settle()).unwrap();
        assert!(restored.load(Ordering::SeqCst));
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(runtime.phase(unrelated), Some(Phase::Active));
    });
}

#[test]
fn effect_wakers_may_reenter_their_handle_without_locking_deadlock() {
    run_bounded(|| {
        struct ReenterWake {
            handle: cordis::EffectHandle,
            calls: AtomicUsize,
        }
        impl Wake for ReenterWake {
            fn wake(self: Arc<Self>) {
                self.handle.finished();
                self.calls.fetch_add(1, Ordering::SeqCst);
            }
        }
        let mut runtime = Runtime::new();
        let owner = runtime
            .mount(&Context::new(), None, Plugin::new("owner", |_| Ok(())))
            .unwrap();
        block_on(runtime.settle()).unwrap();
        let gate = Arc::new(Gate::default());
        let wait = gate.clone();
        let handle = runtime
            .effect(
                owner,
                cordis::Effect::new().step(move |_| async move {
                    WaitGate(wait).await;
                    Ok(cordis::Inverse::empty())
                }),
            )
            .unwrap();
        let reenter = Arc::new(ReenterWake {
            handle: handle.clone(),
            calls: AtomicUsize::new(0),
        });
        let waker = Waker::from(reenter.clone());
        let mut context = TaskContext::from_waker(&waker);
        assert_eq!(
            Pin::new(&mut runtime.settle()).poll(&mut context),
            Poll::Pending
        );
        assert_eq!(
            Pin::new(&mut handle.join()).poll(&mut context),
            Poll::Pending
        );
        gate.release();
        assert_eq!(
            Pin::new(&mut runtime.settle()).poll(&mut context),
            Poll::Ready(Ok(()))
        );
        handle.cancel();
        assert_eq!(
            Pin::new(&mut runtime.settle()).poll(&mut context),
            Poll::Ready(Ok(()))
        );
        assert_eq!(
            Pin::new(&mut handle.join()).poll(&mut context),
            Poll::Ready(Ok(()))
        );
        assert!(reenter.calls.load(Ordering::SeqCst) >= 2);
    });
}
