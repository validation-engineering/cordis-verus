//! End-to-end composition of local model factories, agent sessions, isolated
//! tenant contexts, event dispatch, timers and transactional revisions. No model
//! network endpoint is involved: `Model` represents a checked local resource.
use cordis::config::{Field, Schema};
use cordis::events::{AsyncEvent, EventScope};
use cordis::loader::{ConfigTree, Entry, FactoryRegistry, Loader, LoaderError};
use cordis::timer::{ManualClock, TimerService};
use cordis::{Context, Effect, Inverse, Phase, Plugin, ServiceKey};
use serde_json::json;
use std::future::{poll_fn, Future};
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Wake, Waker};
use std::time::Duration;

struct WakeThread(std::thread::Thread);
impl Wake for WakeThread {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.0.unpark();
    }
}
fn poll<F: Future>(future: Pin<&mut F>) -> Poll<F::Output> {
    let waker = Waker::from(Arc::new(WakeThread(std::thread::current())));
    future.poll(&mut TaskContext::from_waker(&waker))
}
fn run<F: Future>(future: F) -> F::Output {
    let mut future = std::pin::pin!(future);
    for _ in 0..10_000 {
        if let Poll::Ready(result) = poll(future.as_mut()) {
            return result;
        }
        std::thread::yield_now();
    }
    panic!("composition did not settle within its cooperative polling budget");
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
    async fn wait(&self) {
        poll_fn(|cx| {
            *self.waker.lock().unwrap() = Some(cx.waker().clone());
            if self.open.load(Ordering::SeqCst) {
                Poll::Ready(())
            } else {
                Poll::Pending
            }
        })
        .await
    }
}
async fn yield_once() {
    let mut yielded = false;
    poll_fn(|cx| {
        if yielded {
            Poll::Ready(())
        } else {
            yielded = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    })
    .await
}
struct Model {
    version: u64,
    alive: AtomicBool,
}
#[derive(Clone, Debug)]
struct Record {
    tenant: String,
    version: u64,
    owner: usize,
    action: &'static str,
}
type Trace = Arc<Mutex<Vec<Record>>>;
fn record(trace: &Trace, tenant: &str, model: &Model, owner: usize, action: &'static str) {
    trace.lock().unwrap().push(Record {
        tenant: tenant.into(),
        version: model.version,
        owner,
        action,
    });
}
struct Harness {
    loader: Loader,
    model: ServiceKey<Model>,
    requests: AsyncEvent<String, Option<String>>,
    trace: Trace,
    clocks: Arc<Mutex<Vec<(String, u64, ManualClock)>>>,
    initialize: Arc<Gate>,
    restore: Arc<Gate>,
}
impl Harness {
    fn new() -> Self {
        let model = ServiceKey::<Model>::new("model");
        let requests = AsyncEvent::<String, Option<String>>::new();
        let trace = Trace::default();
        let clocks = Arc::new(Mutex::new(Vec::new()));
        let initialize = Arc::new(Gate::default());
        let restore = Arc::new(Gate::default());
        let mut registry = FactoryRegistry::new();
        registry.register_service("model", model);
        let output = trace.clone();
        let init = initialize.clone();
        registry.register(
            "model",
            Schema::object([("version", Field::required(Schema::integer(1, 100)))]),
            move |config, scope| {
                let version = config["version"].as_u64().unwrap();
                let tenant = scope
                    .json_metadata("tenant")
                    .unwrap()
                    .as_str()
                    .unwrap()
                    .to_owned();
                let output = output.clone();
                let init = init.clone();
                Ok(Plugin::new_async("model-provider", move |ctx| {
                    let tenant = tenant.clone();
                    let output = output.clone();
                    let init = init.clone();
                    async move {
                        let model = ctx.provide(
                            model,
                            Model {
                                version,
                                alive: AtomicBool::new(true),
                            },
                        )?;
                        record(&output, &tenant, &model, ctx.owner(), "model-initialize");
                        let cleanup_model = model.clone();
                        let cleanup_trace = output.clone();
                        let cleanup_tenant = tenant.clone();
                        let owner = ctx.owner();
                        ctx.on_cleanup(move || {
                            assert!(cleanup_model.alive.swap(false, Ordering::SeqCst));
                            record(
                                &cleanup_trace,
                                &cleanup_tenant,
                                &cleanup_model,
                                owner,
                                "model-stop",
                            );
                            Ok(())
                        })?;
                        if tenant == "alpha" && version == 1 {
                            init.wait().await;
                        }
                        yield_once().await;
                        if version == 13 {
                            return Err("model weights validation failed".into());
                        }
                        Ok(())
                    }
                })
                .provides(model))
            },
        );
        let output = trace.clone();
        let events = requests.clone();
        let recorded_clocks = clocks.clone();
        let restore_gate = restore.clone();
        registry.register("agent", Schema::Any, move |_, scope| {
            let tenant = scope
                .json_metadata("tenant")
                .unwrap()
                .as_str()
                .unwrap()
                .to_owned();
            let output = output.clone();
            let events = events.clone();
            let clocks = recorded_clocks.clone();
            let restore = restore_gate.clone();
            Ok(Plugin::new_async("agent", move |ctx| {
                let tenant = tenant.clone();
                let output = output.clone();
                let events = events.clone();
                let clocks = clocks.clone();
                let restore = restore.clone();
                async move {
                    let bound = ctx.get(model)?;
                    assert!(bound.alive.load(Ordering::SeqCst));
                    yield_once().await;
                    record(&output, &tenant, &bound, ctx.owner(), "agent-start");
                    let effect_model = bound.clone();
                    let effect_trace = output.clone();
                    let effect_tenant = tenant.clone();
                    let owner = ctx.owner();
                    ctx.effect(Effect::new().step(move |_| async move {
                        yield_once().await;
                        Ok(Inverse::new_async(move || async move {
                            assert!(effect_model.alive.load(Ordering::SeqCst));
                            record(
                                &effect_trace,
                                &effect_tenant,
                                &effect_model,
                                owner,
                                "agent-cleanup-start",
                            );
                            if effect_tenant == "alpha" && effect_model.version == 1 {
                                restore.wait().await;
                            }
                            // This is deliberately the old committed model, even
                            // while the configuration requests a newer version.
                            assert!(effect_model.alive.load(Ordering::SeqCst));
                            record(
                                &effect_trace,
                                &effect_tenant,
                                &effect_model,
                                owner,
                                "agent-cleanup-finish",
                            );
                            Ok(())
                        }))
                    }))?;
                    let (timer, clock) = TimerService::manual();
                    timer.bind_async(&ctx)?;
                    clocks
                        .lock()
                        .unwrap()
                        .push((tenant.clone(), bound.version, clock));
                    let timer_model = bound.clone();
                    let timer_trace = output.clone();
                    let timer_tenant = tenant.clone();
                    timer
                        .interval(Duration::from_secs(1), move || {
                            assert!(timer_model.alive.load(Ordering::SeqCst));
                            record(
                                &timer_trace,
                                &timer_tenant,
                                &timer_model,
                                owner,
                                "timer-tick",
                            );
                        })
                        .map_err(|error| error.to_string())?;
                    let event_model = bound.clone();
                    let event_tenant = tenant.clone();
                    let listener = events.on(
                        EventScope::Relevant(ctx.context().port(model)),
                        move |request| {
                            let model = event_model.clone();
                            let tenant = event_tenant.clone();
                            async move {
                                yield_once().await;
                                assert!(model.alive.load(Ordering::SeqCst));
                                Ok(Some(format!("{tenant}/v{}:{request}", model.version)))
                            }
                        },
                    );
                    ctx.on_cleanup(move || {
                        listener.dispose();
                        Ok(())
                    })?;
                    let child_trace = output.clone();
                    let child_tenant = tenant.clone();
                    ctx.mount(Plugin::new("session-child", move |child| {
                        // Real dependency inheritance protects this scope child.
                        let model = child.get(model)?;
                        record(
                            &child_trace,
                            &child_tenant,
                            &model,
                            child.owner(),
                            "child-start",
                        );
                        let trace = child_trace.clone();
                        let tenant = child_tenant.clone();
                        let id = child.owner();
                        child.on_cleanup_async(move || async move {
                            yield_once().await;
                            assert!(model.alive.load(Ordering::SeqCst));
                            record(&trace, &tenant, &model, id, "child-stop");
                            Ok(())
                        });
                        Ok(())
                    }))?;
                    Ok(())
                }
            }))
        });
        Self {
            loader: Loader::new(Context::new(), registry),
            model,
            requests,
            trace,
            clocks,
            initialize,
            restore,
        }
    }
    fn context(&self, tenant: &str) -> Context {
        self.loader.scope(tenant).unwrap().context().clone()
    }
    fn request(&self, tenant: &str) -> String {
        run(self.requests.serial(
            EventScope::Relevant(self.context(tenant).port(self.model)),
            Arc::new("hello".into()),
        ))
        .unwrap()
        .unwrap()
    }
    fn child(&self, tenant: &str, version: u64) -> usize {
        self.trace
            .lock()
            .unwrap()
            .iter()
            .rev()
            .find(|record| {
                record.tenant == tenant
                    && record.version == version
                    && record.action == "child-start"
            })
            .unwrap()
            .owner
    }
    fn clock(&self, tenant: &str, version: u64) -> ManualClock {
        self.clocks
            .lock()
            .unwrap()
            .iter()
            .rev()
            .find(|(scope, revision, _)| scope == tenant && *revision == version)
            .unwrap()
            .2
            .clone()
    }
}
fn tree(alpha_version: u64) -> ConfigTree {
    ConfigTree {
        entries: [("alpha", alpha_version), ("beta", 99)]
            .into_iter()
            .map(|(tenant, version)| {
                let mut agent = Entry::plugin("agent", "agent", json!({}));
                agent.inject.push("model".into());
                let mut scope = Entry::group(
                    tenant,
                    vec![
                        Entry::plugin("model", "model", json!({"version": version})),
                        agent,
                    ],
                );
                scope.isolate.push("model".into());
                scope.metadata.insert("tenant".into(), json!(tenant));
                scope
            })
            .collect(),
    }
}
fn assert_consumer_finished_before_provider(trace: &Trace, tenant: &str, version: u64) {
    let records = trace.lock().unwrap();
    let position = |action| {
        records
            .iter()
            .position(|entry| {
                entry.tenant == tenant && entry.version == version && entry.action == action
            })
            .unwrap()
    };
    assert!(position("agent-cleanup-finish") < position("model-stop"));
    assert!(position("child-stop") < position("model-stop"));
}

#[test]
fn provider_revision_preserves_old_model_through_async_agent_cleanup_and_rebuilds_child() {
    let mut harness = Harness::new();
    let mut first = Box::pin(harness.loader.apply(tree(1)));
    assert!(
        poll(first.as_mut()).is_pending(),
        "real async model initialization must block publication"
    );
    harness.initialize.release();
    run(first).unwrap();
    assert_eq!(harness.request("alpha"), "alpha/v1:hello");
    assert_eq!(harness.request("beta"), "beta/v99:hello");
    assert!(harness
        .loader
        .runtime()
        .get(&Context::new(), harness.model)
        .is_none());
    let alpha_context = harness.context("alpha");
    let beta_context = harness.context("beta");
    assert_ne!(
        alpha_context.port(harness.model),
        beta_context.port(harness.model)
    );
    let old_model = harness
        .loader
        .runtime()
        .get(&alpha_context, harness.model)
        .unwrap();
    let old_provider = harness.loader.id("alpha/model").unwrap();
    let agent = harness.loader.id("alpha/agent").unwrap();
    let old_child = harness.child("alpha", 1);
    let beta_child = harness.child("beta", 99);
    let beta_provider = harness.loader.id("beta/model");
    let old_clock = harness.clock("alpha", 1);
    assert_eq!(old_clock.advance(Duration::from_secs(1)), 1);

    let mut revision = Box::pin(harness.loader.apply(tree(2)));
    assert!(poll(revision.as_mut()).is_pending());
    assert!(old_model.alive.load(Ordering::SeqCst));
    assert!(harness
        .trace
        .lock()
        .unwrap()
        .iter()
        .any(|entry| entry.tenant == "alpha" && entry.action == "agent-cleanup-start"));
    assert!(!harness
        .trace
        .lock()
        .unwrap()
        .iter()
        .any(|entry| entry.tenant == "alpha" && entry.action == "model-stop"));
    assert_eq!(
        old_clock.advance(Duration::from_secs(5)),
        0,
        "owner timer stopped while another effect inverse waits"
    );
    harness.restore.release();
    run(revision).unwrap();

    assert_eq!(harness.loader.id("alpha/agent"), Some(agent));
    assert!(harness.loader.id("alpha/model").unwrap() > old_provider);
    assert!(harness.child("alpha", 2) > old_child);
    assert!(!harness.loader.runtime().contains(old_child));
    assert_eq!(harness.loader.id("beta/model"), beta_provider);
    assert_eq!(harness.child("beta", 99), beta_child);
    assert!(!old_model.alive.load(Ordering::SeqCst));
    assert_eq!(harness.request("alpha"), "alpha/v2:hello");
    assert_eq!(harness.request("beta"), "beta/v99:hello");
    assert_eq!(harness.requests.listener_count(), 2);
    assert_eq!(harness.clock("alpha", 2).advance(Duration::from_secs(1)), 1);
    assert_consumer_finished_before_provider(&harness.trace, "alpha", 1);
    run(harness.loader.dispose()).unwrap();
    assert_eq!(harness.requests.listener_count(), 0);
    assert!(harness.loader.runtime().ids().is_empty());
}

#[test]
fn failed_model_revision_rolls_back_usable_agents_events_children_and_owner_timers() {
    let mut harness = Harness::new();
    harness.initialize.release();
    harness.restore.release();
    run(harness.loader.apply(tree(1))).unwrap();
    let old_provider = harness.loader.id("alpha/model").unwrap();
    let old_child = harness.child("alpha", 1);
    let beta_provider = harness.loader.id("beta/model");
    let beta_child = harness.child("beta", 99);
    let old_clock = harness.clock("alpha", 1);
    let result = run(harness.loader.apply(tree(13)));
    assert!(matches!(
        result,
        Err(LoaderError::Apply { rollback: None, .. })
    ));
    assert_eq!(harness.loader.tree(), &tree(1));
    assert!(!harness.loader.recovery_pending());
    assert_eq!(harness.request("alpha"), "alpha/v1:hello");
    assert_eq!(harness.request("beta"), "beta/v99:hello");
    assert!(harness.loader.id("alpha/model").unwrap() > old_provider);
    assert!(harness.child("alpha", 1) > old_child);
    assert!(!harness.loader.runtime().contains(old_child));
    assert_eq!(harness.loader.id("beta/model"), beta_provider);
    assert_eq!(harness.child("beta", 99), beta_child);
    assert_eq!(harness.requests.listener_count(), 2);
    assert_eq!(old_clock.advance(Duration::from_secs(10)), 0);
    assert_eq!(harness.clock("alpha", 1).advance(Duration::from_secs(1)), 1);
    assert!(harness
        .loader
        .runtime()
        .ids()
        .iter()
        .all(|id| harness.loader.runtime().phase(*id) == Some(Phase::Active)));
    assert!(harness
        .trace
        .lock()
        .unwrap()
        .iter()
        .any(|entry| entry.version == 13 && entry.action == "model-stop"));
    assert!(!harness
        .trace
        .lock()
        .unwrap()
        .iter()
        .any(|entry| entry.version == 13 && entry.action == "agent-start"));
    assert_consumer_finished_before_provider(&harness.trace, "alpha", 1);
    // The restored composition accepts a subsequent successful transaction.
    run(harness.loader.apply(tree(2))).unwrap();
    assert_eq!(harness.request("alpha"), "alpha/v2:hello");
    run(harness.loader.dispose()).unwrap();
    assert_eq!(harness.requests.listener_count(), 0);
    assert!(harness.loader.runtime().ids().is_empty());
}
