//! Real cordis::Plugin definitions and explicit Node views of their original Arc slots.
use cordis::{AsyncSetup, Effect, Plugin, ServiceKey};
use cordis_node::plugin::{
    FactoryRegistry, MethodDescriptor, MethodKind, PluginContext, PluginFuture, PluginResult,
    TypedFactory, TypedService,
};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex, Weak};
use std::task::{Poll, Waker};

#[derive(Default)]
struct Gate {
    released: bool,
    waker: Option<Waker>,
}
#[derive(Default)]
struct Shared {
    events: Vec<Value>,
    counters: BTreeMap<String, Weak<Counter>>,
    gates: BTreeMap<String, Gate>,
    live_setups: BTreeMap<String, AsyncSetup>,
}
#[derive(Clone)]
struct Control(Arc<Mutex<Shared>>);
impl Control {
    fn record(&self, event: Value) {
        self.0.lock().unwrap().events.push(event);
    }
    async fn wait(&self, name: String) {
        let state = self.0.clone();
        std::future::poll_fn(move |cx| {
            let mut state = state.lock().unwrap();
            let gate = state.gates.entry(name.clone()).or_default();
            if gate.released {
                Poll::Ready(())
            } else {
                gate.waker = Some(cx.waker().clone());
                Poll::Pending
            }
        })
        .await
    }
}
struct DefinitionGuard {
    control: Control,
    label: String,
}
impl Drop for DefinitionGuard {
    fn drop(&mut self) {
        self.control
            .record(json!({"phase":"definition:drop","label":self.label}));
    }
}
struct ControlAdapter;
impl TypedService<Control> for ControlAdapter {
    fn methods(&self) -> Vec<MethodDescriptor> {
        ["events", "release", "note", "refreshOld"]
            .into_iter()
            .map(|name| MethodDescriptor {
                name: name.into(),
                kind: MethodKind::Sync,
            })
            .collect()
    }
    fn call_sync(&self, value: Arc<Control>, method: &str, args: Value) -> PluginResult<Value> {
        match method {
            "events" => Ok(json!(value.0.lock().unwrap().events)),
            "release" => {
                let name = args[0].as_str().ok_or("release requires a gate name")?;
                let wake = {
                    let mut state = value.0.lock().unwrap();
                    let gate = state.gates.entry(name.into()).or_default();
                    gate.released = true;
                    gate.waker.take()
                };
                if let Some(wake) = wake {
                    wake.wake();
                }
                Ok(Value::Null)
            }
            "refreshOld" => {
                let name = args[0].as_str().ok_or("refreshOld requires a label")?;
                let setup = value
                    .0
                    .lock()
                    .unwrap()
                    .live_setups
                    .get(name)
                    .cloned()
                    .ok_or("unknown live setup")?;
                setup.refresh()?;
                Ok(Value::Null)
            }
            "note" => {
                value.record(json!({"phase":"js:cleanup","label":args[0]}));
                Ok(Value::Null)
            }
            _ => Err("unknown typed control method".into()),
        }
    }
}
struct Counter {
    value: Mutex<i64>,
    activation: u64,
    label: String,
}
impl Counter {
    fn snapshot(&self) -> Value {
        json!({"value":*self.value.lock().unwrap(),"activation":self.activation,"label":self.label})
    }
}
struct CounterAdapter;
impl TypedService<Counter> for CounterAdapter {
    fn methods(&self) -> Vec<MethodDescriptor> {
        vec![
            MethodDescriptor {
                name: "read".into(),
                kind: MethodKind::Sync,
            },
            MethodDescriptor {
                name: "add".into(),
                kind: MethodKind::Sync,
            },
            MethodDescriptor {
                name: "readAsync".into(),
                kind: MethodKind::Async,
            },
        ]
    }
    fn call_sync(&self, value: Arc<Counter>, method: &str, args: Value) -> PluginResult<Value> {
        match method {
            "read" => Ok(value.snapshot()),
            "add" => {
                let increment = args[0].as_i64().ok_or("add requires an i64")?;
                let mut current = value.value.lock().unwrap();
                *current = current.checked_add(increment).ok_or("counter overflow")?;
                Ok(json!(*current))
            }
            _ => Err("unknown typed counter method".into()),
        }
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        value: Arc<Counter>,
        method: &str,
        _args: Value,
    ) -> PluginFuture {
        let method = method.to_owned();
        Box::pin(async move {
            if method != "readAsync" {
                return Err("unknown typed async method".into());
            }
            super::delay(1).await;
            ctx.cancellation().check()?;
            Ok(value.snapshot())
        })
    }
}
struct Consumer {
    counter: Arc<Counter>,
    same_instance: bool,
}
struct ConsumerAdapter;
impl TypedService<Consumer> for ConsumerAdapter {
    fn methods(&self) -> Vec<MethodDescriptor> {
        vec![MethodDescriptor {
            name: "read".into(),
            kind: MethodKind::Sync,
        }]
    }
    fn call_sync(&self, value: Arc<Consumer>, method: &str, _args: Value) -> PluginResult<Value> {
        if method != "read" {
            return Err("unknown typed consumer method".into());
        }
        let mut result = value.counter.snapshot();
        result["sameInstance"] = json!(value.same_instance);
        Ok(result)
    }
}
#[derive(Clone)]
struct Config {
    label: String,
    initial: i64,
    asynchronous: bool,
    fail_setup: bool,
    fail_cleanup: bool,
    cleanup_gate: bool,
    unsupported: Option<String>,
    ignore_unsupported: bool,
}
impl Config {
    fn parse(value: Value) -> PluginResult<Self> {
        if !value.is_null() && !value.is_object() {
            return Err("typed config must be an object or null".into());
        }
        Ok(Self {
            label: value["label"].as_str().unwrap_or("counter").into(),
            initial: value["initial"].as_i64().unwrap_or(7),
            asynchronous: value["asyncSetup"] == true,
            fail_setup: value["failSetup"] == true,
            fail_cleanup: value["failCleanup"] == true,
            cleanup_gate: value["asyncCleanup"] == true,
            unsupported: value["unsupported"].as_str().map(str::to_owned),
            ignore_unsupported: value["ignoreUnsupported"] == true,
        })
    }
    fn counter(&self, activation: u64) -> Counter {
        Counter {
            value: Mutex::new(self.initial),
            activation,
            label: self.label.clone(),
        }
    }
}
fn install_inverses(
    setup: &AsyncSetup,
    control: Arc<Control>,
    counter: Arc<Counter>,
    config: &Config,
) -> PluginResult<()> {
    control
        .0
        .lock()
        .unwrap()
        .counters
        .insert(counter.label.clone(), Arc::downgrade(&counter));
    control.record(
        json!({"phase":"counter:setup","label":counter.label,"activation":counter.activation}),
    );
    let earlier = control.clone();
    let label = counter.label.clone();
    setup.on_cleanup(move || {
        earlier.record(json!({"phase":"counter:earlier","label":label}));
        Ok(())
    })?;
    let fail = config.fail_cleanup;
    let gated = config.cleanup_gate;
    setup.on_cleanup_async(move || async move {
        if gated {
            control.record(json!({"phase":"counter:cleanup-wait","label":counter.label}));
            control.wait(format!("cleanup:{}",counter.label)).await;
        }
        control.record(json!({"phase":"counter:cleanup","label":counter.label,"activation":counter.activation,"value":*counter.value.lock().unwrap()}));
        if fail { Err("typed inverse failed: FnOnce cannot be replayed".into()) } else { Ok(()) }
    })
}
fn unsupported(setup: &AsyncSetup, key: ServiceKey<Counter>, config: &Config) -> PluginResult<()> {
    let result = match config.unsupported.as_deref() {
        None => return Ok(()),
        Some("publish") => setup.publish(key, config.counter(0)).map(|_| ()),
        Some("mount") => setup
            .mount(Plugin::new("forbidden-child", |_| Ok(())))
            .map(|_| ()),
        Some("effect") => setup.effect(Effect::new()).map(|_| ()),
        Some("set") => setup.set(key, config.counter(0)),
        Some("refresh") => setup.refresh(),
        Some("provide_checked") => setup
            .provide_checked(key, config.counter(0), |_, _, _| true)
            .map(|_| ()),
        Some(_) => return Err("unknown unsupported fixture operation".into()),
    };
    if config.ignore_unsupported {
        Ok(())
    } else {
        result
    }
}
fn counter_plugin(
    control_key: ServiceKey<Control>,
    counter_key: ServiceKey<Counter>,
    control: Control,
    config: Value,
) -> PluginResult<Plugin> {
    let config = Config::parse(config)?;
    let definition = DefinitionGuard {
        control,
        label: config.label.clone(),
    };
    let mut activations = 0;
    let plugin = if config.asynchronous {
        Plugin::new_async("typed-counter", move |setup| {
            let _keep_definition = &definition;
            activations += 1;
            let config = config.clone();
            let activation = activations;
            async move {
                let control = setup.get(control_key)?;
                let counter = setup.provide(counter_key, config.counter(activation))?;
                install_inverses(&setup, control.clone(), counter, &config)?;
                control.record(json!({"phase":"counter:waiting","label":config.label}));
                control.wait(format!("setup:{}", config.label)).await;
                control.record(json!({"phase":"counter:landed","label":config.label,"cancelled":setup.is_cancelled()}));
                if setup.is_cancelled() {
                    return Err("typed setup cancelled after landing".into());
                }
                unsupported(&setup, counter_key, &config)?;
                if config.fail_setup {
                    Err("typed partial setup failure".into())
                } else {
                    Ok(())
                }
            }
        })
    } else {
        Plugin::new("typed-counter", move |setup| {
            let _keep_definition = &definition;
            activations += 1;
            let control = setup.get(control_key)?;
            let counter = setup.provide(counter_key, config.counter(activations))?;
            install_inverses(&setup.to_async(), control, counter, &config)?;
            unsupported(&setup.to_async(), counter_key, &config)?;
            if config.fail_setup {
                Err("typed partial setup failure".into())
            } else {
                Ok(())
            }
        })
    };
    Ok(plugin.requires(control_key).provides(counter_key))
}
fn consumer_plugin(
    control_key: ServiceKey<Control>,
    counter_key: ServiceKey<Counter>,
    consumer_key: ServiceKey<Consumer>,
) -> Plugin {
    Plugin::new("typed-consumer", move |setup| {
        let control = setup.get(control_key)?;
        let counter = setup.get(counter_key)?;
        let same_instance = control.0.lock().unwrap().counters.get(&counter.label).and_then(Weak::upgrade).is_some_and(|original| Arc::ptr_eq(&original, &counter));
        setup.provide(consumer_key, Consumer { counter: counter.clone(), same_instance })?;
        control.record(json!({"phase":"consumer:setup","label":counter.label,"sameInstance":same_instance}));
        let old_setup = setup.to_async();
        setup.on_cleanup(move || {
            let committed = old_setup.get(counter_key)?;
            control.record(json!({"phase":"consumer:cleanup","label":counter.label,"value":*committed.value.lock().unwrap(),"sameInstance":Arc::ptr_eq(&counter,&committed)}));
            Ok(())
        });
        Ok(())
    }).requires(control_key).requires(counter_key).provides(consumer_key)
}
struct LiveValue(i64);
struct LiveControl {
    setup: AsyncSetup,
    key: ServiceKey<LiveValue>,
}
struct LiveView;
impl TypedService<LiveValue> for LiveView {
    fn methods(&self) -> Vec<MethodDescriptor> {
        vec![MethodDescriptor {
            name: "read".into(),
            kind: MethodKind::Sync,
        }]
    }
    fn call_sync(&self, value: Arc<LiveValue>, _method: &str, _args: Value) -> PluginResult<Value> {
        Ok(json!(value.0))
    }
}
struct LiveControlView;
impl TypedService<LiveControl> for LiveControlView {
    fn methods(&self) -> Vec<MethodDescriptor> {
        vec![
            MethodDescriptor {
                name: "set".into(),
                kind: MethodKind::Sync,
            },
            MethodDescriptor {
                name: "setAsync".into(),
                kind: MethodKind::Async,
            },
        ]
    }
    fn call_sync(
        &self,
        value: Arc<LiveControl>,
        _method: &str,
        args: Value,
    ) -> PluginResult<Value> {
        value.setup.set(
            value.key,
            LiveValue(args[0].as_i64().ok_or("set requires i64")?),
        )?;
        Ok(Value::Null)
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        value: Arc<LiveControl>,
        _method: &str,
        args: Value,
    ) -> PluginFuture {
        Box::pin(async move {
            super::delay(1).await;
            ctx.cancellation().check()?;
            value.setup.set(
                value.key,
                LiveValue(args[0].as_i64().ok_or("setAsync requires i64")?),
            )?;
            Ok(Value::Null)
        })
    }
}
struct LiveReader {
    setup: AsyncSetup,
    key: ServiceKey<LiveValue>,
    original: Arc<LiveValue>,
}
struct LiveReaderView;
impl TypedService<LiveReader> for LiveReaderView {
    fn methods(&self) -> Vec<MethodDescriptor> {
        vec![MethodDescriptor {
            name: "read".into(),
            kind: MethodKind::Sync,
        }]
    }
    fn call_sync(
        &self,
        value: Arc<LiveReader>,
        _method: &str,
        _args: Value,
    ) -> PluginResult<Value> {
        let current = value.setup.get(value.key)?;
        Ok(json!({"current": current.0, "original": value.original.0,
            "sameArc": Arc::ptr_eq(&current, &value.original)}))
    }
}
fn register_live(
    registry: &mut FactoryRegistry,
    control_key: ServiceKey<Control>,
) -> PluginResult<()> {
    let key = ServiceKey::<LiveValue>::new("typedLiveValue");
    let controller = ServiceKey::<LiveControl>::new("typedLiveControl");
    let reader = ServiceKey::<LiveReader>::new("typedLiveReader");
    registry.register_typed(
        TypedFactory::new("fixture.typedLive", move |config| {
            let label = config["label"].as_str().unwrap_or("live").to_owned();
            let initial = config["initial"].as_i64().unwrap_or(5);
            let fail_cleanup = config["failCleanup"] == true;
            let fail_setup = config["failSetup"] == true;
            let panic_check = config["panicCheck"] == true;
            let mut generation = 0;
            Ok(Plugin::new("live", move |setup| {
                generation += 1;
                let control = setup.get(control_key)?;
                let realm = setup.context().port(key).realm;
                setup.provide_checked(key, LiveValue(initial), move |value, context, config| {
                    assert!(!panic_check, "live predicate failure");
                    context.port(key).realm == realm
                        && value.0 >= config["minimum"].as_i64().unwrap_or(0)
                })?;
                let handle = setup.to_async();
                control
                    .0
                    .lock()
                    .unwrap()
                    .live_setups
                    .insert(format!("{label}:{generation}"), handle.clone());
                setup.provide(controller, LiveControl { setup: handle, key })?;
                let label = label.clone();
                setup.on_cleanup(move || {
                    control.record(json!({"phase":"live:cleanup","label":label}));
                    if fail_cleanup {
                        Err("live cleanup failed".into())
                    } else {
                        Ok(())
                    }
                });
                if fail_setup {
                    Err("live partial setup failed".into())
                } else {
                    Ok(())
                }
            })
            .requires(control_key)
            .provides(key)
            .provides(controller))
        })
        .requires(control_key, "typedControl")
        .provides(key, "typedLiveValue", LiveView)
        .provides(controller, "typedLiveControl", LiveControlView)
        .with_service_updates(),
    )?;
    registry.register_typed(TypedFactory::new("fixture.typedLiveReader", move |_| {
        Ok(Plugin::new("live-reader", move |setup| {
            let control = setup.get(control_key)?;
            let original = setup.get(key)?;
            let handle = setup.to_async();
            setup.provide(reader, LiveReader { setup: handle.clone(), key, original: original.clone() })?;
            setup.on_cleanup(move || {
                control.record(json!({"phase":"live-reader:cleanup", "current":handle.get(key)?.0,"original":original.0}));
                Ok(())
            });
            Ok(())
        }).requires(control_key).requires(key).provides(reader))
    }).requires(control_key,"typedControl").requires(key,"typedLiveValue").provides(reader,"typedLiveReader",LiveReaderView))?;
    Ok(())
}
pub(super) fn register(registry: &mut FactoryRegistry) -> PluginResult<()> {
    let shared = Control(Arc::new(Mutex::new(Shared::default())));
    let control_key = ServiceKey::<Control>::new("typedControl");
    let counter_key = ServiceKey::<Counter>::new("typedCounter");
    let consumer_key = ServiceKey::<Consumer>::new("typedConsumer");
    let control = shared.clone();
    registry.register_typed(
        TypedFactory::new("fixture.typedControl", move |_| {
            let control = control.clone();
            Ok(Plugin::new("typed-control", move |setup| {
                setup.provide(control_key, control.clone())?;
                Ok(())
            })
            .provides(control_key))
        })
        .provides(control_key, "typedControl", ControlAdapter),
    )?;
    registry.register_typed(
        TypedFactory::new("fixture.typedCounter", move |config| {
            counter_plugin(control_key, counter_key, shared.clone(), config)
        })
        .requires(control_key, "typedControl")
        .provides(counter_key, "typedCounter", CounterAdapter),
    )?;
    registry.register_typed(
        TypedFactory::new("fixture.typedConsumer", move |_| {
            Ok(consumer_plugin(control_key, counter_key, consumer_key))
        })
        .requires(control_key, "typedControl")
        .requires(counter_key, "typedCounter")
        .provides(consumer_key, "typedConsumer", ConsumerAdapter),
    )?;
    // Same spelling and Rust type deliberately do not grant the same ServiceKey identity.
    let wrong_counter_key = ServiceKey::<Counter>::new("typedCounter");
    registry.register_typed(
        TypedFactory::new("fixture.typedWrongKey", move |_| {
            Ok(consumer_plugin(
                control_key,
                wrong_counter_key,
                consumer_key,
            ))
        })
        .requires(control_key, "typedControl")
        .requires(wrong_counter_key, "typedCounter")
        .provides(consumer_key, "typedConsumer", ConsumerAdapter),
    )?;
    register_live(registry, control_key)
}
