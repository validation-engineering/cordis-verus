use super::*;
use std::sync::atomic::AtomicUsize;

struct RootFactory;
struct Stub;
fn descriptor(name: &str) -> FactoryDescriptor {
    FactoryDescriptor {
        name: name.into(),
        inject: vec!["js".into()],
        services: vec![ServiceDescriptor {
            name: "childService".into(),
            methods: vec![MethodDescriptor {
                name: "read".into(),
                kind: MethodKind::Async,
            }],
        }],
    }
}
impl PluginFactory for RootFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        descriptor("root")
    }
    fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Stub))
    }
}
impl PluginInstance for Stub {
    fn setup(&self, _: PluginContext) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
}
#[derive(Default)]
struct Counters {
    descriptors: AtomicUsize,
    creates: AtomicUsize,
    drops: AtomicUsize,
}
struct Factory {
    counters: Arc<Counters>,
    invalid: bool,
    panic_descriptor: bool,
    panic_drop: bool,
}
impl PluginFactory for Factory {
    fn descriptor(&self) -> FactoryDescriptor {
        self.counters.descriptors.fetch_add(1, Ordering::SeqCst);
        assert!(!self.panic_descriptor, "descriptor panic");
        descriptor(if self.invalid { "" } else { "retained" })
    }
    fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        self.counters.creates.fetch_add(1, Ordering::SeqCst);
        Ok(Arc::new(Stub))
    }
}
impl Drop for Factory {
    fn drop(&mut self) {
        self.counters.drops.fetch_add(1, Ordering::SeqCst);
        assert!(!self.panic_drop, "factory destructor panic");
    }
}
fn factory() -> (Factory, Arc<Counters>) {
    let counters = Arc::new(Counters::default());
    (
        Factory {
            counters: counters.clone(),
            invalid: false,
            panic_descriptor: false,
            panic_drop: false,
        },
        counters,
    )
}
extern "C" fn wake(_: u64) {}
fn request(runtime: &Runtime, value: Value) -> PluginResult<Value> {
    runtime.handle(
        serde_json::from_value(value).unwrap(),
        WakeV1 { token: 0, wake },
    )
}
fn create(runtime: &Runtime) -> u64 {
    let id = request(
        runtime,
        json!({"op":"create","factory":"root","config":null}),
    )
    .unwrap()["instance"]
        .as_u64()
        .unwrap();
    let setup = request(runtime, json!({"op":"setup","instance":id})).unwrap()["job"]
        .as_u64()
        .unwrap();
    assert_eq!(
        request(runtime, json!({"op":"poll","job":setup})).unwrap()["result"],
        json!({"ok":null})
    );
    request(runtime, json!({"op":"drop_job","job":setup})).unwrap();
    id
}
fn context(runtime: &Runtime, instance: u64) -> PluginContext {
    let owner = runtime.instance(instance).unwrap();
    PluginContext {
        cancellation: CancellationToken::default(),
        cleanup: false,
        children: Some(owner.children.clone()),
        calls: Some(Arc::new(CallAction::for_instance(
            &owner.descriptor.inject,
            Arc::new(HostWake(Mutex::new(None))),
            owner.children.clone(),
        ))),
    }
}
fn fixture() -> (Runtime, u64, PluginContext) {
    let runtime = Runtime::new(Module::new("children", "1").factory(RootFactory)).unwrap();
    let id = create(&runtime);
    let ctx = context(&runtime, id);
    (runtime, id, ctx)
}
fn poll<F: Future + ?Sized>(future: Pin<&mut F>) -> Poll<F::Output> {
    future.poll(&mut Context::from_waker(Waker::noop()))
}
fn ready<T>(value: Poll<PluginResult<T>>) -> T {
    match value {
        Poll::Ready(Ok(value)) => value,
        _ => panic!("expected successful completion"),
    }
}
fn error<T>(value: Poll<PluginResult<T>>) -> String {
    match value {
        Poll::Ready(Err(error)) => error,
        _ => panic!("expected failed completion"),
    }
}
fn one(ctx: &PluginContext) -> ReverseCall {
    let (mut batch, _) = ctx.calls.as_ref().unwrap().take_batch();
    assert_eq!(batch.len(), 1);
    batch.remove(0)
}
fn acknowledge(ctx: &PluginContext, id: u64, result: ReverseResult) {
    ctx.calls.as_ref().unwrap().resolve(id, result).unwrap();
}
fn remove(runtime: &Runtime, parent: u64, child: u64) {
    request(
        runtime,
        json!({"op":"child_removed","parent":parent,"child":child}),
    )
    .unwrap();
}
fn finish(runtime: &Runtime, id: u64) {
    let job = request(runtime, json!({"op":"cleanup","instance":id})).unwrap()["job"]
        .as_u64()
        .unwrap();
    assert_eq!(
        request(runtime, json!({"op":"poll","job":job})).unwrap()["result"],
        json!({"ok":null})
    );
    request(runtime, json!({"op":"drop_job","job":job})).unwrap();
    request(runtime, json!({"op":"destroy","instance":id})).unwrap();
}

#[test]
fn retained_factory_descriptor_is_cached_and_each_child_activation_is_fresh() {
    let (runtime, parent, ctx) = fixture();
    let (factory, counters) = factory();
    let mut publish = Box::pin(ctx.publish(factory, Value::Null));
    assert!(poll(publish.as_mut()).is_pending());
    let call = one(&ctx);
    let ReverseOperation::ChildPublish { definition, .. } = call.operation else {
        panic!()
    };
    for _ in 0..2 {
        let metadata = request(
            &runtime,
            json!({"op":"describe_definition","parent":parent,"definition":definition}),
        )
        .unwrap();
        assert_eq!(metadata["name"], "retained");
        let child = request(&runtime, json!({"op":"create_child","parent":parent,"target":{"kind":"retained","definition":definition},"config":null})).unwrap()["instance"].as_u64().unwrap();
        assert_eq!(
            request(
                &runtime,
                json!({"op":"drop_definition","parent":parent,"definition":definition})
            )
            .unwrap_err(),
            "DefinitionHasInstances"
        );
        request(&runtime, json!({"op":"destroy","instance":child})).unwrap();
    }
    assert_eq!(counters.descriptors.load(Ordering::SeqCst), 1);
    assert_eq!(counters.creates.load(Ordering::SeqCst), 2);
    acknowledge(&ctx, call.request, ReverseResult::Child { child: 700 });
    let _handle = ready(poll(publish.as_mut()));
    assert_eq!(
        request(
            &runtime,
            json!({"op":"drop_definition","parent":parent,"definition":definition})
        )
        .unwrap_err(),
        "DefinitionHasChild"
    );
    assert_eq!(
        request(&runtime, json!({"op":"cleanup","instance":parent})).unwrap_err(),
        "InvalidLifecycleState"
    );
    remove(&runtime, parent, 700);
    request(
        &runtime,
        json!({"op":"drop_definition","parent":parent,"definition":definition}),
    )
    .unwrap();
    assert_eq!(counters.drops.load(Ordering::SeqCst), 1);
    finish(&runtime, parent);
}

#[test]
fn handle_crosses_same_instance_actions_but_not_other_owners_or_closed_actions() {
    let (runtime, parent, ctx) = fixture();
    let other = create(&runtime);
    let mut mounting = Box::pin(ctx.mount("root", Value::Null));
    assert!(poll(mounting.as_mut()).is_pending());
    let call = one(&ctx);
    acknowledge(&ctx, call.request, ReverseResult::Child { child: 1 });
    let handle = ready(poll(mounting.as_mut()));
    ctx.calls.as_ref().unwrap().close();
    assert_eq!(
        error(poll(Box::pin(handle.status(&ctx)).as_mut())),
        "ActionClosed"
    );
    assert_eq!(
        error(poll(
            Box::pin(handle.status(&context(&runtime, other))).as_mut()
        )),
        "WrongChildOwner"
    );
    let next = context(&runtime, parent);
    let mut status = Box::pin(handle.status(&next));
    assert!(poll(status.as_mut()).is_pending());
    let call = one(&next);
    acknowledge(
        &next,
        call.request,
        ReverseResult::ChildState {
            child_state: ChildStatus {
                id: Some("12".into()),
                initialized: true,
                ..ChildStatus::default()
            },
        },
    );
    assert!(ready(poll(status.as_mut())).initialized);
    remove(&runtime, parent, 1);
    finish(&runtime, parent);
    assert_eq!(
        error(poll(Box::pin(handle.status(&next)).as_mut())),
        "ActionClosed"
    );
    finish(&runtime, other);
}

#[test]
fn early_removed_notification_and_dropped_publish_awaiters_preserve_ownership() {
    let (runtime, parent, ctx) = fixture();
    let (factory, counters) = factory();
    let mut future = Box::pin(ctx.publish(factory, Value::Null));
    assert!(poll(future.as_mut()).is_pending());
    drop(future);
    ctx.calls.as_ref().unwrap().close();
    let call = one(&ctx);
    let ReverseOperation::ChildPublish { definition, .. } = call.operation else {
        panic!()
    };
    remove(&runtime, parent, 9);
    request(
        &runtime,
        json!({"op":"drop_definition","parent":parent,"definition":definition}),
    )
    .unwrap();
    acknowledge(&ctx, call.request, ReverseResult::Child { child: 9 });
    assert!(
        runtime
            .instance(parent)
            .unwrap()
            .state
            .lock()
            .unwrap()
            .controls[&9]
            .removed
    );
    assert_eq!(ctx.calls.as_ref().unwrap().take_batch().1, 0);
    assert_eq!(counters.drops.load(Ordering::SeqCst), 1);
    finish(&runtime, parent);
}

#[test]
fn invalid_descriptor_and_queue_rejection_release_unmounted_definitions_under_owner_gate() {
    let (runtime, parent, ctx) = fixture();
    let owner = runtime.instance(parent).unwrap();
    let _gate = owner.gate.lock().unwrap();
    let (mut invalid, counters) = factory();
    invalid.invalid = true;
    assert_eq!(
        error(poll(Box::pin(ctx.publish(invalid, Value::Null)).as_mut())),
        "EmptyFactoryName"
    );
    assert_eq!(counters.drops.load(Ordering::SeqCst), 1);
    for _ in 0..MAX_PENDING_CALLS {
        let mut call = Box::pin(ctx.call("js", "wait", json!([])));
        assert!(poll(call.as_mut()).is_pending());
    }
    let (factory, counters) = factory();
    assert_eq!(
        error(poll(Box::pin(ctx.publish(factory, Value::Null)).as_mut())),
        "ReverseCallCapacity"
    );
    assert_eq!(counters.drops.load(Ordering::SeqCst), 1);
    assert!(runtime.records.lock().unwrap().definitions.is_empty());
    assert!(owner.state.lock().unwrap().definitions.is_empty());
}

#[test]
fn configuration_limits_precede_registration_and_child_admission_has_a_lifetime_budget() {
    let (runtime, parent, ctx) = fixture();
    let mut deep = Value::Null;
    for _ in 0..65 {
        deep = json!([deep]);
    }
    let (factory_value, counters) = factory();
    assert_eq!(
        error(poll(Box::pin(ctx.publish(factory_value, deep)).as_mut())),
        "ValueTooDeep"
    );
    assert_eq!(counters.descriptors.load(Ordering::SeqCst), 0);
    assert_eq!(
        runtime
            .instance(parent)
            .unwrap()
            .state
            .lock()
            .unwrap()
            .child_attempts,
        0
    );
    for _ in 0..MAX_CHILDREN {
        let (mut value, _) = factory();
        value.invalid = true;
        assert_eq!(
            error(poll(Box::pin(ctx.publish(value, Value::Null)).as_mut())),
            "EmptyFactoryName"
        );
    }
    let (value, _) = factory();
    assert_eq!(
        error(poll(Box::pin(ctx.publish(value, Value::Null)).as_mut())),
        "ChildCapacity"
    );
    assert!(runtime.records.lock().unwrap().definitions.is_empty());
    finish(&runtime, parent);
}

#[test]
fn retained_descriptor_panic_and_factory_destructor_panic_never_confirm_release() {
    for descriptor_panic in [true, false] {
        let (runtime, parent, ctx) = fixture();
        let (mut value, _) = factory();
        value.panic_descriptor = descriptor_panic;
        value.panic_drop = !descriptor_panic;
        let mut future = Box::pin(ctx.publish(value, Value::Null));
        if descriptor_panic {
            assert_eq!(error(poll(future.as_mut())), "PluginPanic");
        } else {
            assert!(poll(future.as_mut()).is_pending());
            let call = one(&ctx);
            let ReverseOperation::ChildPublish { definition, .. } = call.operation else {
                panic!()
            };
            assert_eq!(
                request(
                    &runtime,
                    json!({"op":"drop_definition","parent":parent,"definition":definition})
                )
                .unwrap_err(),
                "PluginPanic"
            );
        }
        assert_eq!(runtime.records.lock().unwrap().definitions.len(), 1);
        assert_eq!(
            runtime
                .instance(parent)
                .unwrap()
                .state
                .lock()
                .unwrap()
                .phase,
            Phase::Faulted
        );
        assert_eq!(
            request(&runtime, json!({"op":"destroy","instance":parent})).unwrap_err(),
            "InstanceHasChildren"
        );
    }
}

#[test]
fn named_child_instances_block_parent_cleanup_until_actual_instance_destruction() {
    let (runtime, parent, _) = fixture();
    let child = request(&runtime, json!({"op":"create_child","parent":parent,"target":{"kind":"module","factory":"root"},"config":null})).unwrap()["instance"].as_u64().unwrap();
    assert_eq!(
        request(&runtime, json!({"op":"cleanup","instance":parent})).unwrap_err(),
        "InvalidLifecycleState"
    );
    request(&runtime, json!({"op":"destroy","instance":child})).unwrap();
    finish(&runtime, parent);
}

#[test]
fn cleanup_cannot_admit_children_and_definition_operations_check_the_exact_parent() {
    let (runtime, parent, mut ctx) = fixture();
    let other = create(&runtime);
    ctx.cleanup = true;
    assert_eq!(
        error(poll(Box::pin(ctx.mount("root", Value::Null)).as_mut())),
        "CleanupCannotMount"
    );
    ctx.cleanup = false;
    let (factory, _) = factory();
    let mut future = Box::pin(ctx.publish(factory, Value::Null));
    assert!(poll(future.as_mut()).is_pending());
    let call = one(&ctx);
    let ReverseOperation::ChildPublish { definition, .. } = call.operation else {
        panic!()
    };
    for op in ["describe_definition", "drop_definition"] {
        assert_eq!(
            request(
                &runtime,
                json!({"op":op,"parent":other,"definition":definition})
            )
            .unwrap_err(),
            "WrongDefinitionOwner"
        );
    }
    assert_eq!(request(&runtime, json!({"op":"create_child","parent":other,"target":{"kind":"retained","definition":definition},"config":null})).unwrap_err(), "WrongDefinitionOwner");
    request(
        &runtime,
        json!({"op":"drop_definition","parent":parent,"definition":definition}),
    )
    .unwrap();
    acknowledge(
        &ctx,
        call.request,
        ReverseResult::Error {
            error: "RejectedBeforeAllocation".into(),
        },
    );
    assert_eq!(error(poll(future.as_mut())), "RejectedBeforeAllocation");
    finish(&runtime, parent);
    finish(&runtime, other);
}

#[test]
fn late_status_snapshot_preserves_actual_removed_tombstone_and_diagnostic_id() {
    let (runtime, parent, ctx) = fixture();
    let mut mounting = Box::pin(ctx.mount("root", Value::Null));
    assert!(poll(mounting.as_mut()).is_pending());
    let call = one(&ctx);
    acknowledge(&ctx, call.request, ReverseResult::Child { child: 7 });
    let handle = ready(poll(mounting.as_mut()));
    let mut status = Box::pin(handle.status(&ctx));
    assert!(poll(status.as_mut()).is_pending());
    let call = one(&ctx);
    remove(&runtime, parent, 7);
    acknowledge(
        &ctx,
        call.request,
        ReverseResult::ChildState {
            child_state: ChildStatus {
                id: Some("42".into()),
                initialized: true,
                ..ChildStatus::default()
            },
        },
    );
    let latest = ready(poll(status.as_mut()));
    assert!(latest.removed);
    assert!(!latest.initialized);
    assert_eq!(latest.id.as_deref(), Some("42"));
    assert!(
        runtime
            .instance(parent)
            .unwrap()
            .state
            .lock()
            .unwrap()
            .controls[&7]
            .removed
    );
    finish(&runtime, parent);
}
