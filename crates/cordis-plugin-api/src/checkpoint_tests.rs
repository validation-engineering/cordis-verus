use super::*;
use std::sync::atomic::AtomicUsize;

struct Factory {
    schema: CheckpointSchema,
    schema_reads: Arc<AtomicUsize>,
}
struct Instance {
    config: Value,
    captures: AtomicUsize,
    cleanups: AtomicUsize,
    value: Mutex<Value>,
}
fn schema() -> CheckpointSchema {
    CheckpointSchema {
        schema: "test.counter".into(),
        version: 2,
        accepts: vec![1],
    }
}
impl PluginFactory for Factory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "counter".into(),
            inject: vec![],
            services: vec![ServiceDescriptor {
                name: "counter".into(),
                methods: vec![MethodDescriptor {
                    name: "read".into(),
                    kind: MethodKind::Sync,
                }],
            }],
        }
    }
    fn checkpoint_schema(&self) -> Option<CheckpointSchema> {
        self.schema_reads.fetch_add(1, Ordering::SeqCst);
        Some(self.schema.clone())
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Instance {
            value: Mutex::new(config.get("data").cloned().unwrap_or(json!(7))),
            config,
            captures: AtomicUsize::new(0),
            cleanups: AtomicUsize::new(0),
        }))
    }
}
impl PluginInstance for Instance {
    fn checkpoint(&self) -> PluginResult<Value> {
        assert!(self.config["capturePanic"] != true, "capture panic");
        let count = self.captures.fetch_add(1, Ordering::SeqCst);
        if self.config["captureOnce"] == true && count == 0 {
            return Err("CaptureFailed".into());
        }
        if self.config["countCaptures"] == true {
            return Ok(json!(count));
        }
        Ok(self.value.lock().unwrap().clone())
    }
    fn restore(&self, checkpoint: Checkpoint) -> PluginResult<()> {
        assert!(self.config["restorePanic"] != true, "restore panic");
        *self.value.lock().unwrap() = checkpoint.data;
        if self.config["restoreFail"] == true {
            Err("RestoreFailed".into())
        } else {
            Ok(())
        }
    }
    fn setup(&self, _: PluginContext) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
    fn cleanup(&self, _: PluginContext) -> PluginFuture {
        let fail =
            self.cleanups.fetch_add(1, Ordering::SeqCst) == 0 && self.config["cleanupOnce"] == true;
        Box::pin(async move {
            if fail {
                Err("CleanupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn call_sync(&self, _: &str, _: &str, _: Value) -> PluginResult<Value> {
        Ok(self.value.lock().unwrap().clone())
    }
}
fn runtime() -> Runtime {
    Runtime::new(Module::new("test", "2").factory(Factory {
        schema: schema(),
        schema_reads: Arc::new(AtomicUsize::new(0)),
    }))
    .unwrap()
}
extern "C" fn wake(_: u64) {}
fn request(runtime: &Runtime, value: Value) -> PluginResult<Value> {
    runtime.handle(
        serde_json::from_value(value).unwrap(),
        WakeV1 { token: 1, wake },
    )
}
fn create(runtime: &Runtime, config: Value) -> u64 {
    request(
        runtime,
        json!({"op":"create","factory":"counter","config":config}),
    )
    .unwrap()["instance"]
        .as_u64()
        .unwrap()
}
fn run(runtime: &Runtime, instance: u64, op: &str) -> Value {
    let job = request(runtime, json!({"op":op,"instance":instance})).unwrap()["job"]
        .as_u64()
        .unwrap();
    let result = request(runtime, json!({"op":"poll","job":job})).unwrap();
    request(runtime, json!({"op":"drop_job","job":job})).unwrap();
    result["result"].clone()
}
fn active(runtime: &Runtime, config: Value) -> u64 {
    let instance = create(runtime, config);
    assert_eq!(run(runtime, instance, "setup"), json!({"ok":null}));
    instance
}
fn capture(runtime: &Runtime, instance: u64) -> PluginResult<Value> {
    request(runtime, json!({"op":"checkpoint","instance":instance}))
}
fn restore(runtime: &Runtime, instance: u64, checkpoint: Value) -> PluginResult<Value> {
    request(
        runtime,
        json!({"op":"restore","instance":instance,"checkpoint":checkpoint}),
    )
}
fn snapshot(data: Value) -> Value {
    json!({"schema":"test.counter","version":1,"data":data})
}
fn clean(runtime: &Runtime, instance: u64) {
    assert_eq!(run(runtime, instance, "cleanup"), json!({"ok":null}));
    request(runtime, json!({"op":"destroy","instance":instance})).unwrap();
}
#[test]
fn schema_is_validated_and_cached_once_current_version_is_implicitly_accepted() {
    let reads = Arc::new(AtomicUsize::new(0));
    let runtime = Runtime::new(Module::new("test", "2").factory(Factory {
        schema: schema(),
        schema_reads: reads.clone(),
    }))
    .unwrap();
    let instance = active(&runtime, Value::Null);
    let checkpoint = capture(&runtime, instance).unwrap();
    assert_eq!(checkpoint["version"], 2);
    assert!(schema().accepts(&serde_json::from_value(checkpoint).unwrap()));
    assert_eq!(reads.load(Ordering::SeqCst), 1);
    for invalid in [
        CheckpointSchema {
            schema: String::new(),
            ..schema()
        },
        CheckpointSchema {
            version: 0,
            ..schema()
        },
        CheckpointSchema {
            accepts: vec![1, 1],
            ..schema()
        },
        CheckpointSchema {
            accepts: vec![0],
            ..schema()
        },
    ] {
        assert_eq!(invalid.validate().unwrap_err(), "InvalidCheckpointSchema");
    }
    CheckpointSchema {
        accepts: vec![],
        ..schema()
    }
    .validate()
    .unwrap();
    clean(&runtime, instance);
}
#[test]
fn capture_requires_actual_drain_and_freezes_business_until_cleanup() {
    let runtime = runtime();
    let instance = create(&runtime, Value::Null);
    assert_eq!(
        capture(&runtime, instance).unwrap_err(),
        "InvalidLifecycleState"
    );
    let job = request(&runtime, json!({"op":"setup","instance":instance})).unwrap()["job"]
        .as_u64()
        .unwrap();
    request(&runtime, json!({"op":"poll","job":job})).unwrap();
    assert_eq!(
        capture(&runtime, instance).unwrap_err(),
        "CheckpointNotDrained"
    );
    request(&runtime, json!({"op":"drop_job","job":job})).unwrap();
    let entry = runtime.instance(instance).unwrap();
    for kind in 0..3 {
        {
            let mut state = entry.state.lock().unwrap();
            match kind {
                0 => {
                    state.resources.insert(99);
                }
                1 => {
                    state.child_instances.insert(99);
                }
                _ => {
                    state.definitions.insert(99);
                }
            }
        }
        assert_eq!(
            capture(&runtime, instance).unwrap_err(),
            "CheckpointNotDrained"
        );
        let mut state = entry.state.lock().unwrap();
        state.resources.clear();
        state.child_instances.clear();
        state.definitions.clear();
    }
    capture(&runtime, instance).unwrap();
    assert_eq!(request(&runtime,json!({"op":"call_sync","instance":instance,"service":"counter","method":"read","args":[]})).unwrap_err(),"InstanceNotActive");
    assert_eq!(
        request(&runtime, json!({"op":"destroy","instance":instance})).unwrap_err(),
        "InstanceNotCleaned"
    );
    clean(&runtime, instance);
}
#[test]
fn failed_capture_retries_but_success_is_cached_across_cleanup_failure() {
    let runtime = runtime();
    let instance = active(
        &runtime,
        json!({"captureOnce":true,"countCaptures":true,"cleanupOnce":true}),
    );
    assert_eq!(capture(&runtime, instance).unwrap_err(), "CaptureFailed");
    assert_eq!(capture(&runtime, instance).unwrap()["data"], 1);
    assert_eq!(capture(&runtime, instance).unwrap()["data"], 1);
    assert_eq!(
        run(&runtime, instance, "cleanup"),
        json!({"error":"CleanupFailed"})
    );
    assert_eq!(
        runtime
            .instance(instance)
            .unwrap()
            .state
            .lock()
            .unwrap()
            .checkpoint
            .as_ref()
            .unwrap()
            .data,
        1
    );
    clean(&runtime, instance);
}
#[test]
fn restore_accepts_old_version_once_before_setup_and_preserves_new_instance_state() {
    let runtime = runtime();
    let instance = create(&runtime, Value::Null);
    restore(&runtime, instance, snapshot(json!(42))).unwrap();
    assert_eq!(
        restore(&runtime, instance, snapshot(json!(2))).unwrap_err(),
        "InvalidLifecycleState"
    );
    run(&runtime, instance, "setup");
    assert_eq!(capture(&runtime, instance).unwrap()["data"], 42);
    clean(&runtime, instance);
}
#[test]
fn restore_hook_or_validation_failure_permits_only_real_cleanup_and_fresh_retry() {
    for (config, checkpoint, error) in [
        (
            json!({"restoreFail":true,"cleanupOnce":true}),
            snapshot(json!(99)),
            "RestoreFailed",
        ),
        (
            Value::Null,
            json!({"schema":"other","version":1,"data":null}),
            "CheckpointSchemaMismatch",
        ),
        (
            Value::Null,
            json!({"schema":"test.counter","version":3,"data":null}),
            "CheckpointSchemaMismatch",
        ),
    ] {
        let runtime = runtime();
        let instance = create(&runtime, config.clone());
        assert_eq!(restore(&runtime, instance, checkpoint).unwrap_err(), error);
        assert_eq!(
            request(&runtime, json!({"op":"setup","instance":instance})).unwrap_err(),
            "InvalidLifecycleState"
        );
        assert_eq!(
            request(&runtime, json!({"op":"destroy","instance":instance})).unwrap_err(),
            "InstanceNotCleaned"
        );
        if config["cleanupOnce"] == true {
            assert_eq!(
                run(&runtime, instance, "cleanup"),
                json!({"error":"CleanupFailed"})
            );
        }
        clean(&runtime, instance);
    }
}
#[test]
fn native_children_are_not_automatically_checkpointed() {
    let runtime = runtime();
    let parent = active(&runtime, Value::Null);
    let child=request(&runtime,json!({"op":"create_child","parent":parent,"target":{"kind":"module","factory":"counter"},"config":null})).unwrap()["instance"].as_u64().unwrap();
    run(&runtime, child, "setup");
    assert_eq!(
        capture(&runtime, child).unwrap_err(),
        "CheckpointRequiresModuleRoot"
    );
    clean(&runtime, child);
    clean(&runtime, parent);
}
#[test]
fn checkpoint_and_restore_panic_retain_faulted_instance() {
    for capture_panic in [true, false] {
        let runtime = runtime();
        let instance = create(
            &runtime,
            json!({"capturePanic":capture_panic,"restorePanic":!capture_panic}),
        );
        let error = if capture_panic {
            run(&runtime, instance, "setup");
            capture(&runtime, instance)
        } else {
            restore(&runtime, instance, snapshot(Value::Null))
        };
        assert_eq!(error.unwrap_err(), "PluginPanic");
        assert_eq!(
            runtime
                .instance(instance)
                .unwrap()
                .state
                .lock()
                .unwrap()
                .phase,
            Phase::Faulted
        );
        assert!(request(&runtime, json!({"op":"destroy","instance":instance})).is_err());
    }
}
unsafe extern "C" fn output(context: *mut c_void, bytes: *const u8, length: usize) {
    // SAFETY: wire passes this live Vec and invokes only while bytes are borrowed.
    unsafe {
        (&mut *context.cast::<Vec<u8>>())
            .extend_from_slice(std::slice::from_raw_parts(bytes, length));
    }
}
fn wire(runtime: &OnceLock<PluginResult<Runtime>>, request: Value) -> Value {
    let request = serde_json::to_vec(&request).unwrap();
    let mut bytes = Vec::<u8>::new();
    // SAFETY: input and output live throughout this synchronous invocation.
    let status = unsafe {
        invoke_export(
            runtime,
            || unreachable!(),
            request.as_ptr(),
            request.len(),
            output,
            (&mut bytes as *mut Vec<u8>).cast(),
            WakeV1 { token: 1, wake },
        )
    };
    assert_eq!(status, STATUS_OK);
    assert!(bytes.len() <= MAX_MESSAGE_BYTES);
    serde_json::from_slice(&bytes).unwrap()
}
#[test]
fn checkpoint_payload_limits_reserve_envelope_and_failures_remain_retryable() {
    let runtime = OnceLock::from(Ok(runtime()));
    let runtime_ref = runtime.get().unwrap().as_ref().unwrap();
    let mut depth64 = Value::Null;
    for _ in 0..64 {
        depth64 = json!([depth64]);
    }
    for data in [
        Value::String("x".repeat(MAX_MESSAGE_BYTES / 2 - 2)),
        depth64.clone(),
    ] {
        let instance = active(runtime_ref, json!({"data":data}));
        let reply = wire(&runtime, json!({"op":"checkpoint","instance":instance}));
        assert_eq!(reply["ok"]["data"], data);
        let target = create(runtime_ref, Value::Null);
        assert_eq!(
            wire(
                &runtime,
                json!({"op":"restore","instance":target,"checkpoint":reply["ok"]})
            ),
            json!({"ok":null})
        );
        run(runtime_ref, target, "setup");
        clean(runtime_ref, target);
        clean(runtime_ref, instance);
    }
    for (data, error) in [
        (
            Value::String("x".repeat(MAX_MESSAGE_BYTES / 2)),
            "ResultTooLarge",
        ),
        (json!([depth64]), "ValueTooDeep"),
    ] {
        let instance = active(runtime_ref, json!({"data":data}));
        assert_eq!(
            wire(&runtime, json!({"op":"checkpoint","instance":instance}))["error"],
            error
        );
        assert_eq!(
            runtime_ref
                .instance(instance)
                .unwrap()
                .state
                .lock()
                .unwrap()
                .phase,
            Phase::Active
        );
        clean(runtime_ref, instance);
        let target = create(runtime_ref, Value::Null);
        assert_eq!(
            wire(
                &runtime,
                json!({"op":"restore","instance":target,"checkpoint":snapshot(data)})
            )["error"],
            error
        );
        clean(runtime_ref, target);
    }
}
