use super::*;
use std::sync::atomic::AtomicUsize;

struct Factory;
struct Instance {
    config: Value,
    attempts: AtomicUsize,
}
impl PluginFactory for Factory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "test".into(),
            inject: vec![],
            services: vec![ServiceDescriptor {
                name: "service".into(),
                methods: vec![
                    MethodDescriptor {
                        name: "sync".into(),
                        kind: MethodKind::Sync,
                    },
                    MethodDescriptor {
                        name: "async".into(),
                        kind: MethodKind::Async,
                    },
                ],
            }],
        }
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Instance {
            config,
            attempts: AtomicUsize::new(0),
        }))
    }
}
impl PluginInstance for Instance {
    fn setup(&self, _ctx: PluginContext) -> PluginFuture {
        if self.config["constructor_panic"].as_bool().unwrap_or(false) {
            panic!("construction panic");
        }
        if self.config["drop_panic"].as_bool().unwrap_or(false) {
            return Box::pin(PanicDrop);
        }
        let failure = self.config["setup_failure"].as_bool().unwrap_or(false);
        let panic = self.config["setup_panic"].as_bool().unwrap_or(false);
        Box::pin(async move {
            assert!(!panic, "fixture panic");
            if failure {
                Err("SetupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn cleanup(&self, _ctx: PluginContext) -> PluginFuture {
        let fail = self.config["cleanup_failure"].as_bool().unwrap_or(false)
            && self.attempts.fetch_add(1, Ordering::SeqCst) == 0;
        Box::pin(async move {
            if fail {
                Err("CleanupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn call_sync(&self, _service: &str, _method: &str, args: Value) -> PluginResult<Value> {
        Ok(args)
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        _service: &str,
        _method: &str,
        args: Value,
    ) -> PluginFuture {
        if let Some(depth) = args.get("nestedDepth").and_then(Value::as_u64) {
            return Box::pin(async move { Ok(nested_value(depth as usize)) });
        }
        if let Some(value) = args.get("echo").cloned() {
            return Box::pin(async move { Ok(value) });
        }
        Box::pin(async move {
            ctx.cancelled().await;
            Err("Cancelled".into())
        })
    }
}
fn module() -> Module {
    Module::new("test", "1").factory(Factory)
}
fn runtime() -> Runtime {
    Runtime::new(module()).unwrap()
}
static WAKES: AtomicUsize = AtomicUsize::new(0);
extern "C" fn wake(_: u64) {
    WAKES.fetch_add(1, Ordering::SeqCst);
}
fn request(runtime: &Runtime, value: Value) -> PluginResult<Value> {
    runtime.handle(
        serde_json::from_value(value).unwrap(),
        WakeV1 { token: 7, wake },
    )
}
fn create(runtime: &Runtime, config: Value) -> u64 {
    request(
        runtime,
        json!({"op":"create","factory":"test","config":config}),
    )
    .unwrap()["instance"]
        .as_u64()
        .unwrap()
}
fn begin(runtime: &Runtime, op: &str, instance: u64) -> u64 {
    request(runtime, json!({"op":op,"instance":instance})).unwrap()["job"]
        .as_u64()
        .unwrap()
}
fn poll(runtime: &Runtime, job: u64) -> PluginResult<Value> {
    request(runtime, json!({"op":"poll","job":job}))
}
fn drop_job(runtime: &Runtime, job: u64) {
    request(runtime, json!({"op":"drop_job","job":job})).unwrap();
}
fn active(runtime: &Runtime, config: Value) -> u64 {
    let instance = create(runtime, config);
    let job = begin(runtime, "setup", instance);
    assert_eq!(
        poll(runtime, job).unwrap(),
        json!({"state":"ready","result":{"ok":null}})
    );
    drop_job(runtime, job);
    instance
}
#[test]
fn setup_and_cleanup_results_are_consumed_once_before_destroy() {
    let runtime = runtime();
    let instance = create(&runtime, Value::Null);
    assert!(request(&runtime, json!({"op":"call_sync","instance":instance,"service":"service","method":"sync","args":null})).is_err());
    let job = begin(&runtime, "setup", instance);
    assert_eq!(poll(&runtime, job).unwrap()["state"], "ready");
    assert_eq!(poll(&runtime, job).unwrap_err(), "JobResultConsumed");
    assert!(request(&runtime, json!({"op":"cleanup","instance":instance})).is_err());
    drop_job(&runtime, job);
    assert_eq!(request(&runtime, json!({"op":"call_sync","instance":instance,"service":"service","method":"sync","args":{"text":"hello"}})).unwrap()["value"]["text"], "hello");
    let cleanup = begin(&runtime, "cleanup", instance);
    poll(&runtime, cleanup).unwrap();
    assert_eq!(
        request(&runtime, json!({"op":"destroy","instance":instance})).unwrap_err(),
        "InstanceHasJobs"
    );
    drop_job(&runtime, cleanup);
    request(&runtime, json!({"op":"destroy","instance":instance})).unwrap();
    assert_eq!(
        request(&runtime, json!({"op":"destroy","instance":instance})).unwrap_err(),
        "UnknownInstance"
    );
}
#[test]
fn pending_cancellation_requires_real_landing_and_drop() {
    let runtime = runtime();
    let instance = active(&runtime, Value::Null);
    let job = request(&runtime, json!({"op":"call_async","instance":instance,"service":"service","method":"async","args":null})).unwrap()["job"].as_u64().unwrap();
    assert_eq!(poll(&runtime, job).unwrap()["state"], "pending");
    assert_eq!(
        request(&runtime, json!({"op":"drop_job","job":job})).unwrap_err(),
        "JobStillPending"
    );
    request(&runtime, json!({"op":"cancel","job":job})).unwrap();
    assert_eq!(
        request(&runtime, json!({"op":"drop_job","job":job})).unwrap_err(),
        "JobStillPending"
    );
    assert_eq!(
        request(&runtime, json!({"op":"cleanup","instance":instance})).unwrap_err(),
        "InvalidLifecycleState"
    );
    assert_eq!(
        poll(&runtime, job).unwrap(),
        json!({"state":"ready","result":{"error":"Cancelled"}})
    );
    drop_job(&runtime, job);
    let cleanup = begin(&runtime, "cleanup", instance);
    poll(&runtime, cleanup).unwrap();
    drop_job(&runtime, cleanup);
    request(&runtime, json!({"op":"destroy","instance":instance})).unwrap();
}
#[test]
fn failed_cleanup_preserves_instance_and_can_retry() {
    let runtime = runtime();
    let instance = active(&runtime, json!({"cleanup_failure":true}));
    let cleanup = begin(&runtime, "cleanup", instance);
    assert_eq!(
        poll(&runtime, cleanup).unwrap()["result"]["error"],
        "CleanupFailed"
    );
    drop_job(&runtime, cleanup);
    assert_eq!(
        request(&runtime, json!({"op":"destroy","instance":instance})).unwrap_err(),
        "InstanceNotCleaned"
    );
    let retry = begin(&runtime, "cleanup", instance);
    assert_eq!(poll(&runtime, retry).unwrap()["result"], json!({"ok":null}));
    drop_job(&runtime, retry);
    request(&runtime, json!({"op":"destroy","instance":instance})).unwrap();
}
#[test]
fn failed_partial_setup_still_needs_cleanup() {
    let runtime = runtime();
    let instance = create(&runtime, json!({"setup_failure":true}));
    let setup = begin(&runtime, "setup", instance);
    assert_eq!(
        poll(&runtime, setup).unwrap()["result"]["error"],
        "SetupFailed"
    );
    drop_job(&runtime, setup);
    assert_eq!(
        request(&runtime, json!({"op":"destroy","instance":instance})).unwrap_err(),
        "InstanceNotCleaned"
    );
    let cleanup = begin(&runtime, "cleanup", instance);
    poll(&runtime, cleanup).unwrap();
    drop_job(&runtime, cleanup);
    request(&runtime, json!({"op":"destroy","instance":instance})).unwrap();
}
#[test]
fn panic_retains_unresolved_future_and_never_fabricates_cleanup() {
    let runtime = runtime();
    let instance = create(&runtime, json!({"setup_panic":true}));
    let setup = begin(&runtime, "setup", instance);
    assert_eq!(poll(&runtime, setup).unwrap_err(), "PluginPanic");
    assert_eq!(poll(&runtime, setup).unwrap_err(), "JobFaulted");
    assert_eq!(
        request(&runtime, json!({"op":"drop_job","job":setup})).unwrap_err(),
        "JobFaulted"
    );
    assert_eq!(
        request(&runtime, json!({"op":"cleanup","instance":instance})).unwrap_err(),
        "InvalidLifecycleState"
    );
    assert_eq!(
        request(&runtime, json!({"op":"destroy","instance":instance})).unwrap_err(),
        "InstanceHasJobs"
    );
}
#[test]
fn handles_never_wrap_or_reuse() {
    let runtime = runtime();
    runtime.records.lock().unwrap().next = u64::MAX;
    assert_eq!(
        request(
            &runtime,
            json!({"op":"create","factory":"test","config":null})
        )
        .unwrap_err(),
        "HandleSpaceExhausted"
    );
    assert_eq!(runtime.records.lock().unwrap().next, u64::MAX);
}
#[test]
fn undeclared_method_and_unknown_fields_are_rejected() {
    let runtime = runtime();
    let instance = active(&runtime, Value::Null);
    assert_eq!(request(&runtime, json!({"op":"call_sync","instance":instance,"service":"service","method":"async","args":null})).unwrap_err(), "UnknownOrMismatchedMethod");
    assert!(serde_json::from_value::<Request>(json!({"op":"describe","extra":1})).is_err());
}
#[test]
fn reentrant_poll_is_rejected_without_repolling_future() {
    let runtime = runtime();
    let instance = create(&runtime, Value::Null);
    let setup = begin(&runtime, "setup", instance);
    let job = runtime.job(setup).unwrap();
    let _locked = job.state.lock().unwrap();
    assert_eq!(poll(&runtime, setup).unwrap_err(), "JobBusy");
}
#[test]
fn never_started_instance_can_be_destroyed() {
    let runtime = runtime();
    let instance = create(&runtime, Value::Null);
    request(&runtime, json!({"op":"destroy","instance":instance})).unwrap();
}
unsafe extern "C" fn output(context: *mut c_void, bytes: *const u8, length: usize) {
    // SAFETY: tests pass valid Vec pointers and invoke_export supplies a live slice.
    unsafe {
        *(context.cast::<Vec<u8>>()) = std::slice::from_raw_parts(bytes, length).to_vec();
    }
}
#[test]
fn ffi_copies_one_response_and_rejects_invalid_buffers() {
    let runtime = OnceLock::new();
    let bytes = br#"{"op":"describe"}"#;
    let mut received = Vec::new();
    let context = (&mut received as *mut Vec<u8>).cast();
    // SAFETY: local buffers outlive synchronous callbacks; wake is static.
    let status = unsafe {
        invoke_export(
            &runtime,
            module,
            bytes.as_ptr(),
            bytes.len(),
            output,
            context,
            WakeV1 { token: 0, wake },
        )
    };
    assert_eq!(status, STATUS_OK);
    assert_eq!(
        serde_json::from_slice::<Value>(&received).unwrap()["ok"]["module_id"],
        "test"
    );
    received.clear();
    // SAFETY: invalid length/null combinations are rejected before dereference.
    let status = unsafe {
        invoke_export(
            &runtime,
            module,
            std::ptr::null(),
            1,
            output,
            context,
            WakeV1 { token: 0, wake },
        )
    };
    assert_eq!(status, STATUS_INVALID_BUFFER);
    assert!(received.is_empty());
}

struct PanicDrop;
impl Future for PanicDrop {
    type Output = PluginResult<Value>;
    fn poll(self: Pin<&mut Self>, _ctx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(Ok(Value::Null))
    }
}
impl Drop for PanicDrop {
    fn drop(&mut self) {
        panic!("future destructor panic");
    }
}
#[test]
fn future_destructor_failure_is_not_a_successful_setup() {
    let runtime = runtime();
    let instance = create(&runtime, json!({"drop_panic":true}));
    let job = begin(&runtime, "setup", instance);
    assert_eq!(poll(&runtime, job).unwrap_err(), "PluginPanic");
    assert_eq!(
        request(&runtime, json!({"op":"drop_job","job":job})).unwrap_err(),
        "JobFaulted"
    );
    assert_eq!(
        request(&runtime, json!({"op":"cleanup","instance":instance})).unwrap_err(),
        "InvalidLifecycleState"
    );
    assert_eq!(
        request(&runtime, json!({"op":"destroy","instance":instance})).unwrap_err(),
        "InstanceHasJobs"
    );
}
#[test]
fn future_constructor_failure_retains_the_unresolved_instance() {
    let runtime = runtime();
    let instance = create(&runtime, json!({"constructor_panic":true}));
    assert_eq!(
        request(&runtime, json!({"op":"setup","instance":instance})).unwrap_err(),
        "PluginPanic"
    );
    assert_eq!(
        request(&runtime, json!({"op":"destroy","instance":instance})).unwrap_err(),
        "InstanceHasJobs"
    );
    assert_eq!(
        request(&runtime, json!({"op":"cleanup","instance":instance})).unwrap_err(),
        "InvalidLifecycleState"
    );
}
#[test]
fn output_limits_turn_large_values_and_errors_into_bounded_errors() {
    assert_eq!(
        bounded_result(Ok(Value::String("x".repeat(MAX_MESSAGE_BYTES)))).unwrap_err(),
        "ResultTooLarge"
    );
    assert_eq!(
        bounded_result(Err("x".repeat(MAX_MESSAGE_BYTES))).unwrap_err(),
        "PluginErrorTooLarge"
    );
}

fn wire(runtime: &OnceLock<PluginResult<Runtime>>, request: Value) -> Value {
    let bytes = serde_json::to_vec(&request).unwrap();
    let mut received = Vec::new();
    let context = (&mut received as *mut Vec<u8>).cast();
    // SAFETY: request, output buffer and callback all remain alive for this call.
    let status = unsafe {
        invoke_export(
            runtime,
            module,
            bytes.as_ptr(),
            bytes.len(),
            output,
            context,
            WakeV1 { token: 42, wake },
        )
    };
    assert_eq!(status, STATUS_OK);
    assert!(received.len() <= MAX_MESSAGE_BYTES);
    serde_json::from_slice(&received).unwrap()
}
#[test]
fn ffi_result_boundaries_preserve_sync_values_and_async_completion_ownership() {
    let runtime = OnceLock::new();
    let instance = wire(
        &runtime,
        json!({"op":"create","factory":"test","config":null}),
    )["ok"]["instance"]
        .as_u64()
        .unwrap();
    let setup = wire(&runtime, json!({"op":"setup","instance":instance}))["ok"]["job"]
        .as_u64()
        .unwrap();
    assert_eq!(
        wire(&runtime, json!({"op":"poll","job":setup}))["ok"]["state"],
        "ready"
    );
    assert_eq!(
        wire(&runtime, json!({"op":"drop_job","job":setup})),
        json!({"ok":null})
    );
    for size in [MAX_MESSAGE_BYTES / 2 - 2, MAX_MESSAGE_BYTES / 2] {
        // The quotes count toward the serialized user value. Its surrounding
        // call/poll envelopes must not reduce the advertised user-value limit.
        let value = Value::String("x".repeat(size));
        let allowed = size + 2 <= MAX_MESSAGE_BYTES / 2;
        let sync = wire(
            &runtime,
            json!({"op":"call_sync","instance":instance,"service":"service","method":"sync","args":value}),
        );
        if allowed {
            assert_eq!(sync["ok"]["value"], value);
        } else {
            assert_eq!(sync["error"], "ResultTooLarge");
        }
        let job = wire(&runtime, json!({"op":"call_async","instance":instance,"service":"service","method":"async","args":{"echo":value}}))["ok"]["job"].as_u64().unwrap();
        let ready = wire(&runtime, json!({"op":"poll","job":job}));
        assert_eq!(ready["ok"]["state"], "ready");
        if allowed {
            assert_eq!(ready["ok"]["result"]["ok"], value);
        } else {
            assert_eq!(ready["ok"]["result"]["error"], "ResultTooLarge");
        }
        assert_eq!(
            wire(&runtime, json!({"op":"poll","job":job}))["error"],
            "JobResultConsumed"
        );
        assert_eq!(
            wire(&runtime, json!({"op":"drop_job","job":job})),
            json!({"ok":null})
        );
    }
    let cleanup = wire(&runtime, json!({"op":"cleanup","instance":instance}))["ok"]["job"]
        .as_u64()
        .unwrap();
    assert_eq!(
        wire(&runtime, json!({"op":"poll","job":cleanup}))["ok"]["result"],
        json!({"ok":null})
    );
    assert_eq!(
        wire(&runtime, json!({"op":"drop_job","job":cleanup})),
        json!({"ok":null})
    );
    assert_eq!(
        wire(&runtime, json!({"op":"destroy","instance":instance})),
        json!({"ok":null})
    );
}

fn nested_value(depth: usize) -> Value {
    let mut value = Value::Null;
    for level in 0..depth {
        value = if level % 2 == 0 {
            Value::Array(vec![value])
        } else {
            Value::Object([("nested".to_string(), value)].into_iter().collect())
        };
    }
    value
}
#[test]
fn ffi_depth_limits_keep_ready_results_parseable_and_instances_cleanable() {
    let runtime = OnceLock::new();
    let instance = wire(
        &runtime,
        json!({"op":"create","factory":"test","config":null}),
    )["ok"]["instance"]
        .as_u64()
        .unwrap();
    let setup = wire(&runtime, json!({"op":"setup","instance":instance}))["ok"]["job"]
        .as_u64()
        .unwrap();
    assert_eq!(
        wire(&runtime, json!({"op":"poll","job":setup}))["ok"]["state"],
        "ready"
    );
    assert_eq!(
        wire(&runtime, json!({"op":"drop_job","job":setup})),
        json!({"ok":null})
    );
    for depth in [MAX_VALUE_DEPTH, MAX_VALUE_DEPTH + 1, 130] {
        let job = wire(&runtime, json!({"op":"call_async","instance":instance,"service":"service","method":"async","args":{"nestedDepth":depth}}))["ok"]["job"].as_u64().unwrap();
        // wire() parses using serde_json's normal recursion limit, exactly as
        // the host does. A deep plugin result must become an inner job error.
        let ready = wire(&runtime, json!({"op":"poll","job":job}));
        assert_eq!(ready["ok"]["state"], "ready");
        if depth <= MAX_VALUE_DEPTH {
            assert_eq!(ready["ok"]["result"]["ok"], nested_value(depth));
        } else {
            assert_eq!(ready["ok"]["result"]["error"], "ValueTooDeep");
        }
        assert_eq!(
            wire(&runtime, json!({"op":"drop_job","job":job})),
            json!({"ok":null})
        );
    }
    let cleanup = wire(&runtime, json!({"op":"cleanup","instance":instance}))["ok"]["job"]
        .as_u64()
        .unwrap();
    assert_eq!(
        wire(&runtime, json!({"op":"poll","job":cleanup}))["ok"]["result"],
        json!({"ok":null})
    );
    assert_eq!(
        wire(&runtime, json!({"op":"drop_job","job":cleanup})),
        json!({"ok":null})
    );
    assert_eq!(
        wire(&runtime, json!({"op":"destroy","instance":instance})),
        json!({"ok":null})
    );
}
#[test]
fn rejected_deep_values_are_discarded_without_recursive_destruction() {
    assert_eq!(
        bounded_result(Ok(nested_value(10_000))).unwrap_err(),
        "ValueTooDeep"
    );
}
