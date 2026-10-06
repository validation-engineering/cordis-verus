use super::*;
use std::sync::atomic::AtomicUsize;

fn cx_poll(future: &mut PluginFuture) -> Poll<PluginResult<Value>> {
    future
        .as_mut()
        .poll(&mut Context::from_waker(Waker::noop()))
}
#[derive(Default)]
struct Shared {
    escaped: Mutex<Option<PluginContext>>,
}
struct Factory(Arc<Shared>);
struct Instance {
    shared: Arc<Shared>,
    config: Value,
    cleanup_count: AtomicUsize,
}
impl PluginFactory for Factory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "reverse".into(),
            inject: vec!["js".into()],
            services: vec![ServiceDescriptor {
                name: "reverse".into(),
                methods: ["call", "dropped", "batch", "escape"]
                    .iter()
                    .map(|name| MethodDescriptor {
                        name: (*name).into(),
                        kind: MethodKind::Async,
                    })
                    .collect(),
            }],
        }
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Instance {
            shared: self.0.clone(),
            config,
            cleanup_count: AtomicUsize::new(0),
        }))
    }
}
impl PluginInstance for Instance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        let call = self.config["setup"].as_bool().unwrap_or(false);
        Box::pin(async move {
            if call {
                ctx.call("js", "setup", json!([])).await?;
            }
            Ok(Value::Null)
        })
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        let call = self.config["cleanup"].as_bool().unwrap_or(false);
        let fail = self.config["failCleanupOnce"].as_bool().unwrap_or(false)
            && self.cleanup_count.fetch_add(1, Ordering::SeqCst) == 0;
        Box::pin(async move {
            if call {
                ctx.call("js", "cleanup", json!([])).await?;
            }
            if fail {
                Err("CleanupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        _service: &str,
        method: &str,
        args: Value,
    ) -> PluginFuture {
        if method == "escape" {
            *self.shared.escaped.lock().unwrap() = Some(ctx);
            return Box::pin(async { Ok(Value::Null) });
        }
        let dropped = method == "dropped" || method == "batch";
        if dropped {
            *self.shared.escaped.lock().unwrap() = Some(ctx.clone());
        }
        Box::pin(async move {
            if !dropped {
                return ctx
                    .call(
                        args["service"].as_str().unwrap_or("js"),
                        "echo",
                        args.get("arguments").cloned().unwrap_or_else(|| json!([])),
                    )
                    .await;
            }
            let count = args["count"].as_u64().unwrap_or(1);
            let size = args["size"].as_u64().unwrap_or(0) as usize;
            let mut admitted = 0;
            let mut failure = None;
            for _ in 0..count {
                let mut call = Box::pin(ctx.call("js", "echo", json!(["x".repeat(size)])));
                std::future::poll_fn(|cx| {
                    match call.as_mut().poll(cx) {
                        Poll::Pending => admitted += 1,
                        Poll::Ready(Err(error)) => failure = Some(error),
                        Poll::Ready(Ok(_)) => panic!("host cannot resolve during setup"),
                    }
                    Poll::Ready(())
                })
                .await;
                drop(call);
            }
            Ok(json!({"admitted":admitted,"failure":failure}))
        })
    }
}
extern "C" fn wake(_: u64) {}
fn runtime(config: Value) -> (Runtime, u64, Arc<Shared>) {
    let shared = Arc::new(Shared::default());
    let runtime =
        Runtime::new(Module::new("reverse", "1").factory(Factory(shared.clone()))).unwrap();
    let instance = req(
        &runtime,
        json!({"op":"create","factory":"reverse","config":config}),
    )
    .unwrap()["instance"]
        .as_u64()
        .unwrap();
    (runtime, instance, shared)
}
fn req(runtime: &Runtime, value: Value) -> PluginResult<Value> {
    runtime.handle(
        serde_json::from_value(value).unwrap(),
        WakeV1 { token: 0, wake },
    )
}
fn start(runtime: &Runtime, instance: u64, op: &str) -> u64 {
    req(runtime, json!({"op":op,"instance":instance})).unwrap()["job"]
        .as_u64()
        .unwrap()
}
fn call(runtime: &Runtime, instance: u64, method: &str, args: Value) -> u64 {
    req(runtime,json!({"op":"call_async","instance":instance,"service":"reverse","method":method,"args":args})).unwrap()["job"].as_u64().unwrap()
}
fn poll(runtime: &Runtime, job: u64) -> Value {
    req(runtime, json!({"op":"poll","job":job})).unwrap()
}
fn resolve(runtime: &Runtime, job: u64, request: u64, result: Value) -> PluginResult<Value> {
    req(
        runtime,
        json!({"op":"resolve_call","job":job,"request":request,"result":result}),
    )
}
fn release(runtime: &Runtime, job: u64) {
    req(runtime, json!({"op":"drop_job","job":job})).unwrap();
}
fn activate(runtime: &Runtime, instance: u64) {
    let job = start(runtime, instance, "setup");
    assert_eq!(poll(runtime, job)["state"], "ready");
    release(runtime, job);
}
fn destroy(runtime: &Runtime, instance: u64) {
    let job = start(runtime, instance, "cleanup");
    assert_eq!(poll(runtime, job)["result"], json!({"ok":null}));
    release(runtime, job);
    req(runtime, json!({"op":"destroy","instance":instance})).unwrap();
}

#[test]
fn setup_reverse_call_is_delivered_once_and_requires_exact_acknowledgement() {
    let (runtime, instance, _) = runtime(json!({"setup":true}));
    let job = start(&runtime, instance, "setup");
    let first = poll(&runtime, job);
    assert_eq!(first["state"], "pending");
    assert_eq!(
        first["calls"],
        json!([{"request":1,"kind":"call","service":"js","method":"setup","args":[]}])
    );
    assert!(poll(&runtime, job).get("calls").is_none());
    assert_eq!(
        resolve(&runtime, job, 99, json!({"ok":null})).unwrap_err(),
        "UnknownReverseCall"
    );
    resolve(&runtime, job, 1, json!({"ok":null})).unwrap();
    assert_eq!(
        resolve(&runtime, job, 1, json!({"ok":null})).unwrap_err(),
        "UnknownReverseCall"
    );
    assert_eq!(poll(&runtime, job)["result"], json!({"ok":null}));
    release(&runtime, job);
    destroy(&runtime, instance);
}
#[test]
fn dropped_reverse_future_keeps_main_completion_pending_until_host_lands() {
    let (runtime, instance, shared) = runtime(Value::Null);
    activate(&runtime, instance);
    let job = call(&runtime, instance, "dropped", json!({}));
    let pending = poll(&runtime, job);
    assert_eq!(pending["calls"][0]["request"], 1);
    assert_eq!(pending["draining"], true);
    assert!(pending.get("queuedCalls").is_none());
    let ctx = shared.escaped.lock().unwrap().take().unwrap();
    let mut escaped: PluginFuture =
        Box::pin(async move { ctx.call("js", "echo", json!([])).await });
    assert!(matches!(cx_poll(&mut escaped),Poll::Ready(Err(error))if error=="ActionClosed"));
    assert_eq!(
        req(&runtime, json!({"op":"drop_job","job":job})).unwrap_err(),
        "JobStillPending"
    );
    req(&runtime, json!({"op":"cancel","job":job})).unwrap();
    assert_eq!(poll(&runtime, job)["state"], "pending");
    resolve(&runtime, job, 1, json!({"ok":null})).unwrap();
    assert_eq!(poll(&runtime, job)["result"]["ok"]["admitted"], 1);
    release(&runtime, job);
    destroy(&runtime, instance);
}
#[test]
fn pending_calls_have_bounded_batches_and_capacity_without_losing_obligations() {
    let (runtime, instance, _) = runtime(Value::Null);
    activate(&runtime, instance);
    let job = call(
        &runtime,
        instance,
        "batch",
        json!({"count":65,"size":10000}),
    );
    let first = poll(&runtime, job);
    assert_eq!(first["draining"], true);
    assert_eq!(first["queuedCalls"], true);
    let first = first["calls"].as_array().unwrap();
    assert!(first.len() < MAX_PENDING_CALLS);
    assert!(serde_json::to_vec(first).unwrap().len() <= MAX_CALL_BATCH_BYTES);
    let second = poll(&runtime, job);
    assert_eq!(second["draining"], true);
    assert!(second.get("queuedCalls").is_none());
    let second = second["calls"].as_array().unwrap();
    assert_eq!(first.len() + second.len(), MAX_PENDING_CALLS);
    for item in first.iter().chain(second) {
        resolve(
            &runtime,
            job,
            item["request"].as_u64().unwrap(),
            json!({"ok":null}),
        )
        .unwrap();
    }
    let ready = poll(&runtime, job);
    assert_eq!(
        ready["result"]["ok"],
        json!({"admitted":64,"failure":"ReverseCallCapacity"})
    );
    release(&runtime, job);
    destroy(&runtime, instance);
}
#[test]
fn an_admitted_maximum_request_always_fits_in_an_empty_batch() {
    let wake = Arc::new(HostWake(Mutex::new(None)));
    let calls = CallAction::new(&["js".into()], wake);
    let empty = ReverseCall {
        request: 1,
        operation: ReverseOperation::Call {
            service: "js".into(),
            method: "echo".into(),
            args: json!([""]),
        },
    };
    let overhead = serde_json::to_vec(&empty).unwrap().len();
    let size = MAX_CALL_BATCH_BYTES - overhead - 3;
    calls
        .enqueue("js", "echo", json!(["x".repeat(size)]))
        .unwrap();
    let (batch, pending) = calls.take_batch();
    assert_eq!(pending, 1);
    assert_eq!(batch.len(), 1);
    assert!(serde_json::to_vec(&batch).unwrap().len() <= MAX_CALL_BATCH_BYTES);
    assert_eq!(
        calls
            .enqueue("js", "echo", json!(["x".repeat(size + 1)]))
            .err()
            .unwrap(),
        "ReverseCallTooLarge"
    );
}
#[test]
fn escaped_context_closes_at_body_completion() {
    let (runtime, instance, shared) = runtime(Value::Null);
    activate(&runtime, instance);
    let job = call(&runtime, instance, "escape", Value::Null);
    assert_eq!(poll(&runtime, job)["state"], "ready");
    let ctx = shared.escaped.lock().unwrap().take().unwrap();
    let mut escaped: PluginFuture =
        Box::pin(async move { ctx.call("js", "echo", json!([])).await });
    assert!(matches!(cx_poll(&mut escaped),Poll::Ready(Err(error))if error=="ActionClosed"));
    release(&runtime, job);
    destroy(&runtime, instance);
}
#[test]
fn undeclared_injections_and_non_array_arguments_never_enqueue_calls() {
    let (runtime, instance, _) = runtime(Value::Null);
    activate(&runtime, instance);
    for (args, error) in [
        (json!({"service":"other"}), "UndeclaredInjection"),
        (json!({"arguments":{}}), "ReverseCallArgumentsMustBeArray"),
    ] {
        let job = call(&runtime, instance, "call", args);
        let ready = poll(&runtime, job);
        assert_eq!(ready["result"]["error"], error);
        assert!(ready.get("calls").is_none());
        release(&runtime, job);
    }
    destroy(&runtime, instance);
}
#[test]
fn cleanup_reverse_calls_survive_cancellation_and_failed_inverse_retry() {
    let (runtime, instance, _) = runtime(json!({"cleanup":true,"failCleanupOnce":true}));
    activate(&runtime, instance);
    for attempt in 0..2 {
        let job = start(&runtime, instance, "cleanup");
        req(&runtime, json!({"op":"cancel","job":job})).unwrap();
        assert_eq!(poll(&runtime, job)["calls"][0]["method"], "cleanup");
        resolve(&runtime, job, 1, json!({"ok":null})).unwrap();
        let ready = poll(&runtime, job);
        assert_eq!(
            ready["result"],
            if attempt == 0 {
                json!({"error":"CleanupFailed"})
            } else {
                json!({"ok":null})
            }
        );
        release(&runtime, job);
    }
    req(&runtime, json!({"op":"destroy","instance":instance})).unwrap();
}
#[test]
fn reverse_reply_limits_and_invalid_variants_do_not_strand_the_job() {
    let (runtime, instance, _) = runtime(Value::Null);
    activate(&runtime, instance);
    let job = call(&runtime, instance, "call", json!({}));
    poll(&runtime, job);
    assert!(serde_json::from_value::<Request>(
        json!({"op":"resolve_call","job":job,"request":1,"result":{"ok":null,"error":"both"}})
    )
    .is_err());
    resolve(
        &runtime,
        job,
        1,
        json!({"ok":"x".repeat(MAX_MESSAGE_BYTES/2)}),
    )
    .unwrap();
    assert_eq!(poll(&runtime, job)["result"]["error"], "ResultTooLarge");
    release(&runtime, job);
    destroy(&runtime, instance);
}
#[test]
fn unresolved_or_exhausted_request_identifiers_are_never_acknowledged_or_reused() {
    let calls = CallAction::new(&["js".into()], Arc::new(HostWake(Mutex::new(None))));
    calls.enqueue("js", "echo", json!([])).unwrap();
    assert_eq!(
        calls.resolve(1, Ok(Value::Null)).unwrap_err(),
        "ReverseCallNotDispatched"
    );
    calls.queue.lock().unwrap().next = u64::MAX;
    assert_eq!(
        calls.enqueue("js", "echo", json!([])).err().unwrap(),
        "ReverseCallHandleSpaceExhausted"
    );
}
