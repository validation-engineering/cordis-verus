// Compile the value-independent SDK itself, with no Node environment or second
// graph. NAPI integration and ticket admission are exercised by the JS suite.
#[path = "../src/plugin.rs"]
mod plugin;
use plugin::*;
use serde_json::{json, Value};
use std::{
    future::Future,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Mutex,
    },
    task::{Context, Poll, Waker},
};

#[derive(Default)]
struct Data {
    polls: AtomicUsize,
    cleanups: AtomicUsize,
    context: Mutex<Option<PluginContext>>,
    wake: Mutex<Option<Waker>>,
}
struct Factory(Arc<Data>);
struct Instance(Arc<Data>);
impl PluginFactory for Factory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "test".into(),
            inject: vec!["input".into()],
            services: vec![ServiceDescriptor {
                name: "service".into(),
                methods: vec![
                    MethodDescriptor {
                        name: "cancel".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "read".into(),
                        kind: MethodKind::Sync,
                    },
                    MethodDescriptor {
                        name: "dropped".into(),
                        kind: MethodKind::Async,
                    },
                ],
            }],
        }
    }
    fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Instance(self.0.clone())))
    }
}
impl PluginInstance for Instance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        *self.0.context.lock().unwrap() = Some(ctx.clone());
        let data = self.0.clone();
        Box::pin(std::future::poll_fn(move |cx| {
            data.polls.fetch_add(1, Ordering::Relaxed);
            *data.wake.lock().unwrap() = Some(cx.waker().clone());
            Poll::Pending
        }))
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        let attempt = self.0.cleanups.fetch_add(1, Ordering::Relaxed);
        Box::pin(async move {
            ctx.call("input", "cleanup", json!([])).await?;
            if attempt == 0 {
                Err("retry".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn call_sync(&self, _: &str, _: &str, _: Value) -> PluginResult<Value> {
        Ok(json!(42))
    }
    fn call_async(&self, ctx: PluginContext, _: &str, method: &str, _: Value) -> PluginFuture {
        if method == "dropped" {
            Box::pin(async move {
                let mut request = Box::pin(ctx.call("input", "wait", json!([])));
                std::future::poll_fn(|cx| {
                    assert!(request.as_mut().poll(cx).is_pending());
                    Poll::Ready(())
                })
                .await;
                drop(request);
                Ok(json!("returned"))
            })
        } else {
            Box::pin(async move {
                ctx.cancellation().cancelled().await;
                Ok(json!("cancelled"))
            })
        }
    }
}
fn backend() -> (plugin::Backend, Arc<Data>) {
    let data = Arc::new(Data::default());
    let mut registry = FactoryRegistry::new();
    registry.register(Factory(data.clone())).unwrap();
    (plugin::Backend::new(registry, Arc::new(|| {})), data)
}
fn number(value: &Value, key: &str) -> u64 {
    value[key].as_str().unwrap().parse().unwrap()
}
#[test]
fn polling_is_event_driven_and_duplicate_factory_names_are_rejected() {
    let (mut backend, data) = backend();
    let started = backend.start(1, 1, "test", Value::Null).unwrap();
    assert!(backend.busy());
    assert!(!backend.can_close());
    assert_eq!(backend.info()["factories"][0]["name"], "test");
    assert_eq!(backend.owner(number(&started, "session")).unwrap(), (1, 1));
    backend.poll();
    backend.poll();
    backend.poll();
    assert_eq!(data.polls.load(Ordering::Relaxed), 1);
    data.wake.lock().unwrap().take().unwrap().wake();
    backend.poll();
    assert_eq!(data.polls.load(Ordering::Relaxed), 2);
    assert!(backend.start(1, 1, "test", Value::Null).is_err());
    let mut registry = FactoryRegistry::new();
    registry.register(Factory(data.clone())).unwrap();
    assert!(registry.register(Factory(data)).is_err());
}
struct ReadyFactory;
struct ReadyInstance;
impl PluginFactory for ReadyFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        Factory(Arc::new(Data::default())).descriptor()
    }
    fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(ReadyInstance))
    }
}
impl PluginInstance for ReadyInstance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        Box::pin(async move {
            ctx.provide("service").await?;
            Ok(Value::Null)
        })
    }
    fn call_sync(&self, _: &str, _: &str, _: Value) -> PluginResult<Value> {
        Ok(json!(42))
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginFuture {
        Instance(Arc::new(Data::default())).call_async(ctx, service, method, args)
    }
}
fn ready() -> (plugin::Backend, u64) {
    let mut registry = FactoryRegistry::new();
    registry.register(ReadyFactory).unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let started = backend.start(1, 1, "test", Value::Null).unwrap();
    let session = number(&started, "session");
    let polled = backend.poll();
    let request = number(&polled["calls"][0], "request");
    backend
        .reply(
            request,
            Ok(json!({"publication":"3","port":{"key":"4","realm":"0"}})),
        )
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    assert_eq!(backend.binding(session, "service").unwrap().0, 3);
    (backend, session)
}
#[test]
fn cancellation_is_per_job_and_completed_cancellation_is_idempotent() {
    let (mut backend, session) = ready();
    let first = number(
        &backend
            .call(session, "service", "cancel", json!([]), false, false)
            .unwrap(),
        "job",
    );
    let second = number(
        &backend
            .call(session, "service", "cancel", json!([]), false, false)
            .unwrap(),
        "job",
    );
    backend.poll();
    backend.cancel_job(first).unwrap();
    let result = backend.poll();
    assert_eq!(result["jobs"].as_array().unwrap().len(), 1);
    assert_eq!(number(&result["jobs"][0], "job"), first);
    backend.cancel_job(first).unwrap();
    assert_eq!(backend.poll()["jobs"], json!([]));
    assert_eq!(
        backend
            .call(session, "service", "read", json!([]), false, false)
            .unwrap()["value"],
        42
    );
    backend.cancel(session).unwrap();
    let result = backend.poll();
    assert_eq!(number(&result["jobs"][0], "job"), second);
    assert!(backend
        .call(session, "service", "read", json!([]), false, false)
        .is_err());
    assert_eq!(
        backend
            .call(session, "service", "read", json!([]), true, false)
            .unwrap()["value"],
        42
    );
    assert!(backend.cancel_job(u64::MAX).is_err());
}
#[test]
fn dropping_a_call_future_does_not_fabricate_external_completion() {
    let (mut backend, session) = ready();
    let job = number(
        &backend
            .call(session, "service", "dropped", json!([]), true, false)
            .unwrap(),
        "job",
    );
    let polled = backend.poll();
    let request = number(&polled["calls"][0], "request");
    assert_eq!(polled["jobs"], json!([]));
    assert_eq!(backend.authority(session, job).unwrap(), (1, 1, true));
    assert!(backend.cleanup(session).is_err());
    backend.cancel_job(job).unwrap();
    assert_eq!(backend.poll()["jobs"], json!([]));
    backend.reply(request, Ok(Value::Null)).unwrap();
    let result = backend.poll();
    assert_eq!(result["jobs"][0]["value"], "returned");
    assert!(backend.reply(request, Ok(Value::Null)).is_err());
    assert!(backend.authority(session, job).is_err());
    let cleanup = backend.cleanup(session).unwrap();
    let orphan = expect_call(&mut backend, "close_orphans");
    backend
        .reply(number(&orphan, "request"), Ok(Value::Null))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["job"], cleanup["job"]);
    backend.release(session).unwrap();
    assert!(backend.can_close());
    assert!(!backend.busy());
}
#[test]
fn backend_drop_closes_worker_requests_and_cancels_individual_tokens() {
    let (mut backend, data) = backend();
    backend.start(1, 1, "test", Value::Null).unwrap();
    backend.poll();
    let ctx = data.context.lock().unwrap().clone().unwrap();
    let token = ctx.cancellation();
    let mut request = Box::pin(ctx.call("input", "wait", json!([])));
    let waker = Waker::noop();
    assert!(request
        .as_mut()
        .poll(&mut Context::from_waker(waker))
        .is_pending());
    drop(backend);
    assert!(token.is_cancelled());
    assert_eq!(
        request.as_mut().poll(&mut Context::from_waker(waker)),
        Poll::Ready(Err("ActionClosed".into()))
    );
    let mut escaped = Box::pin(ctx.call("input", "late", json!([])));
    assert!(matches!(
        escaped.as_mut().poll(&mut Context::from_waker(waker)),
        Poll::Ready(Err(_))
    ));
}

struct RetryFactory(Arc<Data>);
struct RetryInstance(Arc<Data>);
impl PluginFactory for RetryFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        Factory(self.0.clone()).descriptor()
    }
    fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(RetryInstance(self.0.clone())))
    }
}
impl PluginInstance for RetryInstance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        *self.0.context.lock().unwrap() = Some(ctx.clone());
        ReadyInstance.setup(ctx)
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        Instance(self.0.clone()).cleanup(ctx)
    }
}
#[test]
fn cleanup_retry_keeps_the_instance_and_completed_setup_context_is_closed() {
    let data = Arc::new(Data::default());
    let mut registry = FactoryRegistry::new();
    registry.register(RetryFactory(data.clone())).unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let start = backend.start(1, 1, "test", Value::Null).unwrap();
    let session = number(&start, "session");
    let call = backend.poll()["calls"][0].clone();
    backend
        .reply(
            number(&call, "request"),
            Ok(json!({"publication":"3","port":{"key":"4","realm":"0"}})),
        )
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    let ctx = data.context.lock().unwrap().clone().unwrap();
    let mut escaped = Box::pin(ctx.provide("service"));
    let waker = Waker::noop();
    assert_eq!(
        escaped.as_mut().poll(&mut Context::from_waker(waker)),
        Poll::Ready(Err("ActionClosed".into()))
    );
    for success in [false, true] {
        backend.cleanup(session).unwrap();
        let orphan = expect_call(&mut backend, "close_orphans");
        backend
            .reply(number(&orphan, "request"), Ok(Value::Null))
            .unwrap();
        let call = backend.poll()["calls"][0].clone();
        backend
            .reply(number(&call, "request"), Ok(Value::Null))
            .unwrap();
        assert_eq!(backend.poll()["jobs"][0]["success"], success);
        if !success {
            assert!(backend.release(session).is_err());
        }
    }
    assert_eq!(data.cleanups.load(Ordering::Relaxed), 2);
    backend.release(session).unwrap();
}

#[derive(Default)]
struct StreamData {
    pulls: AtomicUsize,
    cancels: AtomicUsize,
    closes: AtomicUsize,
}
struct StreamFactory(Arc<StreamData>);
struct StreamInstance(Arc<StreamData>);
struct TestStream(Arc<StreamData>);
impl PluginFactory for StreamFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        let mut descriptor = ReadyFactory.descriptor();
        descriptor.services[0].methods.extend([
            MethodDescriptor {
                name: "stream".into(),
                kind: MethodKind::Stream,
            },
            MethodDescriptor {
                name: "foreign".into(),
                kind: MethodKind::Async,
            },
        ]);
        descriptor
    }
    fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(StreamInstance(self.0.clone())))
    }
}
impl PluginInstance for StreamInstance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        ReadyInstance.setup(ctx)
    }
    fn open_stream(&self, _: &str, _: &str, _: Value) -> PluginResult<Arc<dyn PluginStream>> {
        Ok(Arc::new(TestStream(self.0.clone())))
    }
    fn call_async(&self, ctx: PluginContext, _: &str, _: &str, args: Value) -> PluginFuture {
        Box::pin(async move {
            if args[0] == "lateOpen" {
                let mut open = Box::pin(ctx.open_stream("input", "stream", json!([])));
                std::future::poll_fn(|cx| {
                    assert!(open.as_mut().poll(cx).is_pending());
                    Poll::Ready(())
                })
                .await;
                return Ok(Value::Null);
            }
            let stream: JsStream = ctx.open_stream("input", "stream", json!([])).await?;
            if args[0] == "busyClose" {
                let mut next = Box::pin(stream.next());
                std::future::poll_fn(|cx| {
                    assert!(next.as_mut().poll(cx).is_pending());
                    Poll::Ready(())
                })
                .await;
                let clone = stream.clone();
                assert_eq!(clone.close().await, Err("StreamBusy".into()));
                let first = next.await?;
                // Busy is side-effect free: another pull remains admissible.
                stream.next().await?;
                stream.close().await?;
                return Ok(json!(first));
            }
            if args[0] == "dropNext" {
                let mut next = Box::pin(stream.next());
                std::future::poll_fn(|cx| {
                    assert!(next.as_mut().poll(cx).is_pending());
                    Poll::Ready(())
                })
                .await;
                drop(next);
                return Ok(json!("dropped"));
            }
            let value = stream.next().await?;
            if args[0] == "explicit" {
                stream.close().await?;
            }
            Ok(json!(value))
        })
    }
}
impl PluginStream for TestStream {
    fn next(&self, ctx: PluginContext) -> StreamFuture {
        self.0.pulls.fetch_add(1, Ordering::Relaxed);
        Box::pin(async move { Ok(Some(ctx.call("input", "pull", json!([])).await?)) })
    }
    fn cancel(&self) {
        self.0.cancels.fetch_add(1, Ordering::Relaxed);
    }
    fn close(&self, _: PluginContext) -> PluginFuture {
        let attempt = self.0.closes.fetch_add(1, Ordering::Relaxed);
        Box::pin(async move {
            if attempt == 0 {
                Err("first close failed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
}
fn stream_ready() -> (plugin::Backend, u64, Arc<StreamData>) {
    let data = Arc::new(StreamData::default());
    let mut registry = FactoryRegistry::new();
    registry.register(StreamFactory(data.clone())).unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let start = backend.start(1, 1, "test", Value::Null).unwrap();
    let session = number(&start, "session");
    let call = backend.poll()["calls"][0].clone();
    backend
        .reply(
            number(&call, "request"),
            Ok(json!({"publication":"3","port":{"key":"4","realm":"0"}})),
        )
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    (backend, session, data)
}
fn expect_call(backend: &mut plugin::Backend, kind: &str) -> Value {
    // A main result switches to its finalizer on the first event-driven poll;
    // the second poll runs that newly readied finalizer.
    for _ in 0..2 {
        let polled = backend.poll();
        assert_eq!(polled["jobs"], json!([]));
        if let Some(call) = polled["calls"].as_array().unwrap().first() {
            assert_eq!(polled["calls"].as_array().unwrap().len(), 1);
            assert_eq!(call["kind"], kind);
            return call.clone();
        }
    }
    panic!("missing {kind}");
}
fn foreign_open(backend: &mut plugin::Backend, session: u64, mode: &str) -> (u64, Value) {
    let job = number(
        &backend
            .call(session, "service", "foreign", json!([mode]), false, false)
            .unwrap(),
        "job",
    );
    (job, expect_call(backend, "stream_open"))
}
#[test]
fn rust_streams_are_owned_single_flight_and_close_joins_real_pull_with_retry() {
    let (mut backend, session, data) = stream_ready();
    assert!(backend
        .is_resource_method(session, "service", "stream")
        .unwrap());
    let stream = number(
        &backend
            .call(session, "service", "stream", json!([]), false, false)
            .unwrap(),
        "stream",
    );
    backend.bind_stream(stream, Some((9, 2))).unwrap();
    assert_eq!(
        backend
            .stream_binding(session, stream, Some((9, 2)))
            .unwrap()
            .1,
        3
    );
    assert!(backend
        .stream_binding(session, stream, Some((9, 3)))
        .is_err());
    assert!(backend
        .stream_binding(session + 1, stream, Some((9, 2)))
        .is_err());
    assert_eq!(data.pulls.load(Ordering::Relaxed), 0);
    let pull = backend.stream_next(session, stream, false, false).unwrap();
    assert!(backend.stream_next(session, stream, false, false).is_err());
    let request = expect_call(&mut backend, "call");
    let closing = backend.stream_close(session, stream).unwrap();
    assert_eq!(backend.stream_close(session, stream).unwrap(), closing);
    assert_eq!(data.cancels.load(Ordering::Relaxed), 1);
    assert!(backend.cancel_job(number(&closing, "job")).is_err());
    assert_eq!(backend.poll()["jobs"], json!([]));
    assert_eq!(data.closes.load(Ordering::Relaxed), 0);
    assert!(backend.cleanup(session).is_err());
    backend
        .reply(number(&request, "request"), Ok(json!(17)))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["job"], pull["job"]);
    let failed = backend.poll();
    assert_eq!(failed["jobs"][0]["job"], closing["job"]);
    assert_eq!(failed["jobs"][0]["success"], false);
    assert!(backend.stream_next(session, stream, false, false).is_err());
    assert!(backend.cleanup(session).is_err());
    backend.stream_close(session, stream).unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    assert_eq!(
        backend.stream_close(session, stream).unwrap()["closed"],
        true
    );
    let cleanup = backend.cleanup(session).unwrap();
    let orphan = expect_call(&mut backend, "close_orphans");
    backend
        .reply(number(&orphan, "request"), Ok(Value::Null))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["job"], cleanup["job"]);
    backend.release(session).unwrap();
}
#[test]
fn foreign_stream_explicit_close_keeps_exact_request_authority_until_reply() {
    let (mut backend, session, _) = stream_ready();
    let (job, open) = foreign_open(&mut backend, session, "explicit");
    backend
        .reply(number(&open, "request"), Ok(json!({"stream":"js1"})))
        .unwrap();
    let next = expect_call(&mut backend, "stream_next");
    assert_eq!(
        backend
            .request_authority(session, job, number(&next, "request"))
            .unwrap(),
        (1, 1, false)
    );
    backend
        .reply(
            number(&next, "request"),
            Ok(json!({"done":false,"value":4})),
        )
        .unwrap();
    assert!(backend
        .request_authority(session, job, number(&next, "request"))
        .is_err());
    let close = expect_call(&mut backend, "stream_close");
    assert_eq!(close["stream"], "js1");
    backend
        .reply(number(&close, "request"), Ok(json!({"done":true})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["value"], 4);
    assert!(backend.authority(session, job).is_err());
}
#[test]
fn dropped_pending_next_starts_return_before_waiting_for_rpc_completion() {
    let (mut backend, session, _) = stream_ready();
    let (job, open) = foreign_open(&mut backend, session, "dropNext");
    backend
        .reply(number(&open, "request"), Ok(json!({"stream":"js1"})))
        .unwrap();
    let next = expect_call(&mut backend, "stream_next");
    let close = expect_call(&mut backend, "stream_close");
    assert_eq!(
        backend
            .request_authority(session, job, number(&next, "request"))
            .unwrap(),
        (1, 1, false)
    );
    assert_eq!(
        backend
            .request_authority(session, job, number(&close, "request"))
            .unwrap(),
        (1, 1, true)
    );
    backend
        .reply(number(&close, "request"), Ok(json!({"done":true})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"], json!([]));
    assert!(backend.cleanup(session).is_err());
    backend
        .reply(number(&next, "request"), Ok(json!({"done":true})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["value"], "dropped");
}
#[test]
fn cancellation_returns_foreign_stream_while_main_future_is_waiting_for_next() {
    let (mut backend, session, _) = stream_ready();
    let (job, open) = foreign_open(&mut backend, session, "wait");
    backend
        .reply(number(&open, "request"), Ok(json!({"stream":"js1"})))
        .unwrap();
    let next = expect_call(&mut backend, "stream_next");
    backend.cancel_job(job).unwrap();
    let close = expect_call(&mut backend, "stream_close");
    assert_eq!(close["restoring"], true);
    assert_eq!(backend.poll()["jobs"], json!([]));
    backend
        .reply(number(&close, "request"), Ok(json!({"done":true})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"], json!([]));
    backend
        .reply(number(&next, "request"), Ok(json!({"done":true})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["job"], job.to_string());
}
#[test]
fn late_foreign_acquisition_is_journaled_before_cancelled_job_can_complete() {
    for mode in ["wait", "lateOpen"] {
        let (mut backend, session, _) = stream_ready();
        let (job, open) = foreign_open(&mut backend, session, mode);
        backend.cancel_job(job).unwrap();
        assert_eq!(backend.poll()["jobs"], json!([]));
        backend
            .reply(number(&open, "request"), Ok(json!({"stream":"late"})))
            .unwrap();
        let close = expect_call(&mut backend, "stream_close");
        backend
            .reply(number(&close, "request"), Ok(json!({"done":true})))
            .unwrap();
        let result = backend.poll();
        assert_eq!(result["jobs"][0]["job"], job.to_string());
    }
}
#[test]
fn failed_foreign_return_remains_owned_and_cleanup_retries_before_instance_cleanup() {
    let (mut backend, session, _) = stream_ready();
    let (_, open) = foreign_open(&mut backend, session, "wait");
    backend
        .reply(number(&open, "request"), Ok(json!({"stream":"js1"})))
        .unwrap();
    let next = expect_call(&mut backend, "stream_next");
    backend
        .reply(number(&next, "request"), Ok(json!({"done":true})))
        .unwrap();
    let close = expect_call(&mut backend, "stream_close");
    backend
        .reply(number(&close, "request"), Ok(json!({"done":false})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["error"], "StreamCloseIncomplete");
    assert!(backend.release(session).is_err());
    let cleanup = backend.cleanup(session).unwrap();
    let orphan = expect_call(&mut backend, "close_orphans");
    assert_eq!(orphan["restoring"], true);
    backend
        .reply(number(&orphan, "request"), Ok(Value::Null))
        .unwrap();
    let close = expect_call(&mut backend, "stream_close");
    backend
        .reply(number(&close, "request"), Ok(json!({"done":true})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["job"], cleanup["job"]);
    backend.release(session).unwrap();
}

#[derive(Default)]
struct ObjectData {
    owned: std::sync::atomic::AtomicBool,
    closes: AtomicUsize,
}
struct ObjectFactory(Arc<TestObject>);
struct ObjectInstance(Arc<TestObject>);
struct TestObject(Arc<ObjectData>);
impl PluginObject for TestObject {
    fn descriptor(&self) -> ObjectDescriptor {
        ObjectDescriptor::callback(
            "test.Callback",
            if self.0.owned.load(Ordering::Relaxed) {
                ObjectOwnership::Owned
            } else {
                ObjectOwnership::Borrowed
            },
        )
        .unwrap()
    }
    fn call(&self, ctx: PluginContext, _: &str, args: Value) -> PluginFuture {
        Box::pin(async move { ctx.call("input", "query", args).await })
    }
    fn close(&self, _: PluginContext) -> PluginFuture {
        let attempt = self.0.closes.fetch_add(1, Ordering::Relaxed);
        Box::pin(async move {
            if attempt == 0 {
                Err("retry object close".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
}
impl PluginFactory for ObjectFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        let mut descriptor = ReadyFactory.descriptor();
        descriptor.services[0].methods.extend([
            MethodDescriptor {
                name: "object".into(),
                kind: MethodKind::Object,
            },
            MethodDescriptor {
                name: "foreignObject".into(),
                kind: MethodKind::Async,
            },
        ]);
        descriptor
    }
    fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(ObjectInstance(self.0.clone())))
    }
}
impl PluginInstance for ObjectInstance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        ReadyInstance.setup(ctx)
    }
    fn open_object(&self, _: &str, _: &str, _: Value) -> PluginResult<Arc<dyn PluginObject>> {
        Ok(self.0.clone())
    }
    fn call_async(&self, ctx: PluginContext, _: &str, _: &str, args: Value) -> PluginFuture {
        Box::pin(async move {
            if args[0] == "parallelOpen" {
                let mut first = Box::pin(ctx.open_object("input", "object", json!(["first"])));
                let mut second = Box::pin(ctx.open_object("input", "object", json!(["second"])));
                let (mut a, mut b) = (false, false);
                return std::future::poll_fn(|cx| {
                    if !a {
                        if let Poll::Ready(result) = first.as_mut().poll(cx) {
                            result?;
                            a = true;
                        }
                    }
                    if !b {
                        if let Poll::Ready(result) = second.as_mut().poll(cx) {
                            result?;
                            b = true;
                        }
                    }
                    if a && b {
                        Poll::Ready(Ok(Value::Null))
                    } else {
                        Poll::Pending
                    }
                })
                .await;
            }
            if args[0] == "late" {
                let mut open = Box::pin(ctx.open_object("input", "object", json!([])));
                std::future::poll_fn(|cx| {
                    assert!(open.as_mut().poll(cx).is_pending());
                    Poll::Ready(())
                })
                .await;
                return Ok(Value::Null);
            }
            if args[0] == "callback" {
                let callback: JsCallback = ctx.open_callback("input", "object", json!([])).await?;
                assert_eq!(callback.descriptor().type_name(), "test.Callback");
                assert_eq!(callback.descriptor().methods(), ["call"]);
                assert_eq!(callback.descriptor().ownership(), ObjectOwnership::Owned);
                let value = callback.invoke(json!([7])).await?;
                callback.close().await?;
                return Ok(value);
            }
            let first: JsObject = ctx.open_object("input", "object", json!(["first"])).await?;
            if args[0] == "lateSecond" {
                let mut second = Box::pin(ctx.open_object("input", "object", json!(["second"])));
                std::future::poll_fn(|cx| {
                    assert!(second.as_mut().poll(cx).is_pending());
                    Poll::Ready(())
                })
                .await;
                return Ok(Value::Null);
            }
            if args[0] == "busyClose" {
                let mut call = Box::pin(first.call("call", json!([1])));
                std::future::poll_fn(|cx| {
                    assert!(call.as_mut().poll(cx).is_pending());
                    Poll::Ready(())
                })
                .await;
                let clone = first.clone();
                assert_eq!(clone.close().await, Err("ObjectBusy".into()));
                call.await?;
                // Busy is side-effect free: this second admission must work.
                let value = first.call("call", json!([2])).await?;
                first.close().await?;
                return Ok(value);
            }
            if args[0] == "concurrentClose" {
                let mut close = Box::pin(first.close());
                std::future::poll_fn(|cx| {
                    assert!(close.as_mut().poll(cx).is_pending());
                    Poll::Ready(())
                })
                .await;
                assert_eq!(first.close().await, Err("ObjectBusy".into()));
                close.await?;
                return Ok(json!("closed"));
            }
            if args[0] == "two" {
                let _second = ctx
                    .open_object("input", "object", json!(["second"]))
                    .await?;
                return Ok(Value::Null);
            }
            if args[0] == "dropCall" {
                let mut call = Box::pin(first.call("call", json!([9])));
                std::future::poll_fn(|cx| {
                    assert!(call.as_mut().poll(cx).is_pending());
                    Poll::Ready(())
                })
                .await;
                return Ok(json!("dropped"));
            }
            first.call("call", json!([9])).await
        })
    }
}
fn object_ready(owned: bool) -> (plugin::Backend, u64, Arc<ObjectData>) {
    let data = Arc::new(ObjectData::default());
    data.owned.store(owned, Ordering::Relaxed);
    let mut registry = FactoryRegistry::new();
    registry
        .register(ObjectFactory(Arc::new(TestObject(data.clone()))))
        .unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let start = backend.start(1, 1, "test", Value::Null).unwrap();
    let session = number(&start, "session");
    let call = expect_call(&mut backend, "provide");
    backend
        .reply(
            number(&call, "request"),
            Ok(json!({"publication":"3","port":{"key":"4","realm":"0"}})),
        )
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    (backend, session, data)
}
fn object_reply(backend: &mut plugin::Backend, open: &Value, id: &str) {
    backend.reply(number(open, "request"), Ok(json!({"object":id,"descriptor":{"typeName":"test.Callback","methods":["call"],"ownership":"owned"}}))).unwrap();
}
fn foreign_object(backend: &mut plugin::Backend, session: u64, mode: &str) -> (u64, Value) {
    let job = number(
        &backend
            .call(
                session,
                "service",
                "foreignObject",
                json!([mode]),
                false,
                false,
            )
            .unwrap(),
        "job",
    );
    (job, expect_call(backend, "object_open"))
}
#[test]
fn object_descriptors_validate_before_acquisition_and_borrowed_leases_do_not_destruct() {
    assert!(ObjectDescriptor::new("", ["call"], ObjectOwnership::Owned).is_err());
    assert!(ObjectDescriptor::new("type", ["call", "call"], ObjectOwnership::Owned).is_err());
    let (mut backend, session, data) = object_ready(false);
    let a = number(
        &backend
            .call(session, "service", "object", json!([]), false, false)
            .unwrap(),
        "object",
    );
    let b = number(
        &backend
            .call(session, "service", "object", json!([]), false, false)
            .unwrap(),
        "object",
    );
    data.owned.store(true, Ordering::Relaxed);
    assert!(backend
        .call(session, "service", "object", json!([]), false, false)
        .is_err());
    backend.object_close(session, a).unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    backend.object_close(session, b).unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    assert_eq!(data.closes.load(Ordering::Relaxed), 0);
    let owned = number(
        &backend
            .call(session, "service", "object", json!([]), false, false)
            .unwrap(),
        "object",
    );
    assert!(backend
        .call(session, "service", "object", json!([]), false, false)
        .is_err());
    backend.object_close(session, owned).unwrap();
    backend.poll();
    backend.object_close(session, owned).unwrap();
    backend.poll();
    // The factory retains the same Arc: it cannot be re-owned after close.
    assert!(backend
        .call(session, "service", "object", json!([]), false, false)
        .is_err());
    data.owned.store(false, Ordering::Relaxed);
    assert!(backend
        .call(session, "service", "object", json!([]), false, false)
        .is_err());
}
#[test]
fn owned_object_close_joins_all_calls_and_retains_failed_resource_for_retry() {
    let (mut backend, session, data) = object_ready(true);
    let object = number(
        &backend
            .call(session, "service", "object", json!([]), false, false)
            .unwrap(),
        "object",
    );
    backend.bind_object(object, Some((8, 2))).unwrap();
    assert!(backend
        .object_binding(session, object, Some((8, 3)))
        .is_err());
    assert!(backend
        .object_binding(session + 1, object, Some((8, 2)))
        .is_err());
    assert_eq!(
        backend
            .object_binding(session, object, Some((8, 2)))
            .unwrap()
            .1,
        3
    );
    assert!(backend
        .object_call(session, object, "missing", json!([]), false, false)
        .is_err());
    backend
        .object_call(session, object, "call", json!([1]), false, false)
        .unwrap();
    let first = expect_call(&mut backend, "call");
    backend
        .object_call(session, object, "call", json!([2]), false, false)
        .unwrap();
    let second = expect_call(&mut backend, "call");
    let close = backend.object_close(session, object).unwrap();
    assert_eq!(backend.object_close(session, object).unwrap(), close);
    assert!(backend.cancel_job(number(&close, "job")).is_err());
    assert!(backend
        .object_call(session, object, "call", json!([]), true, false)
        .is_err());
    assert_eq!(backend.poll()["jobs"], json!([]));
    assert_eq!(data.closes.load(Ordering::Relaxed), 0);
    backend
        .reply(number(&first, "request"), Ok(json!(1)))
        .unwrap();
    backend.poll();
    assert_eq!(data.closes.load(Ordering::Relaxed), 0);
    backend
        .reply(number(&second, "request"), Ok(json!(2)))
        .unwrap();
    backend.poll();
    assert_eq!(backend.poll()["jobs"][0]["success"], false);
    assert!(backend.cleanup(session).is_err());
    backend.object_close(session, object).unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    assert_eq!(
        backend.object_close(session, object).unwrap()["closed"],
        true
    );
}
#[test]
fn js_callback_is_explicit_and_close_has_its_own_restoration_authority() {
    let (mut backend, session, _) = object_ready(false);
    let (job, open) = foreign_object(&mut backend, session, "callback");
    object_reply(&mut backend, &open, "callback");
    let call = expect_call(&mut backend, "object_call");
    assert_eq!(call["object"], "callback");
    assert_eq!(call["method"], "call");
    backend
        .reply(number(&call, "request"), Ok(json!(21)))
        .unwrap();
    let close = expect_call(&mut backend, "object_close");
    assert_eq!(
        backend
            .request_authority(session, job, number(&close, "request"))
            .unwrap(),
        (1, 1, true)
    );
    backend
        .reply(number(&close, "request"), Ok(json!({"closed":true})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["value"], 21);
}
#[test]
fn foreign_object_finalization_and_cancellation_never_destroy_a_pending_call() {
    for mode in ["dropCall", "wait"] {
        let (mut backend, session, _) = object_ready(false);
        let (job, open) = foreign_object(&mut backend, session, mode);
        object_reply(&mut backend, &open, "object");
        let call = expect_call(&mut backend, "object_call");
        backend.cancel_job(job).unwrap();
        let polled = backend.poll();
        assert_eq!(polled["calls"], json!([]));
        assert_eq!(polled["jobs"], json!([]));
        assert!(backend.cleanup(session).is_err());
        backend
            .reply(number(&call, "request"), Ok(json!(42)))
            .unwrap();
        let close = expect_call(&mut backend, "object_close");
        backend
            .reply(number(&close, "request"), Ok(json!({"closed":true})))
            .unwrap();
        assert_eq!(backend.poll()["jobs"][0]["job"], job.to_string());
    }
}
#[test]
fn foreign_objects_finalize_in_reverse_acquisition_order_and_stop_on_failure() {
    let (mut backend, session, _) = object_ready(false);
    let (_, first) = foreign_object(&mut backend, session, "two");
    object_reply(&mut backend, &first, "first");
    let second = expect_call(&mut backend, "object_open");
    object_reply(&mut backend, &second, "second");
    let close = expect_call(&mut backend, "object_close");
    assert_eq!(close["object"], "second");
    backend
        .reply(number(&close, "request"), Err("retry second".into()))
        .unwrap();
    let failed = backend.poll();
    assert_eq!(failed["jobs"][0]["success"], false);
    assert_eq!(failed["calls"], json!([]));
    backend.cleanup(session).unwrap();
    let orphan = expect_call(&mut backend, "close_orphans");
    backend
        .reply(number(&orphan, "request"), Ok(Value::Null))
        .unwrap();
    for id in ["second", "first"] {
        let close = expect_call(&mut backend, "object_close");
        assert_eq!(close["object"], id);
        backend
            .reply(number(&close, "request"), Ok(json!({"closed":true})))
            .unwrap();
    }
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    backend.release(session).unwrap();
}
#[test]
fn late_object_acquisition_is_registered_and_closed_before_action_completion() {
    let (mut backend, session, _) = object_ready(false);
    let (job, open) = foreign_object(&mut backend, session, "late");
    backend.cancel_job(job).unwrap();
    assert_eq!(backend.poll()["jobs"], json!([]));
    object_reply(&mut backend, &open, "late");
    let close = expect_call(&mut backend, "object_close");
    backend
        .reply(number(&close, "request"), Ok(json!({"closed":true})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["job"], job.to_string());
}

#[test]
fn concurrent_js_object_close_does_not_implicitly_retry_the_first_attempt() {
    let (mut backend, session, _) = object_ready(false);
    let (_, open) = foreign_object(&mut backend, session, "concurrentClose");
    object_reply(&mut backend, &open, "one");
    let close = expect_call(&mut backend, "object_close");
    backend
        .reply(number(&close, "request"), Err("close failed".into()))
        .unwrap();
    assert_eq!(backend.poll()["jobs"], json!([]));
    let result = backend.poll();
    assert_eq!(result["jobs"][0]["success"], false);
    assert_eq!(result["calls"], json!([]));
}

#[test]
fn pending_object_acquisition_lands_before_lifo_finalization_begins() {
    let (mut backend, session, _) = object_ready(false);
    let (_, open) = foreign_object(&mut backend, session, "lateSecond");
    object_reply(&mut backend, &open, "first");
    let second = expect_call(&mut backend, "object_open");
    let polled = backend.poll();
    assert_eq!(polled["calls"], json!([]));
    assert_eq!(polled["jobs"], json!([]));
    object_reply(&mut backend, &second, "second");
    for object in ["second", "first"] {
        let close = expect_call(&mut backend, "object_close");
        assert_eq!(close["object"], object);
        backend
            .reply(number(&close, "request"), Ok(json!({"closed":true})))
            .unwrap();
    }
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
}

#[test]
fn foreign_object_lifo_uses_acquisition_completion_not_request_order() {
    let (mut backend, session, _) = object_ready(false);
    backend
        .call(
            session,
            "service",
            "foreignObject",
            json!(["parallelOpen"]),
            false,
            false,
        )
        .unwrap();
    let calls = backend.poll()["calls"].as_array().unwrap().clone();
    assert_eq!(calls.len(), 2);
    object_reply(&mut backend, &calls[1], "second");
    assert_eq!(backend.poll()["jobs"], json!([]));
    object_reply(&mut backend, &calls[0], "first");
    for object in ["first", "second"] {
        let close = expect_call(&mut backend, "object_close");
        assert_eq!(close["object"], object);
        backend
            .reply(number(&close, "request"), Ok(json!({"closed":true})))
            .unwrap();
    }
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
}

#[test]
fn explicit_foreign_object_close_rejects_live_calls_without_changing_admission() {
    let (mut backend, session, _) = object_ready(false);
    let (_, open) = foreign_object(&mut backend, session, "busyClose");
    object_reply(&mut backend, &open, "object");
    let first = expect_call(&mut backend, "object_call");
    let polled = backend.poll();
    assert_eq!(polled["calls"], json!([]));
    assert_eq!(polled["jobs"], json!([]));
    backend
        .reply(number(&first, "request"), Ok(json!(1)))
        .unwrap();
    let second = expect_call(&mut backend, "object_call");
    assert_eq!(second["args"], json!([2]));
    backend
        .reply(number(&second, "request"), Ok(json!(2)))
        .unwrap();
    let close = expect_call(&mut backend, "object_close");
    backend
        .reply(number(&close, "request"), Ok(json!({"closed":true})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["value"], 2);
}

#[test]
fn explicit_foreign_stream_close_rejects_live_next_without_changing_admission() {
    let (mut backend, session, _) = stream_ready();
    let (_, open) = foreign_open(&mut backend, session, "busyClose");
    backend
        .reply(number(&open, "request"), Ok(json!({"stream":"one"})))
        .unwrap();
    let first = expect_call(&mut backend, "stream_next");
    let polled = backend.poll();
    assert_eq!(polled["calls"], json!([]));
    assert_eq!(polled["jobs"], json!([]));
    backend
        .reply(
            number(&first, "request"),
            Ok(json!({"done":false,"value":7})),
        )
        .unwrap();
    let second = expect_call(&mut backend, "stream_next");
    backend
        .reply(number(&second, "request"), Ok(json!({"done":true})))
        .unwrap();
    let close = expect_call(&mut backend, "stream_close");
    backend
        .reply(number(&close, "request"), Ok(json!({"done":true})))
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["value"], 7);
}

// This slice deliberately uses real cordis::Plugin closures and SharedSlots.
// Driver ticket admission is tested at the NAPI boundary, not fabricated here.
#[derive(Default)]
struct TypedCounterView {
    observed: Option<Arc<Mutex<Option<Arc<AtomicUsize>>>>>,
}
impl TypedService<AtomicUsize> for TypedCounterView {
    fn methods(&self) -> Vec<MethodDescriptor> {
        vec![MethodDescriptor {
            name: "read".into(),
            kind: MethodKind::Sync,
        }]
    }
    fn call_sync(&self, value: Arc<AtomicUsize>, method: &str, _: Value) -> PluginResult<Value> {
        assert_eq!(method, "read");
        if let Some(observed) = &self.observed {
            *observed.lock().unwrap() = Some(value.clone());
        }
        Ok(json!(value.load(Ordering::SeqCst)))
    }
}
fn typed_port(key: u64, realm: u64) -> cordis_driver::ServicePort {
    cordis_driver::ServicePort { key, realm }
}
fn typed_ports(
    entries: &[(&str, cordis_driver::ServicePort)],
) -> std::collections::BTreeMap<String, cordis_driver::ServicePort> {
    entries
        .iter()
        .map(|(name, port)| ((*name).into(), *port))
        .collect()
}
fn typed_publish(
    backend: &mut plugin::Backend,
    start: &Value,
    publication: usize,
    port: cordis_driver::ServicePort,
) -> u64 {
    let call = expect_call(backend, "provide");
    assert_eq!(call["session"], start["session"]);
    backend
        .reply(
            number(&call, "request"),
            Ok(json!({
                "publication": publication.to_string(), "port": port,
            })),
        )
        .unwrap();
    let result = backend.poll();
    assert_eq!(result["calls"], json!([]));
    assert_eq!(result["jobs"].as_array().unwrap().len(), 1);
    assert_eq!(result["jobs"][0]["job"], start["job"]);
    assert_eq!(result["jobs"][0]["success"], true, "{result}");
    number(start, "session")
}
fn typed_cleanup_result(backend: &mut plugin::Backend, session: u64) -> Value {
    let start = backend.cleanup(session).unwrap();
    let call = expect_call(backend, "close_orphans");
    backend
        .reply(number(&call, "request"), Ok(Value::Null))
        .unwrap();
    let result = backend.poll();
    assert_eq!(result["calls"], json!([]));
    assert_eq!(result["jobs"].as_array().unwrap().len(), 1);
    assert_eq!(result["jobs"][0]["job"], start["job"]);
    result["jobs"][0].clone()
}
fn typed_release(backend: &mut plugin::Backend, session: u64) {
    backend.cancel(session).unwrap();
    assert_eq!(typed_cleanup_result(backend, session)["success"], true);
    backend.release(session).unwrap();
}

#[test]
fn typed_registration_rejects_ambiguous_service_keys_names_and_descriptors() {
    let one = cordis::ServiceKey::<AtomicUsize>::new("same diagnostic name");
    let two = cordis::ServiceKey::<AtomicUsize>::new("same diagnostic name");
    let blank = || TypedFactory::new("typed", |_| Ok(cordis::Plugin::new("blank", |_| Ok(()))));
    for factory in [
        blank().requires(one, "a").requires(one, "b"),
        blank().requires(one, "a").requires(two, "a"),
        blank().requires(one, ""),
        blank()
            .requires(one, "a")
            .provides(one, "b", TypedCounterView::default()),
    ] {
        assert_eq!(
            FactoryRegistry::new().register_typed(factory),
            Err("DuplicateTypedBinding".into())
        );
    }
    struct DuplicateMethods;
    impl TypedService<AtomicUsize> for DuplicateMethods {
        fn methods(&self) -> Vec<MethodDescriptor> {
            vec![
                MethodDescriptor {
                    name: "read".into(),
                    kind: MethodKind::Sync
                };
                2
            ]
        }
    }
    assert_eq!(
        FactoryRegistry::new().register_typed(blank().provides(one, "a", DuplicateMethods)),
        Err("DuplicateOrEmptyMethod".into())
    );
    let mut registry = FactoryRegistry::new();
    registry.register_typed(blank()).unwrap();
    assert_eq!(
        registry.register_typed(blank()),
        Err("DuplicateOrEmptyFactory".into())
    );
}

#[test]
fn typed_descriptors_require_an_exact_non_aliasing_port_map() {
    let input = cordis::ServiceKey::<AtomicUsize>::new("input");
    let output = cordis::ServiceKey::<AtomicUsize>::new("output");
    let mut registry = FactoryRegistry::new();
    registry.register(ReadyFactory).unwrap();
    registry
        .register_typed(
            TypedFactory::new("typed", move |_| {
                Ok(cordis::Plugin::new("mapped", |_| Ok(()))
                    .requires(input)
                    .provides(output))
            })
            .requires(input, "in")
            .provides(output, "out", TypedCounterView::default()),
        )
        .unwrap();
    let backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let good = typed_ports(&[("in", typed_port(400, 20)), ("out", typed_port(401, 20))]);
    let descriptor = backend.typed_descriptor("typed", &good).unwrap().unwrap();
    assert_eq!(descriptor.inject, ["in"]);
    assert_eq!(descriptor.services[0].name, "out");
    assert!(backend.typed_descriptor("test", &good).unwrap().is_none());
    for bad in [
        typed_ports(&[("in", typed_port(400, 20))]),
        typed_ports(&[("in", typed_port(400, 20)), ("other", typed_port(401, 20))]),
        typed_ports(&[
            ("in", typed_port(400, 20)),
            ("out", typed_port(401, 20)),
            ("extra", typed_port(402, 20)),
        ]),
    ] {
        assert!(backend.typed_descriptor("typed", &bad).is_err());
    }
    let aliased = typed_ports(&[("in", typed_port(400, 20)), ("out", typed_port(400, 20))]);
    assert!(backend.typed_descriptor("typed", &aliased).is_err());
}

#[test]
fn typed_import_and_json_view_share_the_providers_original_arc() {
    let key = cordis::ServiceKey::<AtomicUsize>::new("counter");
    let supplied = Arc::new(Mutex::new(None));
    let consumed = Arc::new(Mutex::new(None));
    let viewed = Arc::new(Mutex::new(None));
    let cleanup_reads = Arc::new(Mutex::new(Vec::new()));
    let mut registry = FactoryRegistry::new();
    let record = supplied.clone();
    registry
        .register_typed(
            TypedFactory::new("provider", move |_| {
                let record = record.clone();
                Ok(cordis::Plugin::new("original provider", move |setup| {
                    *record.lock().unwrap() = Some(setup.provide(key, AtomicUsize::new(41))?);
                    Ok(())
                })
                .provides(key))
            })
            .provides(
                key,
                "counter",
                TypedCounterView {
                    observed: Some(viewed.clone()),
                },
            ),
        )
        .unwrap();
    let record = consumed.clone();
    let reads = cleanup_reads.clone();
    registry
        .register_typed(
            TypedFactory::new("consumer", move |_| {
                let record = record.clone();
                let reads = reads.clone();
                Ok(cordis::Plugin::new("original consumer", move |setup| {
                    let value = setup.get(key)?;
                    value.fetch_add(1, Ordering::SeqCst);
                    *record.lock().unwrap() = Some(value);
                    let escaped = setup.to_async();
                    let reads = reads.clone();
                    setup.on_cleanup(move || {
                        reads
                            .lock()
                            .unwrap()
                            .push(escaped.get(key)?.load(Ordering::SeqCst));
                        Ok(())
                    });
                    Ok(())
                })
                .requires(key))
            })
            .requires(key, "counter"),
        )
        .unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let port = typed_port(100, 901);
    let ports = typed_ports(&[("counter", port)]);
    let provider = backend
        .start_resolved(11, 1, "provider", Value::Null, ports.clone(), vec![])
        .unwrap();
    let provider_session = typed_publish(&mut backend, &provider, 40, port);
    let consumer = backend
        .start_resolved(
            12,
            1,
            "consumer",
            Value::Null,
            ports,
            vec![ResolvedImport {
                name: "counter".into(),
                port,
                owner: 11,
                publication: 40,
            }],
        )
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    assert_eq!(
        backend
            .call(provider_session, "counter", "read", json!([]), false, false)
            .unwrap()["value"],
        42
    );
    let supplied = supplied.lock().unwrap().clone().unwrap();
    assert!(Arc::ptr_eq(
        &supplied,
        consumed.lock().unwrap().as_ref().unwrap()
    ));
    assert!(Arc::ptr_eq(
        &supplied,
        viewed.lock().unwrap().as_ref().unwrap()
    ));
    // The external Driver authorizes cleanup order. Cancelling visibility alone
    // must not erase a committed slot needed by the consumer's inverse.
    backend.cancel(provider_session).unwrap();
    typed_release(&mut backend, number(&consumer, "session"));
    assert_eq!(*cleanup_reads.lock().unwrap(), [42]);
    typed_release(&mut backend, provider_session);
}

#[test]
fn typed_imports_match_exact_publication_owner_port_and_real_key_identity() {
    let key = cordis::ServiceKey::<AtomicUsize>::new("counter");
    let other_key = cordis::ServiceKey::<AtomicUsize>::new("counter");
    let wrong_type = cordis::ServiceKey::<String>::new("counter");
    let mut registry = FactoryRegistry::new();
    registry
        .register_typed(
            TypedFactory::new("provider", move |_| {
                Ok(cordis::Plugin::new("provider", move |setup| {
                    setup.provide(key, AtomicUsize::new(1))?;
                    Ok(())
                })
                .provides(key))
            })
            .provides(key, "counter", TypedCounterView::default()),
        )
        .unwrap();
    for (name, import_key) in [("consumer", key), ("other-key", other_key)] {
        registry
            .register_typed(
                TypedFactory::new(name, move |_| {
                    Ok(cordis::Plugin::new("consumer", move |setup| {
                        setup.get(import_key)?;
                        Ok(())
                    })
                    .requires(import_key))
                })
                .requires(import_key, "counter"),
            )
            .unwrap();
    }
    registry
        .register_typed(
            TypedFactory::new("wrong-type", move |_| {
                Ok(cordis::Plugin::new("consumer", |_| Ok(())).requires(wrong_type))
            })
            .requires(wrong_type, "counter"),
        )
        .unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let port = typed_port(50, 60);
    let ports = typed_ports(&[("counter", port)]);
    let started = backend
        .start_resolved(1, 1, "provider", Value::Null, ports.clone(), vec![])
        .unwrap();
    let session = typed_publish(&mut backend, &started, 70, port);
    for (owner, publication, candidate_port) in [
        (2, 70, port),
        (1, 71, port),
        (1, 70, typed_port(51, 60)),
        (1, 70, typed_port(50, 61)),
    ] {
        assert!(backend
            .start_resolved(
                10,
                1,
                "consumer",
                Value::Null,
                ports.clone(),
                vec![ResolvedImport {
                    name: "counter".into(),
                    port: candidate_port,
                    owner,
                    publication,
                }]
            )
            .is_err());
    }
    for factory in ["other-key", "wrong-type"] {
        assert_eq!(
            backend.start_resolved(
                10,
                1,
                factory,
                Value::Null,
                ports.clone(),
                vec![ResolvedImport {
                    name: "counter".into(),
                    port,
                    owner: 1,
                    publication: 70,
                }]
            ),
            Err("TypedServiceMismatch".into())
        );
    }
    typed_release(&mut backend, session);
    // Retaining old resolution metadata cannot resurrect the released episode.
    assert!(backend
        .start_resolved(
            10,
            1,
            "consumer",
            Value::Null,
            ports,
            vec![ResolvedImport {
                name: "counter".into(),
                port,
                owner: 1,
                publication: 70,
            }]
        )
        .is_err());
}

#[test]
fn typed_publication_reply_must_confirm_the_mapped_port() {
    let key = cordis::ServiceKey::<AtomicUsize>::new("counter");
    let cleanups = Arc::new(AtomicUsize::new(0));
    let observed = cleanups.clone();
    let mut registry = FactoryRegistry::new();
    registry
        .register_typed(
            TypedFactory::new("provider", move |_| {
                let observed = observed.clone();
                Ok(cordis::Plugin::new("provider", move |setup| {
                    setup.provide(key, AtomicUsize::new(1))?;
                    let observed = observed.clone();
                    setup.on_cleanup(move || {
                        observed.fetch_add(1, Ordering::SeqCst);
                        Ok(())
                    });
                    Ok(())
                })
                .provides(key))
            })
            .provides(key, "counter", TypedCounterView::default()),
        )
        .unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let start = backend
        .start_resolved(
            1,
            1,
            "provider",
            Value::Null,
            typed_ports(&[("counter", typed_port(4, 5))]),
            vec![],
        )
        .unwrap();
    let call = expect_call(&mut backend, "provide");
    backend
        .reply(
            number(&call, "request"),
            Ok(json!({"publication":"7","port":{"key":"4","realm":"6"}})),
        )
        .unwrap();
    let result = backend.poll();
    assert_eq!(result["jobs"][0]["success"], false);
    assert_eq!(result["jobs"][0]["error"], "TypedPublicationPortMismatch");
    let session = number(&start, "session");
    assert!(backend.binding(session, "counter").is_err());
    typed_release(&mut backend, session);
    assert_eq!(cleanups.load(Ordering::SeqCst), 1);
}

#[test]
fn typed_restart_reuses_fnmut_but_other_fibers_and_changed_definitions_do_not() {
    let key = cordis::ServiceKey::<AtomicUsize>::new("counter");
    let made = Arc::new(AtomicUsize::new(0));
    let make_factory = |name: &str| {
        let made = made.clone();
        TypedFactory::new(name, move |_| {
            made.fetch_add(1, Ordering::SeqCst);
            let mut generation_count = 0;
            Ok(cordis::Plugin::new("mutable recipe", move |setup| {
                generation_count += 1;
                setup.provide(key, AtomicUsize::new(generation_count))?;
                Ok(())
            })
            .provides(key))
        })
        .provides(key, "counter", TypedCounterView::default())
    };
    let mut registry = FactoryRegistry::new();
    registry.register_typed(make_factory("typed")).unwrap();
    registry.register_typed(make_factory("other")).unwrap();
    registry.register(ReadyFactory).unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let port = typed_port(1, 2);
    let ports = typed_ports(&[("counter", port)]);
    for (owner, generation, expected) in [(1, 1, 1), (1, 2, 2), (2, 1, 1)] {
        let start = backend
            .start_resolved(
                owner,
                generation,
                "typed",
                json!({"n":1}),
                ports.clone(),
                vec![],
            )
            .unwrap();
        let session = typed_publish(&mut backend, &start, generation as usize + owner * 10, port);
        assert_eq!(
            backend
                .call(session, "counter", "read", json!([]), false, false)
                .unwrap()["value"],
            expected
        );
        assert!(backend.forget_typed(owner).is_err());
        typed_release(&mut backend, session);
        if owner == 1 && generation == 1 {
            for (factory, config, candidate_ports) in [
                ("typed", json!({"n":2}), ports.clone()),
                ("other", json!({"n":1}), ports.clone()),
                (
                    "typed",
                    json!({"n":1}),
                    typed_ports(&[("counter", typed_port(1, 3))]),
                ),
                ("test", json!({"n":1}), Default::default()),
            ] {
                assert_eq!(
                    backend.start_resolved(1, 2, factory, config, candidate_ports, vec![]),
                    Err("TypedMountDefinitionChanged".into())
                );
            }
        }
    }
    assert_eq!(made.load(Ordering::SeqCst), 2);
    backend.forget_typed(1).unwrap();
    backend.forget_typed(2).unwrap();
}

#[test]
fn typed_setup_failure_keeps_its_registered_inverse_and_withholds_publication() {
    for panic_setup in [false, true] {
        let key = cordis::ServiceKey::<AtomicUsize>::new("counter");
        let cleanups = Arc::new(AtomicUsize::new(0));
        let observed = cleanups.clone();
        let mut registry = FactoryRegistry::new();
        registry
            .register_typed(
                TypedFactory::new("typed", move |_| {
                    let observed = observed.clone();
                    Ok(cordis::Plugin::new("partial", move |setup| {
                        setup.provide(key, AtomicUsize::new(1))?;
                        let observed = observed.clone();
                        setup.on_cleanup(move || {
                            observed.fetch_add(1, Ordering::SeqCst);
                            Ok(())
                        });
                        if panic_setup {
                            panic!("typed setup panic");
                        }
                        Err("typed setup failure".into())
                    })
                    .provides(key))
                })
                .provides(key, "counter", TypedCounterView::default()),
            )
            .unwrap();
        let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
        let start = backend
            .start_resolved(
                1,
                1,
                "typed",
                Value::Null,
                typed_ports(&[("counter", typed_port(3, 4))]),
                vec![],
            )
            .unwrap();
        let result = backend.poll();
        assert_eq!(result["calls"], json!([]));
        assert_eq!(result["jobs"][0]["success"], false);
        let session = number(&start, "session");
        assert!(backend.binding(session, "counter").is_err());
        typed_release(&mut backend, session);
        assert_eq!(cleanups.load(Ordering::SeqCst), 1);
    }
}

#[test]
fn typed_fnonce_cleanup_error_and_panic_stay_failed_across_host_retries() {
    for panic_inverse in [false, true] {
        let failed = Arc::new(AtomicUsize::new(0));
        let earlier = Arc::new(AtomicUsize::new(0));
        let fail_record = failed.clone();
        let earlier_record = earlier.clone();
        let mut registry = FactoryRegistry::new();
        registry
            .register_typed(TypedFactory::new("typed", move |_| {
                let fail_record = fail_record.clone();
                let earlier_record = earlier_record.clone();
                Ok(cordis::Plugin::new("inverse failure", move |setup| {
                    let earlier_record = earlier_record.clone();
                    setup.on_cleanup(move || {
                        earlier_record.fetch_add(1, Ordering::SeqCst);
                        Ok(())
                    });
                    let fail_record = fail_record.clone();
                    setup.on_cleanup(move || {
                        fail_record.fetch_add(1, Ordering::SeqCst);
                        if panic_inverse {
                            panic!("typed inverse panic");
                        }
                        Err("typed inverse failure".into())
                    });
                    Ok(())
                }))
            }))
            .unwrap();
        let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
        let start = backend
            .start_resolved(1, 1, "typed", Value::Null, Default::default(), vec![])
            .unwrap();
        assert_eq!(backend.poll()["jobs"][0]["success"], true);
        let session = number(&start, "session");
        backend.cancel(session).unwrap();
        let first = typed_cleanup_result(&mut backend, session);
        assert_eq!(first["success"], false);
        for _ in 0..2 {
            let retry = typed_cleanup_result(&mut backend, session);
            assert_eq!(retry["success"], false);
            assert_eq!(retry["error"], first["error"]);
        }
        assert_eq!(failed.load(Ordering::SeqCst), 1);
        assert_eq!(earlier.load(Ordering::SeqCst), 0);
        assert!(backend.release(session).is_err());
        assert!(backend.forget_typed(1).is_err());
        assert!(backend
            .start_resolved(1, 2, "typed", Value::Null, Default::default(), vec![])
            .is_err());
    }
}

#[test]
fn typed_cancel_reaches_escaped_setup_before_cleanup_and_late_inverse_lands() {
    let gate = Arc::new(AtomicUsize::new(0));
    let wake = Arc::new(Mutex::new(None::<Waker>));
    let escaped = Arc::new(Mutex::new(None::<cordis::AsyncSetup>));
    let restored = Arc::new(AtomicUsize::new(0));
    let mut registry = FactoryRegistry::new();
    let (signal, waiter, captured, cleanups) = (
        gate.clone(),
        wake.clone(),
        escaped.clone(),
        restored.clone(),
    );
    registry
        .register_typed(TypedFactory::new("typed", move |_| {
            let (signal, waiter, captured, cleanups) = (
                signal.clone(),
                waiter.clone(),
                captured.clone(),
                cleanups.clone(),
            );
            Ok(cordis::Plugin::new_async("late setup", move |setup| {
                let (signal, waiter, captured, cleanups) = (
                    signal.clone(),
                    waiter.clone(),
                    captured.clone(),
                    cleanups.clone(),
                );
                async move {
                    *captured.lock().unwrap() = Some(setup.clone());
                    std::future::poll_fn(|cx| {
                        *waiter.lock().unwrap() = Some(cx.waker().clone());
                        if signal.load(Ordering::SeqCst) == 0 {
                            Poll::Pending
                        } else {
                            Poll::Ready(())
                        }
                    })
                    .await;
                    setup.on_cleanup(move || {
                        cleanups.fetch_add(1, Ordering::SeqCst);
                        Ok(())
                    })?;
                    Ok(())
                }
            }))
        }))
        .unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let start = backend
        .start_resolved(1, 1, "typed", Value::Null, Default::default(), vec![])
        .unwrap();
    assert_eq!(backend.poll()["jobs"], json!([]));
    let session = number(&start, "session");
    let context = escaped.lock().unwrap().clone().unwrap();
    assert!(!context.is_cancelled());
    backend.cancel(session).unwrap();
    assert!(context.is_cancelled());
    assert!(context.ensure_active().is_err());
    assert!(backend.cleanup(session).is_err());
    assert_eq!(backend.poll()["jobs"], json!([]));
    gate.store(1, Ordering::SeqCst);
    wake.lock().unwrap().take().unwrap().wake();
    let result = backend.poll();
    assert_eq!(result["jobs"][0]["success"], false);
    assert_eq!(restored.load(Ordering::SeqCst), 0);
    typed_release(&mut backend, session);
    assert_eq!(restored.load(Ordering::SeqCst), 1);
    assert!(context.on_cleanup(|| Ok(())).is_err());
}

#[test]
fn typed_definition_is_retained_after_release_and_dropped_only_when_forgotten() {
    struct CapturedDrop(Arc<AtomicUsize>);
    impl Drop for CapturedDrop {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    let drops = Arc::new(AtomicUsize::new(0));
    let observed = drops.clone();
    let mut registry = FactoryRegistry::new();
    registry
        .register_typed(TypedFactory::new("typed", move |_| {
            let captured = CapturedDrop(observed.clone());
            Ok(cordis::Plugin::new("persistent", move |_| {
                let _keep_alive = &captured;
                Ok(())
            }))
        }))
        .unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let start = backend
        .start_resolved(1, 1, "typed", Value::Null, Default::default(), vec![])
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    assert!(backend.forget_typed(1).is_err());
    typed_release(&mut backend, number(&start, "session"));
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    backend.forget_typed(1).unwrap();
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    backend.forget_typed(1).unwrap();
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn typed_live_service_check_notifications_preserve_slot_and_episode_boundaries() {
    let key = cordis::ServiceKey::<AtomicUsize>::new("counter");
    let retained = Arc::new(Mutex::new(None::<cordis::AsyncSetup>));
    let saved = retained.clone();
    let mut registry = FactoryRegistry::new();
    registry
        .register_typed(
            TypedFactory::new("live", move |_| {
                let saved = saved.clone();
                Ok(cordis::Plugin::new("live", move |setup| {
                    let expected_realm = setup.context().port(key).realm;
                    setup.provide_checked(
                        key,
                        AtomicUsize::new(5),
                        move |value, context, config| {
                            context.port(key).realm == expected_realm
                                && value.load(Ordering::SeqCst)
                                    >= config["minimum"].as_u64().unwrap_or(0) as usize
                        },
                    )?;
                    *saved.lock().unwrap() = Some(setup.to_async());
                    Ok(())
                })
                .provides(key))
            })
            .provides(key, "counter", TypedCounterView::default())
            .with_service_updates(),
        )
        .unwrap();
    let wakes = Arc::new(AtomicUsize::new(0));
    let count = wakes.clone();
    let mut backend = plugin::Backend::new(
        registry,
        Arc::new(move || {
            count.fetch_add(1, Ordering::SeqCst);
        }),
    );
    let port = typed_port(100, 901);
    let ports = typed_ports(&[("counter", port)]);
    let start = backend
        .start_resolved(11, 1, "live", Value::Null, ports.clone(), vec![])
        .unwrap();
    let session = typed_publish(&mut backend, &start, 40, port);
    assert!(backend
        .typed_check(session, "counter", &ports, &json!({"minimum": 3}))
        .unwrap());
    assert!(!backend
        .typed_check(session, "counter", &ports, &json!({"minimum": 10}))
        .unwrap());
    assert!(backend
        .typed_check(
            session,
            "counter",
            &typed_ports(&[("counter", typed_port(101, 901))]),
            &Value::Null
        )
        .is_err());
    let handle = retained.lock().unwrap().clone().unwrap();
    handle.set(key, AtomicUsize::new(12)).unwrap();
    handle.refresh().unwrap(); // Coalesces with the pending slot update.
    assert!(!backend
        .typed_check(session, "counter", &ports, &json!({"minimum": 10}))
        .unwrap());
    let notification = backend.poll()["serviceNotifications"].clone();
    assert_eq!(
        notification,
        json!([{"session":session.to_string(),"generation":"1","ports":[port]}])
    );
    assert_eq!(backend.poll()["serviceNotifications"], json!([]));
    assert!(backend
        .typed_check(session, "counter", &ports, &json!({"minimum": 10}))
        .unwrap());
    assert_eq!(
        backend
            .call(session, "counter", "read", json!([]), false, false)
            .unwrap()["value"],
        12
    );
    handle.refresh().unwrap();
    backend.cancel(session).unwrap();
    assert_eq!(backend.poll()["serviceNotifications"], json!([]));
    assert!(backend
        .typed_check(session, "counter", &ports, &Value::Null)
        .is_err());
    assert!(handle.refresh().is_err());
    assert!(handle.set(key, AtomicUsize::new(99)).is_err());
    assert!(wakes.load(Ordering::SeqCst) > 0);
    typed_release(&mut backend, session);
    let next = backend
        .start_resolved(11, 2, "live", Value::Null, ports.clone(), vec![])
        .unwrap();
    let next_session = typed_publish(&mut backend, &next, 41, port);
    assert!(handle.refresh().is_err());
    assert_eq!(
        backend
            .call(next_session, "counter", "read", json!([]), false, false)
            .unwrap()["value"],
        5
    );
    typed_release(&mut backend, next_session);
}

#[test]
fn typed_dependency_configuration_is_advertised_and_matches_the_original_plugin() {
    let key = cordis::ServiceKey::<AtomicUsize>::new("configured");
    let mut registry = FactoryRegistry::new();
    registry
        .register_typed(
            TypedFactory::new("provider", move |_| {
                Ok(cordis::Plugin::new("provider", move |setup| {
                    setup.provide(key, AtomicUsize::new(7))?;
                    Ok(())
                })
                .provides(key))
            })
            .provides(key, "counter", TypedCounterView::default()),
        )
        .unwrap();
    for (name, declared, actual) in [
        (
            "configured",
            json!({"minimum":3,"policy":{"levels":[1,2]}}),
            json!({"minimum":3,"policy":{"levels":[1,2]}}),
        ),
        ("null", Value::Null, Value::Null),
        ("mismatch", json!({"minimum":3}), json!({"minimum":4})),
    ] {
        registry
            .register_typed(
                TypedFactory::new(name, move |_| {
                    Ok(cordis::Plugin::new("configured consumer", move |setup| {
                        assert_eq!(setup.get(key)?.load(Ordering::SeqCst), 7);
                        Ok(())
                    })
                    .requires_with_config(key, actual.clone()))
                })
                .requires_with_config(key, "counter", declared),
            )
            .unwrap();
    }
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let info = backend.info();
    let factories = info["factories"].as_array().unwrap();
    assert_eq!(
        factories
            .iter()
            .find(|f| f["name"] == "configured")
            .unwrap()["injectConfig"],
        json!({"counter":{"minimum":3,"policy":{"levels":[1,2]}}})
    );
    assert_eq!(
        factories.iter().find(|f| f["name"] == "null").unwrap()["injectConfig"],
        json!({"counter":null})
    );
    assert!(factories
        .iter()
        .find(|f| f["name"] == "provider")
        .unwrap()
        .get("injectConfig")
        .is_none());
    let port = typed_port(31, 9);
    let ports = typed_ports(&[("counter", port)]);
    let provider = backend
        .start_resolved(1, 1, "provider", Value::Null, ports.clone(), vec![])
        .unwrap();
    let session = typed_publish(&mut backend, &provider, 17, port);
    let import = || {
        vec![ResolvedImport {
            name: "counter".into(),
            port,
            owner: 1,
            publication: 17,
        }]
    };
    for (id, name) in [(2, "configured"), (3, "null")] {
        let started = backend
            .start_resolved(id, 1, name, Value::Null, ports.clone(), import())
            .unwrap();
        assert_eq!(backend.poll()["jobs"][0]["success"], true);
        typed_release(&mut backend, number(&started, "session"));
    }
    assert!(
        matches!(backend.start_resolved(4,1,"mismatch",Value::Null,ports,import()),Err(error) if error == "StaticInjectionConfigurationMismatch")
    );
    typed_release(&mut backend, session);
}

#[test]
fn typed_child_protocol_preserves_definition_slots_allocation_and_removal() {
    let key = cordis::ServiceKey::<AtomicUsize>::new("dynamic-counter");
    let setup_store = Arc::new(std::sync::Mutex::new(None));
    let handle_store = Arc::new(std::sync::Mutex::new(None));
    let setups = setup_store.clone();
    let handles = handle_store.clone();
    let mut registry = FactoryRegistry::new();
    registry
        .register_typed(
            TypedFactory::new("dynamic", move |_| {
                let setups = setups.clone();
                let handles = handles.clone();
                Ok(cordis::Plugin::new("owner", move |setup| {
                    *setups.lock().unwrap() = Some(setup.to_async());
                    *handles.lock().unwrap() = Some(setup.publish(key, AtomicUsize::new(17))?);
                    Ok(())
                }))
            })
            .child_service(key, "counter", TypedCounterView::default())
            .with_dynamic_children(),
        )
        .unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let anchor = "__cordis_typed_anchor_owner";
    let child_anchor = "__cordis_typed_anchor_child";
    let ports = typed_ports(&[("counter", typed_port(1, 1)), (anchor, typed_port(2, 2))]);
    let start = backend
        .start_resolved(1, 1, "dynamic", Value::Null, ports.clone(), vec![])
        .unwrap();
    let session = number(&start, "session");
    let job = number(&start, "job");
    backend.typed_bind_job_caller(job, Some((1, 1))).unwrap();
    assert!(backend.typed_job_wait_sources().is_empty()); // no child identity yet: no graph scan

    backend.typed_job_join_blocks(job, Default::default());
    let first = backend.poll();
    let child = first["children"][0]["child"].as_str().unwrap().to_string();
    assert_eq!(backend.typed_job_wait_sources()[0].1, Some((1, 1)));
    assert_eq!(backend.typed_child_owner(&child).unwrap(), (1, 1, None));
    assert!(backend
        .typed_child_aborted(&child, "before allocation".into())
        .is_err());
    let call = &first["calls"][0];
    backend
        .reply(
            number(call, "request"),
            Ok(json!({"publication":"20","port":ports[anchor]})),
        )
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    let mut child_ports = ports.clone();
    child_ports.insert(child_anchor.into(), typed_port(3, 3));
    backend
        .typed_child_mounted(&child, 2, child_ports.clone())
        .unwrap();
    assert_eq!(backend.typed_child_owner(&child).unwrap(), (1, 1, Some(2)));
    assert!(backend
        .typed_child_mounted(&child, 2, child_ports.clone())
        .is_err());
    assert!(backend
        .typed_child_rejected(&child, "too late".into())
        .is_err());
    assert_eq!(
        backend.typed_import_ports(&child, &child_ports).unwrap(),
        vec![(anchor.into(), ports[anchor])]
    );
    let child_start = backend
        .start_resolved(
            2,
            1,
            &child,
            Value::Null,
            child_ports.clone(),
            vec![ResolvedImport {
                name: anchor.into(),
                port: ports[anchor],
                owner: 1,
                publication: 20,
            }],
        )
        .unwrap();
    let child_session = number(&child_start, "session");
    for publication in [21, 22] {
        let call = expect_call(&mut backend, "provide");
        let service = call["service"].as_str().unwrap();
        backend
            .reply(
                number(&call, "request"),
                Ok(json!({"publication":publication.to_string(),"port":child_ports[service]})),
            )
            .unwrap();
    }
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    backend
        .typed_child_observed(&child, true, None, false)
        .unwrap();
    let handle = handle_store.lock().unwrap().clone().unwrap();
    assert!(handle.initialized());
    assert_eq!(
        backend
            .call(child_session, "counter", "read", json!([]), false, false)
            .unwrap()["value"],
        17
    );
    handle.set(AtomicUsize::new(23)).unwrap();
    assert_eq!(
        backend
            .call(child_session, "counter", "read", json!([]), false, false)
            .unwrap()["value"],
        23
    );
    handle.dispose();
    assert_eq!(backend.poll()["children"][0]["kind"], "retire");
    assert!(!handle.finished());
    typed_release(&mut backend, child_session);
    backend.forget_typed(2).unwrap();
    assert!(handle.finished());
    let other = setup_store
        .lock()
        .unwrap()
        .as_ref()
        .unwrap()
        .publish(key, AtomicUsize::new(4))
        .unwrap();
    let action = backend.poll()["children"][0].clone();
    backend
        .typed_child_rejected(
            action["child"].as_str().unwrap(),
            "native admission rejected".into(),
        )
        .unwrap();
    assert!(other.finished());
    assert_eq!(other.errors(), vec!["native admission rejected"]);
    assert!(backend.take_typed_failures().is_empty());
    let missing = cordis::ServiceKey::<AtomicUsize>::new("not in catalog");
    let failed = setup_store
        .lock()
        .unwrap()
        .as_ref()
        .unwrap()
        .mount(cordis::Plugin::new("bad child", |_| Ok(())).requires(missing))
        .unwrap();
    assert_eq!(backend.poll()["children"][0]["kind"], "error");
    assert!(failed.id().is_none());
    assert_eq!(
        backend.take_typed_failures(),
        vec![(session, "UnknownTypedChildService".into())]
    );
    typed_release(&mut backend, session);
    backend.forget_typed(1).unwrap();
}

#[test]
fn borrowed_adapter_release_failure_is_retryable_after_calls_land_with_captured_ownership() {
    #[derive(Default)]
    struct Probe {
        releases: AtomicUsize,
        changed: std::sync::atomic::AtomicBool,
    }
    struct Adapter(Arc<Probe>);
    impl PluginObject for Adapter {
        fn descriptor(&self) -> ObjectDescriptor {
            ObjectDescriptor::callback(
                "release.Probe",
                if self.0.changed.load(Ordering::Relaxed) {
                    ObjectOwnership::Owned
                } else {
                    ObjectOwnership::Borrowed
                },
            )
            .unwrap()
        }
        fn call(&self, ctx: PluginContext, _: &str, args: Value) -> PluginFuture {
            Box::pin(async move { ctx.call("input", "query", args).await })
        }
        fn close(&self, _: PluginContext) -> PluginFuture {
            panic!("borrowed user close must never run")
        }
        fn release(&self, _: PluginContext, ownership: ObjectOwnership) -> PluginFuture {
            assert_eq!(ownership, ObjectOwnership::Borrowed);
            let attempt = self.0.releases.fetch_add(1, Ordering::Relaxed);
            Box::pin(async move {
                if attempt == 0 {
                    Err("retry adapter release".into())
                } else {
                    Ok(Value::Null)
                }
            })
        }
    }
    struct AdapterFactory(Arc<Probe>);
    impl PluginFactory for AdapterFactory {
        fn descriptor(&self) -> FactoryDescriptor {
            let mut descriptor = ReadyFactory.descriptor();
            descriptor.services[0].methods.push(MethodDescriptor {
                name: "object".into(),
                kind: MethodKind::Object,
            });
            descriptor
        }
        fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
            Ok(Arc::new(Adapter(self.0.clone())))
        }
    }
    impl PluginInstance for Adapter {
        fn setup(&self, ctx: PluginContext) -> PluginFuture {
            ReadyInstance.setup(ctx)
        }
        fn open_object(&self, _: &str, _: &str, _: Value) -> PluginResult<Arc<dyn PluginObject>> {
            Ok(Arc::new(Adapter(self.0.clone())))
        }
    }
    let probe = Arc::new(Probe::default());
    let mut registry = FactoryRegistry::new();
    registry.register(AdapterFactory(probe.clone())).unwrap();
    let mut backend = plugin::Backend::new(registry, Arc::new(|| {}));
    let session = number(
        &backend.start(1, 1, "test", Value::Null).unwrap(),
        "session",
    );
    let provide = expect_call(&mut backend, "provide");
    backend
        .reply(
            number(&provide, "request"),
            Ok(json!({"publication":"3","port":{"key":"4","realm":"0"}})),
        )
        .unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    let object = number(
        &backend
            .call(session, "service", "object", json!([]), false, false)
            .unwrap(),
        "object",
    );
    probe.changed.store(true, Ordering::Relaxed);
    backend
        .object_call(session, object, "call", json!([]), false, false)
        .unwrap();
    let call = expect_call(&mut backend, "call");
    backend.object_close(session, object).unwrap();
    assert_eq!(backend.poll()["jobs"], json!([]));
    assert_eq!(probe.releases.load(Ordering::Relaxed), 0);
    backend
        .reply(number(&call, "request"), Ok(Value::Null))
        .unwrap();
    backend.poll();
    assert_eq!(backend.poll()["jobs"][0]["success"], false);
    assert!(backend.cleanup(session).is_err());
    backend.object_close(session, object).unwrap();
    assert_eq!(backend.poll()["jobs"][0]["success"], true);
    assert_eq!(probe.releases.load(Ordering::Relaxed), 2);
}
