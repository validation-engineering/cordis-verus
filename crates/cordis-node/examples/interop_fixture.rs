//! A separately compiled addon registers its own factory using only the public
//! SDK. The core binding contains no counter factory or knowledge of jsSource.
#[path = "typed_fixture/mod.rs"]
mod typed_fixture;

use cordis_node::{
    plugin::{
        FactoryDescriptor, FactoryRegistry, MethodDescriptor, MethodKind, ObjectDescriptor,
        ObjectOwnership, PluginContext, PluginFactory, PluginFuture, PluginInstance, PluginObject,
        PluginResult, PluginStream, ServiceDescriptor, StreamFuture,
    },
    NativeDriver,
};
use napi_derive::napi;
use serde_json::{json, Value};
use std::future::Future;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc, Mutex,
};
use std::task::{Poll, Waker};

struct CounterFactory;
struct Counter {
    value: Arc<Mutex<i64>>,
    fail_cleanup: Arc<AtomicBool>,
    fail_setup: bool,
    wait_setup_cancellation: bool,
    panic_instance_drop: bool,
}
impl PluginFactory for CounterFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "fixture.counter".into(),
            inject: vec!["jsSource".into()],
            services: vec![ServiceDescriptor {
                name: "rustCounter".into(),
                methods: vec![
                    MethodDescriptor {
                        name: "read".into(),
                        kind: MethodKind::Sync,
                    },
                    MethodDescriptor {
                        name: "add".into(),
                        kind: MethodKind::Sync,
                    },
                    MethodDescriptor {
                        name: "request".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "waitCancelled".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "threadRequest".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "panicPoll".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "panicDrop".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "object".into(),
                        kind: MethodKind::Object,
                    },
                    MethodDescriptor {
                        name: "callback".into(),
                        kind: MethodKind::Object,
                    },
                    MethodDescriptor {
                        name: "useObject".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "useCallback".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "takeObject".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "twoObjects".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "dropObjectCall".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "stream".into(),
                        kind: MethodKind::Stream,
                    },
                    MethodDescriptor {
                        name: "consumeStream".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "takeStream".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "delay".into(),
                        kind: MethodKind::Async,
                    },
                ],
            }],
        }
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        if !config.is_null() && !config.is_object() {
            return Err("config must be an object or null".into());
        }
        Ok(Arc::new(Counter {
            value: Arc::new(Mutex::new(0)),
            fail_cleanup: Arc::new(AtomicBool::new(config["failCleanupOnce"] == true)),
            fail_setup: config["failSetup"] == true,
            wait_setup_cancellation: config["waitSetupCancellation"] == true,
            panic_instance_drop: config["panicInstanceDrop"] == true,
        }))
    }
}
impl PluginInstance for Counter {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        let value = self.value.clone();
        let fail = self.fail_setup;
        let wait_cancellation = self.wait_setup_cancellation;
        Box::pin(async move {
            let initial = ctx.call("jsSource", "read", json!([])).await?;
            *value.lock().unwrap() = initial
                .as_i64()
                .ok_or("jsSource.read must return an i64 DTO")?;
            ctx.provide("rustCounter").await?;
            if wait_cancellation {
                let current = *value.lock().unwrap();
                ctx.call("jsSource", "record", json!(["setup-wait", current]))
                    .await?;
                ctx.cancellation().cancelled().await;
                return Err("Cancelled".into());
            }
            if fail {
                Err("configured setup failure".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        let value = self.value.clone();
        let fail = self.fail_cleanup.clone();
        Box::pin(async move {
            let current = *value.lock().unwrap();
            ctx.call("jsSource", "record", json!(["cleanup", current]))
                .await?;
            if fail.swap(false, Ordering::AcqRel) {
                Err("configured cleanup failure".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn call_sync(&self, service: &str, method: &str, args: Value) -> PluginResult<Value> {
        if service != "rustCounter" {
            return Err("unknown service".into());
        }
        let mut value = self.value.lock().unwrap();
        match method {
            "read" if args.as_array().is_some_and(Vec::is_empty) => Ok(json!(*value)),
            "add" if args.as_array().is_some_and(|a| a.len() == 1) => {
                *value = value
                    .checked_add(args[0].as_i64().ok_or("add requires an i64")?)
                    .ok_or("counter overflow")?;
                Ok(json!(*value))
            }
            _ => Err("invalid method or argument DTO".into()),
        }
    }
    fn open_stream(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginStream>> {
        if service != "rustCounter" || method != "stream" {
            return Err("unknown stream".into());
        }
        self.make_stream(args)
    }
    fn open_object(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginObject>> {
        if service != "rustCounter" || !["object", "callback"].contains(&method) {
            return Err("unknown object".into());
        }
        let ownership = if args[0]["borrowed"] == true {
            ObjectOwnership::Borrowed
        } else {
            ObjectOwnership::Owned
        };
        let descriptor = if method == "callback" {
            ObjectDescriptor::callback("fixture.Callback", ownership)?
        } else {
            ObjectDescriptor::new(
                "fixture.CounterObject",
                ["read", "add", "query", "waitCancelled"],
                ownership,
            )?
        };
        Ok(Arc::new(CounterObject {
            value: self.value.clone(),
            descriptor,
            close_attempt: Arc::new(Mutex::new(0)),
            fail_close: args[0]["failCloseOnce"] == true,
            label: args[0]["label"].as_str().unwrap_or("object").to_owned(),
        }))
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginFuture {
        let service = service.to_owned();
        let method = method.to_owned();
        Box::pin(async move {
            if service != "rustCounter" {
                return Err("unknown service".into());
            }
            match method.as_str() {
                "request" => ctx.call("jsSource", "query", args).await,
                "consumeStream" | "takeStream" => {
                    let limit = if method == "takeStream" {
                        Some(args[0].as_u64().ok_or("takeStream requires a count")?)
                    } else {
                        None
                    };
                    let stream_args = if limit.is_some() {
                        Value::Array(args.as_array().ok_or("expected args array")?[1..].to_vec())
                    } else {
                        args
                    };
                    let stream = ctx.open_stream("jsSource", "stream", stream_args).await?;
                    let mut values = Vec::new();
                    while limit.is_none_or(|limit| values.len() < limit as usize) {
                        match stream.next().await? {
                            Some(value) => values.push(value),
                            None => break,
                        }
                    }
                    // Intentionally rely on the action journal, including EOF.
                    Ok(Value::Array(values))
                }
                "useObject" => {
                    let object = ctx
                        .open_object(
                            "jsSource",
                            "object",
                            args.get(3).cloned().unwrap_or(json!([])),
                        )
                        .await?;
                    let result = object
                        .call(
                            args[0].as_str().unwrap_or("read"),
                            args.get(1).cloned().unwrap_or(json!([])),
                        )
                        .await?;
                    if args[2] == true {
                        object.close().await?;
                    }
                    Ok(result)
                }
                "useCallback" => {
                    let callback = ctx.open_callback("jsSource", "callback", json!([])).await?;
                    callback.invoke(args).await
                }
                "takeObject" => {
                    let _object = ctx.open_object("jsSource", "object", args).await?;
                    Ok(Value::Null)
                }
                "twoObjects" => {
                    let first = ctx
                        .open_object("jsSource", "object", json!(["first"]))
                        .await?;
                    let second = ctx
                        .open_object("jsSource", "object", json!(["second"]))
                        .await?;
                    Ok(json!([
                        first.call("read", json!([])).await?,
                        second.call("read", json!([])).await?
                    ]))
                }
                "dropObjectCall" => {
                    let object = ctx.open_object("jsSource", "object", json!([])).await?;
                    let mut call = Box::pin(object.call(
                        args[0].as_str().unwrap_or("query"),
                        args.get(1).cloned().unwrap_or(json!([])),
                    ));
                    std::future::poll_fn(|cx| {
                        assert!(call.as_mut().poll(cx).is_pending());
                        Poll::Ready(())
                    })
                    .await;
                    drop(call);
                    Ok(json!("dropped"))
                }
                "threadRequest" => thread_request(ctx, args).await,
                "panicPoll" => panic!("configured Rust poll panic"),
                "panicDrop" => PanicDrop.await,
                "waitCancelled" => {
                    ctx.cancellation().cancelled().await;
                    Ok(json!("cancelled"))
                }
                "delay" => {
                    let ms = args[0]
                        .as_u64()
                        .filter(|ms| *ms <= 1000)
                        .ok_or("delay requires 0..1000 ms")?;
                    delay(ms).await;
                    Ok(args[1].clone())
                }
                _ => Err("invalid async method".into()),
            }
        })
    }
}
impl Counter {
    fn make_stream(&self, args: Value) -> PluginResult<Arc<dyn PluginStream>> {
        let options = &args[0];
        Ok(Arc::new(CounterStream {
            next: Arc::new(Mutex::new(0)),
            count: options["count"].as_u64().unwrap_or(3),
            delay_ms: options["delayMs"].as_u64().unwrap_or(0).min(1000),
            wait_cancel: options["waitForCancel"] == true,
            rpc: options["rpc"] == true,
            fail_close: options["failCloseOnce"] == true,
            close_attempt: Arc::new(Mutex::new(0)),
        }))
    }
}
struct CounterObject {
    value: Arc<Mutex<i64>>,
    descriptor: ObjectDescriptor,
    close_attempt: Arc<Mutex<u64>>,
    fail_close: bool,
    label: String,
}
impl PluginObject for CounterObject {
    fn descriptor(&self) -> ObjectDescriptor {
        self.descriptor.clone()
    }
    fn call(&self, ctx: PluginContext, method: &str, args: Value) -> PluginFuture {
        let method = method.to_owned();
        let value = self.value.clone();
        Box::pin(async move {
            match method.as_str() {
                "read" => Ok(json!(*value.lock().unwrap())),
                "add" => {
                    let mut value = value.lock().unwrap();
                    *value = value
                        .checked_add(args[0].as_i64().ok_or("add requires integer")?)
                        .ok_or("overflow")?;
                    Ok(json!(*value))
                }
                "query" | "call" => ctx.call("jsSource", "query", args).await,
                "waitCancelled" => {
                    ctx.cancellation().cancelled().await;
                    Ok(json!("cancelled"))
                }
                _ => Err("unknown object method".into()),
            }
        })
    }
    fn close(&self, ctx: PluginContext) -> PluginFuture {
        let attempts = self.close_attempt.clone();
        let fail = self.fail_close;
        let label = self.label.clone();
        Box::pin(async move {
            let attempt = {
                let mut n = attempts.lock().unwrap();
                *n += 1;
                *n
            };
            ctx.call(
                "jsSource",
                "record",
                json!(["object-close", label, attempt]),
            )
            .await?;
            if fail && attempt == 1 {
                Err("configured object close failure".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
}
struct CounterStream {
    next: Arc<Mutex<u64>>,
    count: u64,
    delay_ms: u64,
    wait_cancel: bool,
    rpc: bool,
    fail_close: bool,
    close_attempt: Arc<Mutex<u64>>,
}
impl PluginStream for CounterStream {
    fn next(&self, ctx: PluginContext) -> StreamFuture {
        let next = self.next.clone();
        let count = self.count;
        let delay_ms = self.delay_ms;
        let wait_cancel = self.wait_cancel;
        let rpc = self.rpc;
        Box::pin(async move {
            let index = *next.lock().unwrap();
            ctx.call("jsSource", "record", json!(["stream-pull", index]))
                .await?;
            if wait_cancel {
                ctx.cancellation().cancelled().await;
                return Err("Cancelled".into());
            }
            if delay_ms > 0 {
                delay(delay_ms).await;
            }
            ctx.cancellation().check()?;
            if index >= count {
                return Ok(None);
            }
            let value = if rpc {
                ctx.call("jsSource", "query", json!([index])).await?
            } else {
                json!(index)
            };
            *next.lock().unwrap() += 1;
            Ok(Some(value))
        })
    }
    fn close(&self, ctx: PluginContext) -> PluginFuture {
        let attempts = self.close_attempt.clone();
        let fail = self.fail_close;
        Box::pin(async move {
            let attempt = {
                let mut n = attempts.lock().unwrap();
                *n += 1;
                *n
            };
            ctx.call("jsSource", "record", json!(["stream-close", attempt]))
                .await?;
            if fail && attempt == 1 {
                Err("configured stream close failure".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
}
impl Drop for Counter {
    fn drop(&mut self) {
        if self.panic_instance_drop {
            panic!("configured Rust instance Drop panic");
        }
    }
}
struct PanicDrop;
impl std::future::Future for PanicDrop {
    type Output = PluginResult<Value>;
    fn poll(self: std::pin::Pin<&mut Self>, _: &mut std::task::Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(Ok(Value::Null))
    }
}
impl Drop for PanicDrop {
    fn drop(&mut self) {
        panic!("configured Rust future Drop panic");
    }
}
async fn thread_request(ctx: PluginContext, args: Value) -> PluginResult<Value> {
    struct State {
        result: Option<PluginResult<Value>>,
        waker: Option<Waker>,
    }
    struct ThreadWake(std::thread::Thread);
    impl std::task::Wake for ThreadWake {
        fn wake(self: Arc<Self>) {
            self.0.unpark();
        }
    }
    let state = Arc::new(Mutex::new(State {
        result: None,
        waker: None,
    }));
    let worker = state.clone();
    std::thread::spawn(move || {
        let waker = Waker::from(Arc::new(ThreadWake(std::thread::current())));
        let mut future = Box::pin(ctx.call("jsSource", "query", args));
        let result = loop {
            match std::future::Future::poll(
                future.as_mut(),
                &mut std::task::Context::from_waker(&waker),
            ) {
                Poll::Ready(result) => break result,
                Poll::Pending => std::thread::park(),
            }
        };
        let wake = {
            let mut state = worker.lock().unwrap();
            state.result = Some(result);
            state.waker.take()
        };
        if let Some(wake) = wake {
            wake.wake();
        }
    });
    std::future::poll_fn(move |ctx| {
        let mut state = state.lock().unwrap();
        if let Some(result) = state.result.take() {
            Poll::Ready(result)
        } else {
            state.waker = Some(ctx.waker().clone());
            Poll::Pending
        }
    })
    .await
}
async fn delay(ms: u64) {
    struct State {
        done: bool,
        waker: Option<Waker>,
    }
    let state = Arc::new(Mutex::new(State {
        done: false,
        waker: None,
    }));
    let worker = state.clone();
    std::thread::spawn(move || {
        std::thread::sleep(std::time::Duration::from_millis(ms));
        let wake = {
            let mut state = worker.lock().unwrap();
            state.done = true;
            state.waker.take()
        };
        if let Some(wake) = wake {
            wake.wake();
        }
    });
    std::future::poll_fn(move |ctx| {
        let mut state = state.lock().unwrap();
        if state.done {
            Poll::Ready(())
        } else {
            state.waker = Some(ctx.waker().clone());
            Poll::Pending
        }
    })
    .await;
}
#[napi]
pub fn create_driver() -> napi::Result<NativeDriver> {
    let mut registry = FactoryRegistry::new();
    registry
        .register(CounterFactory)
        .map_err(napi::Error::from_reason)?;
    typed_fixture::register(&mut registry).map_err(napi::Error::from_reason)?;
    NativeDriver::with_factories(registry)
}
