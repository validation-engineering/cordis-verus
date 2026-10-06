mod checkpoint;
mod children;
mod resources;
mod reverse_resources;

use cordis_plugin_api::{
    FactoryDescriptor, MethodDescriptor, MethodKind, Module, PluginContext, PluginFactory,
    PluginFuture, PluginInstance, PluginResult, ServiceDescriptor,
};
use serde_json::{json, Value};
use std::future::Future;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::task::Poll;

pub fn module(version: &'static str, failing: bool) -> Module {
    Module::new("cordis.native-text-analysis", version)
        .factory(TextFactory { version, failing })
        .factory(checkpoint::CheckpointFactory { version, failing })
        .factory(JsFactory { version, failing })
        .factory(resources::ResourceFactory::new(version, failing))
        .factory(reverse_resources::ReverseResourceFactory { version, failing })
        .factory(children::ParentFactory { version, failing })
        .factory(children::LeafFactory {
            version,
            service: "nativeNamedChild".into(),
            extra_inject: None,
        })
}
struct TextFactory {
    version: &'static str,
    failing: bool,
}
impl PluginFactory for TextFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "native-text-analysis".into(),
            inject: vec![],
            services: vec![ServiceDescriptor {
                name: "nativeText".into(),
                methods: vec![
                    MethodDescriptor {
                        name: "analyze".into(),
                        kind: MethodKind::Sync,
                    },
                    MethodDescriptor {
                        name: "delayed".into(),
                        kind: MethodKind::Async,
                    },
                ],
            }],
        }
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(TextInstance {
            version: self.version,
            failing: self.failing,
            config,
            cleanup_count: AtomicUsize::new(0),
        }))
    }
}
struct TextInstance {
    version: &'static str,
    failing: bool,
    config: Value,
    cleanup_count: AtomicUsize,
}
fn enabled(value: &Value, key: &str) -> bool {
    value[key].as_bool().unwrap_or(false)
}
async fn yield_once() {
    let mut pending = true;
    std::future::poll_fn(move |cx| {
        if std::mem::take(&mut pending) {
            cx.waker().wake_by_ref();
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    })
    .await;
}
fn normalize_args(args: Value) -> Value {
    if let Some(args) = args.as_array() {
        args.first().cloned().unwrap_or(Value::Null)
    } else {
        args
    }
}
fn analyze(version: &'static str, args: Value) -> PluginResult<Value> {
    let args = normalize_args(args);
    if let Some(depth) = args["nestedDepth"].as_u64() {
        if depth > 256 {
            return Err("FixtureDepthTooLarge".into());
        }
        let mut value = Value::Null;
        for _ in 0..depth {
            value = Value::Array(vec![value]);
        }
        return Ok(value);
    }
    let text = args["text"].as_str().ok_or("ExpectedText")?;
    Ok(
        json!({"version": version, "words": text.split_whitespace().count(), "characters": text.chars().count(), "text": text}),
    )
}
impl PluginInstance for TextInstance {
    fn setup(&self, _ctx: PluginContext) -> PluginFuture {
        let pending = enabled(&self.config, "setup_pending");
        let failing = self.failing || enabled(&self.config, "fail_setup");
        Box::pin(async move {
            if pending {
                yield_once().await;
            }
            if failing {
                Err("CandidateSetupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn cleanup(&self, _ctx: PluginContext) -> PluginFuture {
        let attempt = self.cleanup_count.fetch_add(1, Ordering::SeqCst);
        let failing = enabled(&self.config, "fail_cleanup_always")
            || (enabled(&self.config, "fail_cleanup_once") && attempt == 0);
        let pending = enabled(&self.config, "cleanup_pending");
        Box::pin(async move {
            if pending {
                yield_once().await;
            }
            if failing {
                Err("FixtureCleanupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn call_sync(&self, service: &str, method: &str, args: Value) -> PluginResult<Value> {
        if service != "nativeText" || method != "analyze" {
            return Err("UnknownSyncMethod".into());
        }
        analyze(self.version, args)
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginFuture {
        if service != "nativeText" || method != "delayed" {
            return Box::pin(async { Err("UnknownAsyncMethod".into()) });
        }
        let version = self.version;
        let args = normalize_args(args);
        Box::pin(async move {
            if enabled(&args, "wait_for_cancel") {
                ctx.cancelled().await;
                return Err("Cancelled".into());
            }
            yield_once().await;
            ctx.cancellation.check()?;
            analyze(version, args)
        })
    }
}

struct JsFactory {
    version: &'static str,
    failing: bool,
}
struct JsInstance {
    version: &'static str,
    failing: bool,
    config: Value,
    cleanup_count: AtomicUsize,
}
impl PluginFactory for JsFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "native-js-consumer".into(),
            inject: vec!["jsHost".into()],
            services: vec![ServiceDescriptor {
                name: "nativeJs".into(),
                methods: vec![
                    MethodDescriptor {
                        name: "call".into(),
                        kind: MethodKind::Async,
                    },
                    MethodDescriptor {
                        name: "dropped".into(),
                        kind: MethodKind::Async,
                    },
                ],
            }],
        }
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(JsInstance {
            version: self.version,
            failing: self.failing,
            config,
            cleanup_count: AtomicUsize::new(0),
        }))
    }
}
impl PluginInstance for JsInstance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        let failing = self.failing || enabled(&self.config, "fail_setup");
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{ "phase":"setup", "version":version }]),
            )
            .await?;
            if failing {
                Err("CandidateSetupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        let attempt = self.cleanup_count.fetch_add(1, Ordering::SeqCst);
        let failing = enabled(&self.config, "fail_cleanup_always")
            || (enabled(&self.config, "fail_cleanup_once") && attempt == 0);
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{ "phase":"cleanup", "version":version }]),
            )
            .await?;
            if failing {
                Err("FixtureCleanupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginFuture {
        let valid = service == "nativeJs" && matches!(method, "call" | "dropped");
        let dropped = method == "dropped";
        Box::pin(async move {
            if !valid {
                return Err("UnknownAsyncMethod".into());
            }
            let arg = normalize_args(args);
            let service = arg["service"].as_str().unwrap_or("jsHost");
            let method = arg["method"].as_str().ok_or("ExpectedMethod")?;
            let arguments = arg.get("args").cloned().unwrap_or_else(|| json!([]));
            let future = ctx.call(service, method, arguments);
            if !dropped {
                return future.await;
            }
            let mut future = Box::pin(future);
            std::future::poll_fn(|cx| match future.as_mut().poll(cx) {
                Poll::Pending => Poll::Ready(Ok(())),
                Poll::Ready(Ok(_)) => Poll::Ready(Ok(())),
                Poll::Ready(Err(error)) => Poll::Ready(Err(error)),
            })
            .await?;
            drop(future);
            Ok(json!({"dropped":true}))
        })
    }
}
