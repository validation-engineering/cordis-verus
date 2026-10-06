use super::*;
use cordis_plugin_api::{ChildHandle, ChildStatus};
use std::collections::BTreeMap;
use std::sync::Mutex;

pub(super) struct ParentFactory {
    pub version: &'static str,
    pub failing: bool,
}
pub(super) struct LeafFactory {
    pub version: &'static str,
    pub service: String,
    pub extra_inject: Option<String>,
}
struct Parent {
    version: &'static str,
    failing: bool,
    config: Value,
    handles: Arc<Mutex<BTreeMap<String, ChildHandle>>>,
}
struct Leaf {
    version: &'static str,
    service: String,
    config: Value,
    cleanup_attempt: AtomicUsize,
}
fn descriptor(name: &str, service: &str, methods: &[&str]) -> FactoryDescriptor {
    FactoryDescriptor {
        name: name.into(),
        inject: vec!["jsHost".into()],
        services: vec![ServiceDescriptor {
            name: service.into(),
            methods: methods
                .iter()
                .map(|method| MethodDescriptor {
                    name: (*method).into(),
                    kind: MethodKind::Async,
                })
                .collect(),
        }],
    }
}
impl PluginFactory for ParentFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        descriptor(
            "native-children",
            "nativeChildren",
            &[
                "publish",
                "mount",
                "status",
                "ready",
                "dispose",
                "join",
                "retry_cleanup",
                "dropped_publish",
            ],
        )
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Parent {
            version: self.version,
            failing: self.failing,
            config,
            handles: Arc::new(Mutex::new(BTreeMap::new())),
        }))
    }
}
impl PluginFactory for LeafFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        let mut descriptor = descriptor(
            if self.service == "nativeNamedChild" {
                "native-child-leaf"
            } else {
                "native-published-child"
            },
            &self.service,
            &["read"],
        );
        if let Some(injection) = &self.extra_inject {
            descriptor.inject.push(injection.clone());
        }
        descriptor
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Leaf {
            version: self.version,
            service: self.service.clone(),
            config,
            cleanup_attempt: AtomicUsize::new(0),
        }))
    }
}
async fn publish(
    ctx: &PluginContext,
    version: &'static str,
    options: Value,
) -> PluginResult<ChildHandle> {
    let service = options["service"]
        .as_str()
        .unwrap_or("nativePublished")
        .to_owned();
    let extra_inject = options["extraInject"].as_str().map(str::to_owned);
    ctx.publish(
        LeafFactory {
            version,
            service,
            extra_inject,
        },
        options,
    )
    .await
}
impl PluginInstance for Parent {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        let failing = self.failing;
        let initial = self.config.get("initial").cloned();
        let join_setup = enabled(&self.config, "joinSetup");
        let handles = self.handles.clone();
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{"phase":"children-setup","version":version}]),
            )
            .await?;
            if let Some(options) = initial {
                let key = options["key"].as_str().unwrap_or("published").to_owned();
                let child = publish(&ctx, version, options).await?;
                handles.lock().unwrap().insert(key, child.clone());
                if join_setup {
                    child.initialized(&ctx).await?;
                }
            }
            if failing {
                Err("CandidateSetupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{"phase":"children-cleanup","version":version}]),
            )
            .await
        })
    }
    fn call_async(&self, ctx: PluginContext, _: &str, method: &str, args: Value) -> PluginFuture {
        let version = self.version;
        let method = method.to_owned();
        let options = normalize_args(args);
        let handles = self.handles.clone();
        Box::pin(async move {
            let key = options["key"]
                .as_str()
                .unwrap_or(if method == "mount" {
                    "named"
                } else {
                    "published"
                })
                .to_owned();
            if method == "dropped_publish" {
                let mut future = Box::pin(publish(&ctx, version, options));
                std::future::poll_fn(|cx| match future.as_mut().poll(cx) {
                    Poll::Ready(Err(error)) => Poll::Ready(Err(error)),
                    _ => Poll::Ready(Ok(())),
                })
                .await?;
                drop(future);
                return Ok(Value::Null);
            }
            if matches!(method.as_str(), "mount" | "publish") {
                if handles.lock().unwrap().contains_key(&key) {
                    return Err("DuplicateChildKey".into());
                }
                let child = if method == "publish" {
                    publish(&ctx, version, options).await?
                } else {
                    let factory = options["factory"].as_str().unwrap_or("native-child-leaf");
                    ctx.mount(
                        factory,
                        options.get("config").cloned().unwrap_or(Value::Null),
                    )
                    .await?
                };
                handles.lock().unwrap().insert(key.clone(), child);
                return Ok(json!({"key":key}));
            }
            let child = handles
                .lock()
                .unwrap()
                .get(&key)
                .cloned()
                .ok_or("UnknownChildKey")?;
            match method.as_str() {
                "status" => {
                    let state: ChildStatus = child.status(&ctx).await?;
                    return serde_json::to_value(state).map_err(|_| "InvalidChildStatus".into());
                }
                "ready" => child.initialized(&ctx).await?,
                "dispose" => child.dispose(&ctx).await?,
                "join" => child.join(&ctx).await?,
                "retry_cleanup" => child.retry_cleanup(&ctx).await?,
                _ => return Err("UnknownChildMethod".into()),
            }
            Ok(json!({"key":key}))
        })
    }
}
impl PluginInstance for Leaf {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        let service = self.service.clone();
        let label = self.config["label"].clone();
        let failing = enabled(&self.config, "failSetup");
        let nested = self.config.get("nested").cloned();
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{"phase":"child-setup","version":version,"label":label,"service":service}]),
            )
            .await?;
            if let Some(nested) = nested {
                publish(&ctx, version, nested).await?;
            }
            if failing {
                Err("FixtureChildSetupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        let service = self.service.clone();
        let label = self.config["label"].clone();
        let attempt = self.cleanup_attempt.fetch_add(1, Ordering::SeqCst) + 1;
        let failing = enabled(&self.config, "failCleanupOnce") && attempt == 1;
        Box::pin(async move {
            ctx.call("jsHost", "record", json!([{"phase":"child-cleanup","version":version,"label":label,"service":service,"attempt":attempt}])).await?;
            if failing {
                Err("FixtureChildCleanupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn call_async(&self, ctx: PluginContext, _: &str, _: &str, args: Value) -> PluginFuture {
        let version = self.version;
        let service = self.service.clone();
        let label = self.config["label"].clone();
        let value = args
            .as_array()
            .and_then(|args| args.first())
            .cloned()
            .unwrap_or(Value::Null);
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{"phase":"child-read","version":version,"label":label,"service":service}]),
            )
            .await?;
            Ok(json!({"version":version,"label":label,"service":service,"value":value}))
        })
    }
}
