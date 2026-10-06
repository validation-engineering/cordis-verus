use cordis_plugin_api::{
    FactoryDescriptor, MethodDescriptor, MethodKind, ObjectDescriptor, ObjectOwnership,
    PluginContext, PluginFactory, PluginFuture, PluginInstance, PluginObject, PluginResult,
    PluginStream, ServiceDescriptor, StreamFuture,
};
use serde_json::{json, Value};
use std::sync::atomic::{AtomicBool, AtomicI64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

pub(super) struct ResourceFactory {
    version: &'static str,
    failing: bool,
}
impl ResourceFactory {
    pub(super) fn new(version: &'static str, failing: bool) -> Self {
        Self { version, failing }
    }
}
struct Instance {
    version: &'static str,
    failing: bool,
    borrowed: Arc<Mutex<Vec<Arc<Object>>>>,
}
fn options(args: Value) -> Value {
    args.as_array()
        .and_then(|args| args.first())
        .cloned()
        .unwrap_or(Value::Null)
}
fn flag(value: &Value, key: &str) -> bool {
    value[key].as_bool().unwrap_or(false)
}
impl PluginFactory for ResourceFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "native-resource-consumer".into(),
            inject: vec!["jsHost".into()],
            services: vec![ServiceDescriptor {
                name: "nativeResources".into(),
                methods: vec![
                    MethodDescriptor {
                        name: "stream".into(),
                        kind: MethodKind::Stream,
                    },
                    MethodDescriptor {
                        name: "object".into(),
                        kind: MethodKind::Object,
                    },
                ],
            }],
        }
    }
    fn create(&self, _config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Instance {
            version: self.version,
            failing: self.failing,
            borrowed: Arc::new(Mutex::new(Vec::new())),
        }))
    }
}
impl PluginInstance for Instance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        let failing = self.failing;
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{"phase":"resource-setup","version":version}]),
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
        let borrowed = self.borrowed.clone();
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{"phase":"resource-cleanup","version":version}]),
            )
            .await?;
            // Borrowed handles only release references. Their actual referents
            // remain owned here until the plugin itself finishes its cleanup.
            let values = std::mem::take(&mut *borrowed.lock().unwrap());
            drop(values);
            Ok(Value::Null)
        })
    }
    fn open_stream(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginStream>> {
        if service != "nativeResources" || method != "stream" {
            return Err("UnknownStreamMethod".into());
        }
        let args = options(args);
        Ok(Arc::new(Stream {
            version: self.version,
            values: args["values"].as_array().cloned().unwrap_or_default(),
            index: AtomicUsize::new(0),
            gate: flag(&args, "gateNext"),
            fail: flag(&args, "failCloseOnce"),
            attempt: AtomicUsize::new(0),
            cancelled: Arc::new(AtomicBool::new(false)),
            label: args["label"].clone(),
            close_object_args: args.get("closeObjectArgs").cloned(),
        }))
    }
    fn open_object(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginObject>> {
        if service != "nativeResources" || method != "object" {
            return Err("UnknownObjectMethod".into());
        }
        let args = options(args);
        let ownership = match args["ownership"].as_str() {
            None | Some("owned") => ObjectOwnership::Owned,
            Some("borrowed") => ObjectOwnership::Borrowed,
            _ => return Err("InvalidOwnership".into()),
        };
        let object = Arc::new(Object {
            version: self.version,
            value: Arc::new(AtomicI64::new(args["start"].as_i64().unwrap_or(0))),
            ownership,
            gate: flag(&args, "gateCalls"),
            fail: flag(&args, "failCloseOnce"),
            attempt: AtomicUsize::new(0),
            label: args["label"].clone(),
            close_object_args: args.get("closeObjectArgs").cloned(),
        });
        if ownership == ObjectOwnership::Borrowed {
            self.borrowed.lock().unwrap().push(object.clone());
        }
        Ok(object)
    }
}
struct Stream {
    version: &'static str,
    values: Vec<Value>,
    index: AtomicUsize,
    gate: bool,
    fail: bool,
    attempt: AtomicUsize,
    cancelled: Arc<AtomicBool>,
    label: Value,
    close_object_args: Option<Value>,
}
impl PluginStream for Stream {
    fn next(&self, ctx: PluginContext) -> StreamFuture {
        let index = self.index.fetch_add(1, Ordering::SeqCst);
        let value = self.values.get(index).cloned();
        let version = self.version;
        let gate = self.gate;
        let cancelled = self.cancelled.clone();
        let label = self.label.clone();
        Box::pin(async move {
            let event =
                json!({"phase":"stream-next","version":version,"index":index,"label":label});
            ctx.call("jsHost", "record", json!([event])).await?;
            if gate {
                ctx.call("jsHost", "gate", json!([event])).await?;
            }
            ctx.cancellation.check()?;
            if cancelled.load(Ordering::Acquire) {
                return Err("Cancelled".into());
            }
            Ok(value.map(|value| json!({"version":version,"index":index,"value":value})))
        })
    }
    fn cancel(&self) {
        self.cancelled.store(true, Ordering::Release);
    }
    fn close(&self, ctx: PluginContext) -> PluginFuture {
        let attempt = self.attempt.fetch_add(1, Ordering::SeqCst) + 1;
        let fail = self.fail && attempt == 1;
        let version = self.version;
        let label = self.label.clone();
        let close_object_args = self.close_object_args.clone();
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{"phase":"stream-close","version":version,"attempt":attempt,"label":label}]),
            )
            .await?;
            if let Some(args) = close_object_args {
                ctx.open_object("jsHost", "object", args).await?;
            }
            if fail {
                Err("FixtureStreamCloseFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
}
struct Object {
    version: &'static str,
    value: Arc<AtomicI64>,
    ownership: ObjectOwnership,
    gate: bool,
    fail: bool,
    attempt: AtomicUsize,
    label: Value,
    close_object_args: Option<Value>,
}
impl PluginObject for Object {
    fn descriptor(&self) -> ObjectDescriptor {
        ObjectDescriptor::new("native.counter", ["read", "add", "wait"], self.ownership).unwrap()
    }
    fn call(&self, ctx: PluginContext, method: &str, args: Value) -> PluginFuture {
        let method = method.to_owned();
        let version = self.version;
        let value = self.value.clone();
        let gate = self.gate || method == "wait";
        let label = self.label.clone();
        Box::pin(async move {
            let event =
                json!({"phase":"object-call","version":version,"method":method,"label":label});
            ctx.call("jsHost", "record", json!([event])).await?;
            if gate {
                ctx.call("jsHost", "gate", json!([event])).await?;
            }
            ctx.cancellation.check()?;
            if method == "add" {
                let delta = args
                    .as_array()
                    .and_then(|args| args.first())
                    .and_then(Value::as_i64)
                    .ok_or("ExpectedDelta")?;
                value
                    .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |value| {
                        value.checked_add(delta)
                    })
                    .map_err(|_| "CounterOverflow")?;
            }
            Ok(json!({"version":version,"value":value.load(Ordering::SeqCst)}))
        })
    }
    fn close(&self, ctx: PluginContext) -> PluginFuture {
        let attempt = self.attempt.fetch_add(1, Ordering::SeqCst) + 1;
        let fail = self.fail && attempt == 1;
        let version = self.version;
        let label = self.label.clone();
        let close_object_args = self.close_object_args.clone();
        Box::pin(async move {
            ctx.call(
                "jsHost",
                "record",
                json!([{"phase":"object-close","version":version,"attempt":attempt,"label":label}]),
            )
            .await?;
            if let Some(args) = close_object_args {
                ctx.open_object("jsHost", "object", args).await?;
            }
            if fail {
                Err("FixtureObjectCloseFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
}
