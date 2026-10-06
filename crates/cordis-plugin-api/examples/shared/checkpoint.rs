use super::{enabled, normalize_args};
use cordis_plugin_api::{
    Checkpoint, CheckpointSchema, FactoryDescriptor, MethodDescriptor, MethodKind, PluginContext,
    PluginFactory, PluginFuture, PluginInstance, PluginResult, ServiceDescriptor,
};
use serde_json::{json, Value};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

pub struct CheckpointFactory {
    pub version: &'static str,
    pub failing: bool,
}
impl PluginFactory for CheckpointFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "native-checkpoint".into(),
            inject: vec!["jsHost".into()],
            services: vec![ServiceDescriptor {
                name: "nativeCheckpoint".into(),
                methods: vec![
                    MethodDescriptor {
                        name: "read".into(),
                        kind: MethodKind::Sync,
                    },
                    MethodDescriptor {
                        name: "mutate".into(),
                        kind: MethodKind::Sync,
                    },
                    MethodDescriptor {
                        name: "add".into(),
                        kind: MethodKind::Async,
                    },
                ],
            }],
        }
    }
    fn checkpoint_schema(&self) -> Option<CheckpointSchema> {
        Some(CheckpointSchema {
            schema: if self.failing {
                "cordis.fixture.counter.incompatible"
            } else {
                "cordis.fixture.counter"
            }
            .into(),
            version: if self.version == "v2" { 2 } else { 1 },
            accepts: vec![1, 2],
        })
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Counter {
            version: self.version,
            failing: self.failing,
            state: Arc::new(Mutex::new(State {
                value: config["initial"].as_i64().unwrap_or(0),
                restored_from: None,
            })),
            config,
            captures: AtomicUsize::new(0),
            cleanups: AtomicUsize::new(0),
        }))
    }
}
struct State {
    value: i64,
    restored_from: Option<u32>,
}
impl State {
    fn snapshot(&self, version: &str) -> Value {
        json!({"version":version,"value":self.value,"restoredFrom":self.restored_from})
    }
    fn add(&mut self, delta: i64) -> PluginResult<()> {
        self.value = self.value.checked_add(delta).ok_or("CounterOverflow")?;
        Ok(())
    }
}
struct Counter {
    version: &'static str,
    failing: bool,
    config: Value,
    state: Arc<Mutex<State>>,
    captures: AtomicUsize,
    cleanups: AtomicUsize,
}
fn failure(config: &Value, name: &str, version: &str) -> bool {
    config[name].as_bool() == Some(true) || config[name].as_str() == Some(version)
}
impl PluginInstance for Counter {
    fn checkpoint(&self) -> PluginResult<Value> {
        if self.captures.fetch_add(1, Ordering::SeqCst) == 0
            && enabled(&self.config, "failCaptureOnce")
        {
            return Err("FixtureCaptureFailed".into());
        }
        match self.config["captureInvalid"].as_str() {
            Some("depth") => {
                let mut value = Value::Null;
                for _ in 0..65 {
                    value = json!([value]);
                }
                return Ok(value);
            }
            Some("size") => return Ok(Value::String("a".repeat(512 * 1024))),
            _ => {}
        }
        let value = self.state.lock().unwrap().value;
        Ok(if self.version == "v2" {
            json!({"counter":value})
        } else {
            json!({"value":value})
        })
    }
    fn restore(&self, checkpoint: Checkpoint) -> PluginResult<()> {
        let value = if checkpoint.version == 1 {
            &checkpoint.data["value"]
        } else {
            &checkpoint.data["counter"]
        }
        .as_i64()
        .ok_or("InvalidCounterCheckpoint")?;
        let mut state = self.state.lock().unwrap();
        state.value = value;
        state.restored_from = Some(checkpoint.version);
        if failure(&self.config, "failRestore", self.version) {
            return Err("FixtureRestoreFailed".into());
        }
        Ok(())
    }
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        let value = self.state.lock().unwrap().snapshot(version);
        let fail = self.failing || failure(&self.config, "failSetup", version);
        Box::pin(async move {
            ctx.call("jsHost","record",json!([{"phase":"checkpoint-setup","version":version,"value":value["value"],"restoredFrom":value["restoredFrom"]}])).await?;
            if fail {
                Err("CandidateSetupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        let version = self.version;
        let attempt = self.cleanups.fetch_add(1, Ordering::SeqCst) + 1;
        let fail = enabled(&self.config, "failCleanupOnce") && attempt == 1;
        let value = self.state.lock().unwrap().snapshot(version);
        Box::pin(async move {
            ctx.call("jsHost","record",json!([{"phase":"checkpoint-cleanup","version":version,"attempt":attempt,"value":value["value"],"restoredFrom":value["restoredFrom"]}])).await?;
            if fail {
                Err("FixtureCleanupFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
    fn call_sync(&self, service: &str, method: &str, args: Value) -> PluginResult<Value> {
        if service != "nativeCheckpoint" {
            return Err("UnknownService".into());
        }
        let mut state = self.state.lock().unwrap();
        match method {
            "read" => {}
            "mutate" => state.add(normalize_args(args).as_i64().unwrap_or(1))?,
            _ => return Err("UnknownSyncMethod".into()),
        }
        Ok(state.snapshot(self.version))
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginFuture {
        if service != "nativeCheckpoint" || method != "add" {
            return Box::pin(async { Err("UnknownAsyncMethod".into()) });
        }
        let options = normalize_args(args);
        let delta = options["delta"].as_i64().unwrap_or(1);
        let gate = enabled(&options, "gate");
        let state = self.state.clone();
        let version = self.version;
        Box::pin(async move {
            if gate {
                ctx.call(
                    "jsHost",
                    "gate",
                    json!([{"phase":"checkpoint-add","version":version,"delta":delta}]),
                )
                .await?;
            }
            let mut state = state.lock().unwrap();
            state.add(delta)?;
            Ok(state.snapshot(version))
        })
    }
}
