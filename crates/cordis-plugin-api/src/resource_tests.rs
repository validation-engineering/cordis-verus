use super::*;
use std::sync::atomic::AtomicUsize;

#[derive(Default)]
struct Shared {
    stream_closes: AtomicUsize,
    object_closes: AtomicUsize,
    object_drops: AtomicUsize,
    borrowed: Mutex<Vec<Arc<Object>>>,
}
struct Factory(Arc<Shared>);
struct Instance(Arc<Shared>);
struct Stream {
    shared: Arc<Shared>,
    gate: bool,
    reverse_close: bool,
    fail: bool,
    attempt: AtomicUsize,
    index: AtomicUsize,
    drop_panic: bool,
    large: bool,
    large_error: bool,
}
struct Object {
    shared: Arc<Shared>,
    borrowed: bool,
    gate: bool,
    fail: bool,
    attempt: AtomicUsize,
    descriptor_panic: bool,
}
impl PluginFactory for Factory {
    fn descriptor(&self) -> FactoryDescriptor {
        FactoryDescriptor {
            name: "resources".into(),
            inject: vec!["js".into()],
            services: vec![ServiceDescriptor {
                name: "resources".into(),
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
    fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(Instance(self.0.clone())))
    }
}
fn flag(value: &Value, key: &str) -> bool {
    value[key].as_bool().unwrap_or(false)
}
impl PluginInstance for Instance {
    fn setup(&self, _: PluginContext) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
    fn open_stream(&self, _: &str, _: &str, args: Value) -> PluginResult<Arc<dyn PluginStream>> {
        Ok(Arc::new(Stream {
            shared: self.0.clone(),
            gate: flag(&args, "gate"),
            reverse_close: flag(&args, "reverseClose"),
            fail: flag(&args, "fail"),
            attempt: AtomicUsize::new(0),
            index: AtomicUsize::new(0),
            drop_panic: flag(&args, "dropPanic"),
            large: flag(&args, "large"),
            large_error: flag(&args, "largeError"),
        }))
    }
    fn open_object(&self, _: &str, _: &str, args: Value) -> PluginResult<Arc<dyn PluginObject>> {
        let object = Arc::new(Object {
            shared: self.0.clone(),
            borrowed: flag(&args, "borrowed"),
            gate: flag(&args, "gate"),
            fail: flag(&args, "fail"),
            attempt: AtomicUsize::new(0),
            descriptor_panic: flag(&args, "descriptorPanic"),
        });
        if object.borrowed {
            self.0.borrowed.lock().unwrap().push(object.clone());
        }
        Ok(object)
    }
}
impl PluginStream for Stream {
    fn next(&self, ctx: PluginContext) -> StreamFuture {
        let gate = self.gate;
        let index = self.index.fetch_add(1, Ordering::SeqCst);
        let large = self.large;
        let large_error = self.large_error;
        Box::pin(async move {
            if large_error {
                return Err("x".repeat(MAX_MESSAGE_BYTES));
            }
            if gate {
                ctx.call("js", "next", json!([])).await?;
                ctx.cancellation.check()?;
            }
            if index == 0 {
                Ok(Some(if large {
                    Value::String("x".repeat(MAX_MESSAGE_BYTES / 2 - 2))
                } else {
                    json!(42)
                }))
            } else {
                Ok(None)
            }
        })
    }
    fn close(&self, ctx: PluginContext) -> PluginFuture {
        self.shared.stream_closes.fetch_add(1, Ordering::SeqCst);
        let fail = self.fail && self.attempt.fetch_add(1, Ordering::SeqCst) == 0;
        let reverse = self.reverse_close;
        Box::pin(async move {
            if reverse {
                ctx.call("js", "close", json!([])).await?;
            }
            if fail {
                Err("CloseFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
}
impl Drop for Stream {
    fn drop(&mut self) {
        assert!(!self.drop_panic, "resource destructor failed");
    }
}
impl PluginObject for Object {
    fn descriptor(&self) -> ObjectDescriptor {
        assert!(!self.descriptor_panic, "descriptor failed");
        ObjectDescriptor::new(
            "test.object",
            ["get"],
            if self.borrowed {
                ObjectOwnership::Borrowed
            } else {
                ObjectOwnership::Owned
            },
        )
        .unwrap()
    }
    fn call(&self, ctx: PluginContext, _: &str, _: Value) -> PluginFuture {
        let gate = self.gate;
        Box::pin(async move {
            if gate {
                ctx.call("js", "get", json!([])).await?;
            }
            Ok(json!(7))
        })
    }
    fn close(&self, _: PluginContext) -> PluginFuture {
        self.shared.object_closes.fetch_add(1, Ordering::SeqCst);
        let fail = self.fail && self.attempt.fetch_add(1, Ordering::SeqCst) == 0;
        Box::pin(async move {
            if fail {
                Err("CloseFailed".into())
            } else {
                Ok(Value::Null)
            }
        })
    }
}
impl Drop for Object {
    fn drop(&mut self) {
        self.shared.object_drops.fetch_add(1, Ordering::SeqCst);
    }
}
extern "C" fn wake(_: u64) {}
fn req(runtime: &Runtime, request: Value) -> PluginResult<Value> {
    runtime.handle(
        serde_json::from_value(request).unwrap(),
        WakeV1 { token: 0, wake },
    )
}
fn job(runtime: &Runtime, request: Value) -> u64 {
    req(runtime, request).unwrap()["job"].as_u64().unwrap()
}
fn poll(runtime: &Runtime, id: u64) -> Value {
    req(runtime, json!({"op":"poll","job":id})).unwrap()
}
fn release(runtime: &Runtime, id: u64) {
    req(runtime, json!({"op":"drop_job","job":id})).unwrap();
}
fn ready(runtime: &Runtime, id: u64) -> Value {
    let value = poll(runtime, id);
    assert_eq!(value["state"], "ready");
    release(runtime, id);
    value["result"].clone()
}
fn instance(runtime: &Runtime) -> u64 {
    let id = req(
        runtime,
        json!({"op":"create","factory":"resources","config":null}),
    )
    .unwrap()["instance"]
        .as_u64()
        .unwrap();
    let setup = job(runtime, json!({"op":"setup","instance":id}));
    assert_eq!(ready(runtime, setup), json!({"ok":null}));
    id
}
fn fixture() -> (Runtime, u64, Arc<Shared>) {
    let shared = Arc::new(Shared::default());
    let runtime =
        Runtime::new(Module::new("resources", "1").factory(Factory(shared.clone()))).unwrap();
    let id = instance(&runtime);
    (runtime, id, shared)
}
fn open(runtime: &Runtime, instance: u64, kind: &str, args: Value) -> u64 {
    req(runtime,json!({"op":format!("open_{kind}"),"instance":instance,"service":"resources","method":kind,"args":args})).unwrap()[kind].as_u64().unwrap()
}
fn action(_runtime: &Runtime, instance: u64, kind: &str, op: &str, id: u64) -> Value {
    let mut request = json!({"op":format!("{kind}_{op}"),"instance":instance});
    request[kind] = json!(id);
    request
}
fn close(runtime: &Runtime, instance: u64, kind: &str, id: u64) {
    let close = job(runtime, action(runtime, instance, kind, "close", id));
    assert_eq!(ready(runtime, close), json!({"ok":null}));
    let mut request = json!({"op":format!("destroy_{kind}"),"instance":instance});
    request[kind] = json!(id);
    req(runtime, request).unwrap();
}
fn finish(runtime: &Runtime, instance: u64) {
    let cleanup = job(runtime, json!({"op":"cleanup","instance":instance}));
    assert_eq!(ready(runtime, cleanup), json!({"ok":null}));
    req(runtime, json!({"op":"destroy","instance":instance})).unwrap();
}

#[test]
fn resources_require_same_owner_true_close_and_non_reused_handles() {
    let (runtime, owner, _) = fixture();
    let other = instance(&runtime);
    let stream = open(&runtime, owner, "stream", Value::Null);
    assert_eq!(
        req(
            &runtime,
            json!({"op":"stream_next","instance":other,"stream":stream})
        )
        .unwrap_err(),
        "WrongResourceOwner"
    );
    assert_eq!(
        req(
            &runtime,
            json!({"op":"object_close","instance":owner,"object":stream})
        )
        .unwrap_err(),
        "WrongResourceKind"
    );
    assert!(req(&runtime, json!({"op":"cleanup","instance":owner})).is_err());
    assert_eq!(
        req(
            &runtime,
            json!({"op":"destroy_stream","instance":owner,"stream":stream})
        )
        .unwrap_err(),
        "ResourceNotClosed"
    );
    close(&runtime, owner, "stream", stream);
    assert_eq!(
        req(
            &runtime,
            json!({"op":"stream_next","instance":owner,"stream":stream})
        )
        .unwrap_err(),
        "UnknownResource"
    );
    let next = open(&runtime, owner, "stream", Value::Null);
    assert!(next > stream);
    close(&runtime, owner, "stream", next);
    finish(&runtime, owner);
    finish(&runtime, other);
}
#[test]
fn stream_eof_still_needs_close_and_cannot_pull_again() {
    let (runtime, owner, shared) = fixture();
    let stream = open(&runtime, owner, "stream", Value::Null);
    let first = job(&runtime, action(&runtime, owner, "stream", "next", stream));
    assert_eq!(
        ready(&runtime, first),
        json!({"ok":{"done":false,"value":42}})
    );
    let end = job(&runtime, action(&runtime, owner, "stream", "next", stream));
    assert_eq!(ready(&runtime, end), json!({"ok":{"done":true}}));
    assert_eq!(
        req(&runtime, action(&runtime, owner, "stream", "next", stream)).unwrap_err(),
        "ResourceNotOpen"
    );
    close(&runtime, owner, "stream", stream);
    assert_eq!(shared.stream_closes.load(Ordering::SeqCst), 1);
    finish(&runtime, owner);
}
#[test]
fn stream_cancel_waits_for_actual_reverse_pull_before_cleanup_close() {
    let (runtime, owner, _) = fixture();
    let stream = open(
        &runtime,
        owner,
        "stream",
        json!({"gate":true,"reverseClose":true}),
    );
    let pull = job(&runtime, action(&runtime, owner, "stream", "next", stream));
    assert_eq!(poll(&runtime, pull)["calls"][0]["method"], "next");
    assert_eq!(
        req(&runtime, action(&runtime, owner, "stream", "next", stream)).unwrap_err(),
        "StreamBusy"
    );
    assert_eq!(
        req(&runtime, action(&runtime, owner, "stream", "close", stream)).unwrap_err(),
        "ResourceBusy"
    );
    req(
        &runtime,
        action(&runtime, owner, "stream", "cancel", stream),
    )
    .unwrap();
    assert_eq!(poll(&runtime, pull)["state"], "pending");
    req(
        &runtime,
        json!({"op":"resolve_call","job":pull,"request":1,"result":{"ok":null}}),
    )
    .unwrap();
    assert_eq!(ready(&runtime, pull), json!({"error":"Cancelled"}));
    let closing = job(&runtime, action(&runtime, owner, "stream", "close", stream));
    req(&runtime, json!({"op":"cancel","job":closing})).unwrap();
    assert_eq!(poll(&runtime, closing)["calls"][0]["method"], "close");
    req(
        &runtime,
        json!({"op":"resolve_call","job":closing,"request":1,"result":{"ok":null}}),
    )
    .unwrap();
    assert_eq!(ready(&runtime, closing), json!({"ok":null}));
    req(
        &runtime,
        json!({"op":"destroy_stream","instance":owner,"stream":stream}),
    )
    .unwrap();
    finish(&runtime, owner);
}
#[test]
fn failed_stream_and_object_closes_are_retryable_and_do_not_reopen_business() {
    let (runtime, owner, _) = fixture();
    for kind in ["stream", "object"] {
        let resource = open(&runtime, owner, kind, json!({"fail":true}));
        let first = job(&runtime, action(&runtime, owner, kind, "close", resource));
        assert_eq!(ready(&runtime, first), json!({"error":"CloseFailed"}));
        let mut destroy = json!({"op":format!("destroy_{kind}"),"instance":owner});
        destroy[kind] = json!(resource);
        assert_eq!(req(&runtime, destroy).unwrap_err(), "ResourceNotClosed");
        let mut call = action(
            &runtime,
            owner,
            kind,
            if kind == "stream" { "next" } else { "call" },
            resource,
        );
        if kind == "object" {
            call["method"] = json!("get");
            call["args"] = json!([]);
        }
        assert_eq!(req(&runtime, call).unwrap_err(), "ResourceNotOpen");
        close(&runtime, owner, kind, resource);
    }
    finish(&runtime, owner);
}
#[test]
fn object_close_waits_for_every_call_and_job_drop() {
    let (runtime, owner, _) = fixture();
    let object = open(&runtime, owner, "object", json!({"gate":true}));
    let first = job(
        &runtime,
        json!({"op":"object_call","instance":owner,"object":object,"method":"get","args":[]}),
    );
    let second = job(
        &runtime,
        json!({"op":"object_call","instance":owner,"object":object,"method":"get","args":[]}),
    );
    poll(&runtime, first);
    poll(&runtime, second);
    for current in [first, second] {
        assert_eq!(
            req(&runtime, action(&runtime, owner, "object", "close", object)).unwrap_err(),
            "ResourceBusy"
        );
        req(
            &runtime,
            json!({"op":"resolve_call","job":current,"request":1,"result":{"ok":null}}),
        )
        .unwrap();
        assert_eq!(poll(&runtime, current)["result"], json!({"ok":7}));
        assert_eq!(
            req(&runtime, action(&runtime, owner, "object", "close", object)).unwrap_err(),
            "ResourceBusy"
        );
        release(&runtime, current);
    }
    close(&runtime, owner, "object", object);
    finish(&runtime, owner);
}
#[test]
fn borrowed_release_preserves_referent_without_calling_its_close_hook() {
    let (runtime, owner, shared) = fixture();
    let object = open(&runtime, owner, "object", json!({"borrowed":true}));
    close(&runtime, owner, "object", object);
    assert_eq!(shared.object_closes.load(Ordering::SeqCst), 0);
    assert_eq!(shared.object_drops.load(Ordering::SeqCst), 0);
    shared.borrowed.lock().unwrap().clear();
    assert_eq!(shared.object_drops.load(Ordering::SeqCst), 1);
    finish(&runtime, owner);
}
#[test]
fn descriptor_panic_after_acquisition_is_retained_and_blocks_false_cleanup() {
    let (runtime, owner, shared) = fixture();
    assert_eq!(req(&runtime,json!({"op":"open_object","instance":owner,"service":"resources","method":"object","args":{"descriptorPanic":true}})).unwrap_err(),"PluginPanic");
    assert_eq!(shared.object_drops.load(Ordering::SeqCst), 0);
    assert_eq!(runtime.records.lock().unwrap().resources.len(), 1);
    assert!(req(&runtime, json!({"op":"cleanup","instance":owner})).is_err());
    assert_eq!(
        req(&runtime, json!({"op":"destroy","instance":owner})).unwrap_err(),
        "InstanceHasResources"
    );
}
#[test]
fn destructor_panic_does_not_make_resource_release_successful() {
    let (runtime, owner, _) = fixture();
    let stream = open(&runtime, owner, "stream", json!({"dropPanic":true}));
    let closing = job(&runtime, action(&runtime, owner, "stream", "close", stream));
    ready(&runtime, closing);
    assert_eq!(
        req(
            &runtime,
            json!({"op":"destroy_stream","instance":owner,"stream":stream})
        )
        .unwrap_err(),
        "PluginPanic"
    );
    assert_eq!(runtime.records.lock().unwrap().resources.len(), 1);
    assert!(req(&runtime, json!({"op":"cleanup","instance":owner})).is_err());
}
#[test]
fn item_limit_is_applied_before_stream_envelope_and_descriptor_limits_are_explicit() {
    let (runtime, owner, _) = fixture();
    let stream = open(&runtime, owner, "stream", json!({"large":true}));
    let pull = job(&runtime, action(&runtime, owner, "stream", "next", stream));
    let value = ready(&runtime, pull);
    assert_eq!(
        value["ok"]["value"].as_str().unwrap().len(),
        MAX_MESSAGE_BYTES / 2 - 2
    );
    assert!(serde_json::to_vec(&value).unwrap().len() < MAX_MESSAGE_BYTES);
    close(&runtime, owner, "stream", stream);
    let stream = open(&runtime, owner, "stream", json!({"largeError":true}));
    let pull = job(&runtime, action(&runtime, owner, "stream", "next", stream));
    assert_eq!(
        ready(&runtime, pull),
        json!({"error":"PluginErrorTooLarge"})
    );
    close(&runtime, owner, "stream", stream);
    finish(&runtime, owner);
    assert!(ObjectDescriptor::new("", ["get"], ObjectOwnership::Owned).is_err());
    assert!(ObjectDescriptor::new("test", ["get", "get"], ObjectOwnership::Owned).is_err());
    assert!(ObjectDescriptor::new(
        "x".repeat(MAX_MESSAGE_BYTES),
        ["get"],
        ObjectOwnership::Owned
    )
    .is_err());
}

struct AliasedObject {
    owned: AtomicBool,
    closes: AtomicUsize,
}
impl AliasedObject {
    fn new(owned: bool) -> Arc<Self> {
        Arc::new(Self {
            owned: AtomicBool::new(owned),
            closes: AtomicUsize::new(0),
        })
    }
}
impl PluginObject for AliasedObject {
    fn descriptor(&self) -> ObjectDescriptor {
        ObjectDescriptor::new(
            "shared.object",
            ["get"],
            if self.owned.load(Ordering::SeqCst) {
                ObjectOwnership::Owned
            } else {
                ObjectOwnership::Borrowed
            },
        )
        .unwrap()
    }
    fn call(&self, _: PluginContext, _: &str, _: Value) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
    fn close(&self, _: PluginContext) -> PluginFuture {
        self.closes.fetch_add(1, Ordering::SeqCst);
        Box::pin(async { Ok(Value::Null) })
    }
}
struct AliasFactory(Arc<Mutex<Arc<AliasedObject>>>);
struct AliasInstance(Arc<Mutex<Arc<AliasedObject>>>);
impl PluginFactory for AliasFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        Factory(Arc::new(Shared::default())).descriptor()
    }
    fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Ok(Arc::new(AliasInstance(self.0.clone())))
    }
}
impl PluginInstance for AliasInstance {
    fn setup(&self, _: PluginContext) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
    fn open_object(&self, _: &str, _: &str, _: Value) -> PluginResult<Arc<dyn PluginObject>> {
        Ok(self.0.lock().unwrap().clone())
    }
}
fn alias_fixture(owned: bool) -> (Runtime, u64, u64, Arc<Mutex<Arc<AliasedObject>>>) {
    let value = Arc::new(Mutex::new(AliasedObject::new(owned)));
    let runtime =
        Runtime::new(Module::new("aliases", "1").factory(AliasFactory(value.clone()))).unwrap();
    let first = instance(&runtime);
    let second = instance(&runtime);
    (runtime, first, second, value)
}
fn assert_alias_conflict(runtime: &Runtime, instance: u64) {
    assert_eq!(req(runtime, json!({"op":"open_object","instance":instance,"service":"resources","method":"object","args":null})).unwrap_err(), "ObjectOwnershipConflict");
}

#[test]
fn owned_object_identity_is_exclusive_across_instances_and_after_handle_release() {
    let (runtime, first, second, referent) = alias_fixture(true);
    let handle = open(&runtime, first, "object", Value::Null);
    assert_alias_conflict(&runtime, first);
    assert_alias_conflict(&runtime, second);
    // A changed descriptor cannot re-export an owned referent as borrowed.
    referent
        .lock()
        .unwrap()
        .owned
        .store(false, Ordering::SeqCst);
    assert_alias_conflict(&runtime, second);
    assert_eq!(runtime.records.lock().unwrap().resources.len(), 1);
    close(&runtime, first, "object", handle);
    assert_eq!(referent.lock().unwrap().closes.load(Ordering::SeqCst), 1);
    assert_alias_conflict(&runtime, second);
    assert!(runtime.records.lock().unwrap().resources.is_empty());
    finish(&runtime, first);
    finish(&runtime, second);
}

#[test]
fn borrowed_aliases_allow_release_then_ownership_and_weak_history_expires_safely() {
    let (runtime, first, second, referent) = alias_fixture(false);
    let one = open(&runtime, first, "object", Value::Null);
    let two = open(&runtime, second, "object", Value::Null);
    referent.lock().unwrap().owned.store(true, Ordering::SeqCst);
    assert_alias_conflict(&runtime, first);
    close(&runtime, first, "object", one);
    assert_alias_conflict(&runtime, first);
    close(&runtime, second, "object", two);
    assert_eq!(referent.lock().unwrap().closes.load(Ordering::SeqCst), 0);
    let owned = open(&runtime, second, "object", Value::Null);
    close(&runtime, second, "object", owned);
    assert_eq!(referent.lock().unwrap().closes.load(Ordering::SeqCst), 1);
    let old_identity = runtime.records.lock().unwrap().owned_objects[0].clone();
    *referent.lock().unwrap() = AliasedObject::new(true);
    assert_eq!(old_identity.strong_count(), 0);
    let fresh = open(&runtime, first, "object", Value::Null);
    {
        let records = runtime.records.lock().unwrap();
        assert_eq!(records.owned_objects.len(), 1);
        assert!(!old_identity.ptr_eq(&records.owned_objects[0]));
    }
    close(&runtime, first, "object", fresh);
    finish(&runtime, first);
    finish(&runtime, second);
}
