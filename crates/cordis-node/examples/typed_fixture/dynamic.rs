//! Dynamic typed publication and child acceptance fixtures on the native graph.
use super::*;
use cordis::ServiceHandle;
use cordis_node::plugin::{
    ObjectDescriptor, ObjectOwnership, PluginObject, PluginStream, StreamFuture,
};

struct DynamicValue(i64);
struct DynamicView;
impl TypedService<DynamicValue> for DynamicView {
    fn methods(&self) -> Vec<MethodDescriptor> {
        vec![MethodDescriptor {
            name: "read".into(),
            kind: MethodKind::Sync,
        }]
    }
    fn call_sync(&self, value: Arc<DynamicValue>, _: &str, _: Value) -> PluginResult<Value> {
        Ok(json!(value.0))
    }
}
struct Reader {
    setup: AsyncSetup,
    key: ServiceKey<DynamicValue>,
    original: Arc<DynamicValue>,
}
struct ReaderView;
impl TypedService<Reader> for ReaderView {
    fn methods(&self) -> Vec<MethodDescriptor> {
        vec![MethodDescriptor {
            name: "read".into(),
            kind: MethodKind::Sync,
        }]
    }
    fn call_sync(&self, reader: Arc<Reader>, _: &str, _: Value) -> PluginResult<Value> {
        let current = reader.setup.get(reader.key)?;
        Ok(
            json!({"current":current.0,"original":reader.original.0,"sameArc":Arc::ptr_eq(&current,&reader.original)}),
        )
    }
}
struct Manager {
    setup: AsyncSetup,
    control: Arc<Control>,
    key: ServiceKey<DynamicValue>,
    reader: ServiceKey<Reader>,
    handles: Mutex<BTreeMap<String, ServiceHandle<DynamicValue>>>,
}
impl Manager {
    fn handle(&self, label: &str) -> PluginResult<ServiceHandle<DynamicValue>> {
        self.handles
            .lock()
            .unwrap()
            .get(label)
            .cloned()
            .ok_or_else(|| "unknown publication handle".into())
    }
    fn publish(&self, label: String, initial: i64, checked: bool) -> PluginResult<()> {
        if self.handles.lock().unwrap().contains_key(&label) {
            return Err("handle label already used".into());
        }
        let key = self.key;
        let realm = self.setup.context().port(key).realm;
        let handle = if checked {
            self.setup.publish_checked(
                key,
                DynamicValue(initial),
                move |value, context, config| {
                    context.port(key).realm == realm
                        && value.0 >= config["minimum"].as_i64().unwrap_or(0)
                },
            )?
        } else {
            self.setup.publish(key, DynamicValue(initial))?
        };
        self.handles.lock().unwrap().insert(label, handle);
        Ok(())
    }
}
struct ManagerView;
impl TypedService<Manager> for ManagerView {
    fn methods(&self) -> Vec<MethodDescriptor> {
        let mut methods = [
            "publish",
            "publishUnknown",
            "mountUnknown",
            "set",
            "dispose",
            "status",
            "mount",
            "mountIsolated",
            "mountWaiting",
            "mountFailing",
        ]
        .into_iter()
        .map(|name| MethodDescriptor {
            name: name.into(),
            kind: MethodKind::Sync,
        })
        .collect::<Vec<_>>();
        methods.push(MethodDescriptor {
            name: "join".into(),
            kind: MethodKind::Async,
        });
        methods.push(MethodDescriptor {
            name: "joinStream".into(),
            kind: MethodKind::Stream,
        });
        methods.push(MethodDescriptor {
            name: "joinObject".into(),
            kind: MethodKind::Object,
        });
        methods
    }
    fn call_sync(&self, manager: Arc<Manager>, method: &str, args: Value) -> PluginResult<Value> {
        let label = args[0].as_str().ok_or("requires label")?.to_owned();
        match method {
            "publish" => manager.publish(
                label,
                args[1].as_i64().ok_or("requires value")?,
                args[2] == true,
            )?,
            "publishUnknown" => {
                let key = ServiceKey::<DynamicValue>::new("uncatalogued-dynamic");
                let handle = manager.setup.publish(key, DynamicValue(91))?;
                manager.handles.lock().unwrap().insert(label, handle);
            }
            "mountUnknown" => {
                let key = ServiceKey::<DynamicValue>::new("uncatalogued-child");
                let control = manager.control.clone();
                manager.setup.mount(
                    Plugin::new("uncatalogued-child", move |setup| {
                        control.record(json!({"phase":"unknown-child:setup"}));
                        setup.provide(key, DynamicValue(92))?;
                        Ok(())
                    })
                    .provides(key),
                )?;
            }
            "set" => manager
                .handle(&label)?
                .set(DynamicValue(args[1].as_i64().ok_or("requires value")?))?,
            "dispose" => manager.handle(&label)?.dispose(),
            "status" => {
                let handle = manager.handle(&label)?;
                return Ok(
                    json!({"id":handle.id().map(|id|id.to_string()),"initialized":handle.initialized(),"finished":handle.finished(),"errors":handle.errors(),"value":handle.get()?.0}),
                );
            }
            "mount" | "mountFailing" => {
                let control = manager.control.clone();
                let fail = method == "mountFailing";
                manager.setup.mount(Plugin::new(
                    format!("dynamic-child:{label}"),
                    move |setup| {
                        control.record(json!({"phase":"dynamic-child:setup","label":label}));
                        let control = control.clone();
                        let label = label.clone();
                        setup.on_cleanup(move || {
                            control.record(json!({"phase":"dynamic-child:cleanup","label":label}));
                            if fail {
                                Err("dynamic child inverse failed".into())
                            } else {
                                Ok(())
                            }
                        });
                        Ok(())
                    },
                ))?;
            }
            "mountWaiting" => {
                let control = manager.control.clone();
                manager.setup.mount(Plugin::new_async(format!("dynamic-wait:{label}"), move |setup| {
                    let control = control.clone(); let label = label.clone();
                    async move {
                        control.record(json!({"phase":"dynamic-child:waiting","label":label}));
                        control.wait(format!("dynamic:{label}")).await;
                        let cleanup_control = control.clone(); let cleanup_label = label.clone();
                        setup.on_cleanup(move || {
                            cleanup_control.record(json!({"phase":"dynamic-child:late-cleanup","label":cleanup_label})); Ok(())
                        })?;
                        let cancelled = setup.is_cancelled();
                        let late_rejected = setup.mount(Plugin::new("late-child", |_| Ok(()))).is_err();
                        control.record(json!({"phase":"dynamic-child:landed","label":label,"cancelled":cancelled,"lateRejected":late_rejected}));
                        Ok(())
                    }
                }))?;
            }
            "mountIsolated" => {
                let key = manager.key;
                let reader_key = manager.reader;
                let initial = args[1].as_i64().ok_or("requires value")?;
                let context = manager.setup.context().isolate(key).isolate(reader_key);
                let control = manager.control.clone();
                manager.setup.mount_in(&context, Plugin::new(format!("dynamic-isolated:{label}"), move |setup| {
                    let original = setup.provide(key, DynamicValue(initial))?;
                    let control = control.clone(); let label = label.clone();
                    setup.mount(Plugin::new(format!("dynamic-nested:{label}"), move |setup| {
                        let actual = setup.get(key)?;
                        control.record(json!({"phase":"dynamic-nested:setup","label":label,"value":actual.0,"sameArc":Arc::ptr_eq(&original,&actual)}));
                        let handle = setup.to_async();
                        setup.provide(reader_key, Reader {setup:handle.clone(),key,original:actual})?;
                        let control=control.clone(); let label=label.clone();
                        setup.on_cleanup(move || {
                            control.record(json!({"phase":"dynamic-nested:cleanup","label":label,"value":handle.get(key)?.0})); Ok(())
                        });
                        Ok(())
                    }).requires(key).provides(reader_key))?;
                    Ok(())
                }).provides(key))?;
            }
            _ => return Err("unknown dynamic manager method".into()),
        }
        Ok(Value::Null)
    }
    fn open_stream(
        &self,
        manager: Arc<Manager>,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginStream>> {
        if method != "joinStream" {
            return Err("unknown dynamic stream".into());
        }
        Ok(Arc::new(JoinResource::new(&manager, &args, "stream")?))
    }
    fn open_object(
        &self,
        manager: Arc<Manager>,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginObject>> {
        if method != "joinObject" {
            return Err("unknown dynamic object".into());
        }
        Ok(Arc::new(JoinResource::new(&manager, &args, "object")?))
    }
    fn call_async(
        &self,
        _ctx: PluginContext,
        manager: Arc<Manager>,
        method: &str,
        args: Value,
    ) -> PluginFuture {
        let result = if method == "join" {
            args[0]
                .as_str()
                .ok_or_else(|| "requires label".into())
                .and_then(|label| manager.handle(label))
        } else {
            Err("unknown async dynamic method".into())
        };
        Box::pin(async move {
            result?.join().await?;
            Ok(Value::Null)
        })
    }
}
struct JoinResource {
    handle: ServiceHandle<DynamicValue>,
    control: Arc<Control>,
    label: String,
    kind: &'static str,
    check_close: bool,
}
impl JoinResource {
    fn new(manager: &Manager, args: &Value, kind: &'static str) -> PluginResult<Self> {
        let label = args[0].as_str().ok_or("requires label")?;
        Ok(Self {
            handle: manager.handle(label)?,
            control: manager.control.clone(),
            label: label.into(),
            kind,
            check_close: args[1] == true,
        })
    }
    fn close_future(&self) -> PluginFuture {
        let handle = self.handle.clone();
        let control = self.control.clone();
        let label = self.label.clone();
        let kind = self.kind;
        let check_close = self.check_close;
        Box::pin(async move {
            if check_close {
                let error = handle
                    .join()
                    .await
                    .err()
                    .ok_or("cyclic close join unexpectedly completed")?;
                if error != "ReentrantServiceJoin" {
                    return Err(error);
                }
                control.record(json!({"phase":"dynamic-resource:close-join-rejected","kind":kind,"label":label}));
            }
            control.record(json!({"phase":"dynamic-resource:closed","kind":kind,"label":label}));
            Ok(Value::Null)
        })
    }
}
impl PluginStream for JoinResource {
    fn next(&self, _ctx: PluginContext) -> StreamFuture {
        let handle = self.handle.clone();
        Box::pin(async move {
            handle.join().await?;
            Ok(Some(Value::Null))
        })
    }
    fn close(&self, _ctx: PluginContext) -> PluginFuture {
        self.close_future()
    }
}
impl PluginObject for JoinResource {
    fn descriptor(&self) -> ObjectDescriptor {
        ObjectDescriptor::new("fixture.TypedJoin", ["join"], ObjectOwnership::Owned).unwrap()
    }
    fn call(&self, _ctx: PluginContext, method: &str, _args: Value) -> PluginFuture {
        if method != "join" {
            return Box::pin(async { Err("unknown typed join resource method".into()) });
        }
        let handle = self.handle.clone();
        Box::pin(async move {
            handle.join().await?;
            Ok(Value::Null)
        })
    }
    fn close(&self, _ctx: PluginContext) -> PluginFuture {
        self.close_future()
    }
}
pub(super) fn register(
    registry: &mut FactoryRegistry,
    control_key: ServiceKey<Control>,
) -> PluginResult<()> {
    let key = ServiceKey::<DynamicValue>::new("typedDynamicValue");
    let manager_key = ServiceKey::<Manager>::new("typedDynamicManager");
    let reader = ServiceKey::<Reader>::new("typedDynamicReader");
    registry.register_typed(
        TypedFactory::new("fixture.typedDynamic", move |config| {
            let auto = config["publishDuringSetup"].as_i64();
            let checked = config["checked"] == true;
            Ok(Plugin::new("typed-dynamic-owner", move |setup| {
                let control = setup.get(control_key)?;
                let manager = setup.provide(
                    manager_key,
                    Manager {
                        setup: setup.to_async(),
                        control: control.clone(),
                        key,
                        reader,
                        handles: Mutex::new(BTreeMap::new()),
                    },
                )?;
                setup.on_cleanup(move || {
                    control.record(json!({"phase":"dynamic-owner:cleanup"}));
                    Ok(())
                });
                if let Some(initial) = auto {
                    manager.publish("initial".into(), initial, checked)?;
                }
                Ok(())
            })
            .requires(control_key)
            .provides(manager_key))
        })
        .requires(control_key, "typedControl")
        .provides(manager_key, "typedDynamicManager", ManagerView)
        .child_service(key, "typedDynamicValue", DynamicView)
        .child_service(reader, "typedDynamicReader", ReaderView)
        .with_dynamic_children(),
    )?;
    registry.register_typed(
        TypedFactory::new("fixture.typedDynamicSelfJoin", move |_| {
            Ok(
                Plugin::new_async("typed-self-join", move |setup| async move {
                    let control = setup.get(control_key)?;
                    setup.on_cleanup(move || {
                        control.record(json!({"phase":"dynamic-self-join:cleanup"}));
                        Ok(())
                    })?;
                    let child = setup.publish(key, DynamicValue(17))?;
                    child.join().await
                })
                .requires(control_key),
            )
        })
        .requires(control_key, "typedControl")
        .child_service(key, "typedDynamicValue", DynamicView)
        .with_dynamic_children(),
    )?;
    registry.register_typed(
        TypedFactory::new("fixture.typedDynamicReader", move |_| {
            Ok(Plugin::new("typed-dynamic-reader", move |setup| {
                let control = setup.get(control_key)?;
                let manager = setup.get(manager_key)?;
                let original = setup.get(key)?;
                let same = manager.handles.lock().unwrap().values().any(|handle| {
                    handle
                        .get()
                        .is_ok_and(|value| Arc::ptr_eq(&value, &original))
                });
                control.record(json!({"phase":"dynamic-reader:setup","sameArc":same}));
                let handle = setup.to_async();
                setup.provide(
                    reader,
                    Reader {
                        setup: handle.clone(),
                        key,
                        original,
                    },
                )?;
                setup.on_cleanup(move || {
                    control.record(
                        json!({"phase":"dynamic-reader:cleanup","value":handle.get(key)?.0}),
                    );
                    Ok(())
                });
                Ok(())
            })
            .requires(control_key)
            .requires(manager_key)
            .requires(key)
            .provides(reader))
        })
        .requires(control_key, "typedControl")
        .requires(manager_key, "typedDynamicManager")
        .requires(key, "typedDynamicValue")
        .provides(reader, "typedDynamicReader", ReaderView),
    )?;
    Ok(())
}
