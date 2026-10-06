//! Native definitions/control records, not a scheduler. Every lifecycle state
//! below is acknowledged by the existing NativeDriver and ordinary JS Fiber.
use super::super::Backend;
use super::*;
use cordis_plugin_api::ChildStatus;
use std::sync::Weak;

type Ports = BTreeMap<String, cordis_driver::ServicePort>;
#[derive(Clone)]
enum Target {
    Module(String),
    Retained(u64),
}
impl Target {
    fn wire(&self) -> Value {
        match self {
            Self::Module(factory) => json!({"kind":"module","factory":factory}),
            Self::Retained(definition) => json!({"kind":"retained","definition":definition}),
        }
    }
}
#[derive(Default)]
struct Progress {
    id: Option<usize>,
    mounted: bool,
    mount_sent: bool,
    initialized: bool,
    retiring: bool,
    retire_sent: bool,
    retry: bool,
    removed: bool,
    finalized: bool,
    cleanup_failed: bool,
    error: Option<String>,
    history_error: Option<String>,
    waiters: Vec<Waker>,
    ports: Ports,
}
struct Child {
    key: u64,
    parent_session: u64,
    parent: Weak<InstanceLease>,
    target: Target,
    descriptor: FactoryDescriptor,
    config: Value,
    inherited: Mutex<Vec<(String, cordis_driver::ServicePort)>>,
    progress: Mutex<Progress>,
}
impl Child {
    fn factory(&self) -> String {
        format!("@cordis/native-child/{}", self.key)
    }
    fn status(&self) -> ChildStatus {
        let state = self.progress.lock().unwrap();
        ChildStatus {
            id: state.id.map(|id| id.to_string()),
            initialized: state.initialized,
            retiring: state.retiring,
            removed: state.removed,
            cleanup_failed: state.cleanup_failed,
            error: state.error.clone(),
        }
    }
    fn wake(&self) {
        let waiters = std::mem::take(&mut self.progress.lock().unwrap().waiters);
        for waiter in waiters {
            waiter.wake();
        }
    }
}
#[derive(Default)]
struct Records {
    next: u64,
    children: BTreeMap<u64, Arc<Child>>,
}
pub(crate) struct Children {
    records: Mutex<Records>,
    dirty: AtomicBool,
    notify: Arc<dyn Fn() + Send + Sync>,
}
#[derive(Clone, Copy)]
pub(super) enum Operation {
    Status,
    Ready,
    Retire,
    Join,
    Retry,
}
impl Children {
    pub(crate) fn new(notify: Arc<dyn Fn() + Send + Sync>) -> Self {
        Self {
            records: Mutex::new(Records::default()),
            dirty: AtomicBool::new(false),
            notify,
        }
    }
    fn changed(&self) {
        self.dirty.store(true, Ordering::Release);
        (self.notify)();
    }
    fn get(&self, id: u64) -> PluginResult<Arc<Child>> {
        self.records
            .lock()
            .unwrap()
            .children
            .get(&id)
            .cloned()
            .ok_or("UnknownNativeChild".into())
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.records.lock().unwrap().children.is_empty()
    }
    pub(super) fn mount(
        self: &Arc<Self>,
        parent: Arc<InstanceLease>,
        context: PluginContext,
        factory: Option<String>,
        definition: Option<u64>,
        config: Value,
    ) -> Pin<Box<dyn Future<Output = PluginResult<u64>> + Send>> {
        let children = self.clone();
        Box::pin(async move {
            let prepare = (|| -> PluginResult<(Target, FactoryDescriptor)> {
                if context.cleanup {
                    return Err("CleanupCannotMountChild".into());
                }
                context.cancellation.check()?;
                if !context.alive.load(Ordering::Acquire) {
                    return Err("ActionClosed".into());
                }
                let (target, descriptor) = if let Some(factory) = factory {
                    let descriptor = parent
                        .module
                        .description
                        .factories
                        .iter()
                        .find(|item| item.name == factory)
                        .cloned()
                        .ok_or("UnknownNativeChildFactory")?;
                    (Target::Module(factory), descriptor)
                } else {
                    let definition = definition.ok_or("NativeChildDefinitionRequired")?;
                    let value=parent.module.request(json!({"op":"describe_definition","parent":parent.handle,"definition":definition}))?;
                    let descriptor: FactoryDescriptor =
                        serde_json::from_value(value).map_err(|_| "NativeChildDescriptor")?;
                    let mut registry = FactoryRegistry::new();
                    registry.register(DescriptorOnly(descriptor.clone()))?;
                    (Target::Retained(definition), descriptor)
                };
                Ok((target, descriptor))
            })();
            let (target, descriptor) =
                prepare.map_err(|error| reject_definition(&parent, definition, error))?;
            let child = {
                let mut records = children.records.lock().unwrap();
                records.next = records.next.checked_add(1).ok_or_else(|| {
                    reject_definition(&parent, definition, "NativeChildCapacity".into())
                })?;
                let child = Arc::new(Child {
                    key: records.next,
                    parent_session: context.session,
                    parent: Arc::downgrade(&parent),
                    target,
                    descriptor,
                    config,
                    inherited: Mutex::new(Vec::new()),
                    progress: Mutex::new(Progress::default()),
                });
                records.children.insert(child.key, child.clone());
                child
            };
            children.changed();
            std::future::poll_fn(|cx| {
                let mut state = child.progress.lock().unwrap();
                if state.mounted {
                    return Poll::Ready(Ok(child.key));
                }
                if let Some(error) = &state.error {
                    return Poll::Ready(Err(error.clone()));
                }
                if !state.waiters.iter().any(|w| w.will_wake(cx.waker())) {
                    state.waiters.push(cx.waker().clone());
                }
                Poll::Pending
            })
            .await
        })
    }
    pub(super) fn operation(
        self: &Arc<Self>,
        parent: Arc<InstanceLease>,
        context: PluginContext,
        id: u64,
        operation: Operation,
    ) -> Pin<Box<dyn Future<Output = PluginResult<ChildStatus>> + Send>> {
        let children = self.clone();
        Box::pin(async move {
            if !context.alive.load(Ordering::Acquire) {
                return Err("ActionClosed".into());
            }
            let child = children.get(id)?;
            let owner = child.parent.upgrade().ok_or("NativeChildOwnerExpired")?;
            if !Arc::ptr_eq(&owner, &parent) || child.parent_session != context.session {
                return Err("NativeChildOwnerMismatch".into());
            }
            let mut requested = false;
            std::future::poll_fn(|cx| {
                let mut state = child.progress.lock().unwrap();
                if matches!(
                    operation,
                    Operation::Ready | Operation::Join | Operation::Retry
                ) && (context.setup
                    || state
                        .id
                        .is_some_and(|id| context.join_blocked.lock().unwrap().contains(&id)))
                {
                    return Poll::Ready(Err("ReentrantServiceJoin".into()));
                }
                match operation {
                    Operation::Status => {
                        drop(state);
                        return Poll::Ready(Ok(child.status()));
                    }
                    Operation::Retire => {
                        state.retiring = true;
                        drop(state);
                        children.changed();
                        return Poll::Ready(Ok(child.status()));
                    }
                    Operation::Retry if !requested => {
                        if !state.cleanup_failed || state.removed {
                            return Poll::Ready(Err("NativeChildCleanupNotRetryable".into()));
                        }
                        requested = true;
                        state.retry = true;
                        state.cleanup_failed = false;
                        state.error = None;
                        drop(state);
                        children.changed();
                        state = child.progress.lock().unwrap();
                    }
                    _ => {}
                }
                if matches!(operation, Operation::Join) && state.finalized {
                    if let Some(error) = &state.history_error {
                        return Poll::Ready(Err(error.clone()));
                    }
                }
                if let Some(error) = &state.error {
                    if matches!(operation, Operation::Ready)
                        || state.cleanup_failed
                        || state.finalized
                    {
                        return Poll::Ready(Err(error.clone()));
                    }
                }
                if matches!(operation, Operation::Ready) && state.initialized
                    || matches!(operation, Operation::Join | Operation::Retry) && state.finalized
                {
                    drop(state);
                    return Poll::Ready(Ok(child.status()));
                }
                if matches!(operation, Operation::Ready) && state.removed {
                    return Poll::Ready(Err("NativeChildRemoved".into()));
                }
                if !state.waiters.iter().any(|w| w.will_wake(cx.waker())) {
                    state.waiters.push(cx.waker().clone());
                }
                Poll::Pending
            })
            .await
        })
    }
    pub(crate) fn release_session(&self, session: u64) {
        self.records.lock().unwrap().children.retain(|_, child| {
            child.parent_session != session || !child.progress.lock().unwrap().finalized
        });
    }
    pub(crate) fn owned_ids(&self, session: u64) -> Vec<usize> {
        self.records
            .lock()
            .unwrap()
            .children
            .values()
            .filter(|child| child.parent_session == session)
            .filter_map(|child| child.progress.lock().unwrap().id)
            .collect()
    }
}
fn bounded_error(error: String) -> String {
    bounded_reverse_result(Err(error)).unwrap_err()
}
pub(super) fn reject_definition(
    parent: &InstanceLease,
    definition: Option<u64>,
    error: String,
) -> String {
    if let Some(definition) = definition {
        if let Err(failure) = parent
            .module
            .request(json!({"op":"drop_definition","parent":parent.handle,"definition":definition}))
        {
            return bounded_error(format!("{error}; NativeDefinitionCleanupFailed: {failure}"));
        }
    }
    bounded_error(error)
}
pub(super) fn metadata(descriptor: &FactoryDescriptor, reference: &str) -> Value {
    let mut value = json!(descriptor);
    value["ref"] = json!(reference);
    value["nativeChildren"] = json!(true);
    value["ports"] = json!(descriptor
        .inject
        .iter()
        .chain(descriptor.services.iter().map(|s| &s.name))
        .collect::<std::collections::BTreeSet<_>>());
    value
}
struct ChildFactory {
    child: Arc<Child>,
    parent: Arc<InstanceLease>,
}
impl PluginFactory for ChildFactory {
    fn descriptor(&self) -> FactoryDescriptor {
        let mut descriptor = self.child.descriptor.clone();
        descriptor.name = self.child.factory();
        descriptor
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        let reply=self.parent.module.request(json!({"op":"create_child","parent":self.parent.handle,"target":self.child.target.wire(),"config":config}))?;
        let handle = handle(&reply, "instance")?;
        self.parent.module.instances.fetch_add(1, Ordering::AcqRel);
        Ok(Arc::new(Instance {
            lease: Arc::new(InstanceLease {
                module: self.parent.module.clone(),
                handle,
                destroyed: AtomicBool::new(false),
                cleaned: AtomicBool::new(false),
                finalization: Finalization::default(),
                children: self.parent.children.clone(),
                checkpoint: checkpoint::InstanceState::new(
                    self.parent.checkpoint.journal.clone(),
                    &self.parent.module,
                    &self.child.descriptor.name,
                    false,
                ),
            }),
            services: self
                .child
                .descriptor
                .services
                .iter()
                .map(|s| s.name.clone())
                .collect(),
        }))
    }
}
impl Backend {
    pub(crate) fn native_start(
        &mut self,
        id: usize,
        generation: u64,
        factory: &str,
        config: Value,
        ports: Ports,
        checkpoint: Option<&str>,
    ) -> PluginResult<Value> {
        let child = self
            .native_children
            .records
            .lock()
            .unwrap()
            .children
            .values()
            .find(|child| child.factory() == factory)
            .cloned();
        if let Some(child) = &child {
            let state = child.progress.lock().unwrap();
            if state.id != Some(id) || state.ports != ports || state.removed {
                return Err("NativeChildMountChanged".into());
            }
        }
        let restore = self.checkpoint_restore(factory, checkpoint)?;
        let result = self.start(id, generation, factory, config)?;
        let session = result["session"].as_str().unwrap().parse::<u64>().unwrap();
        if let Some(restore) = restore {
            self.native_checkpoints.bind_restore(session, restore)?;
        }
        self.sessions.get_mut(&session).unwrap().ports = ports;
        if let Some(child) = child {
            self.sessions.get_mut(&session).unwrap().inherited =
                child.inherited.lock().unwrap().clone();
        }
        Ok(result)
    }
    pub(crate) fn native_child_actions(&mut self) -> Vec<Value> {
        if !self.native_children.dirty.swap(false, Ordering::AcqRel) {
            return Vec::new();
        }
        let records = self
            .native_children
            .records
            .lock()
            .unwrap()
            .children
            .values()
            .cloned()
            .collect::<Vec<_>>();
        let mut actions = Vec::new();
        for child in records {
            let mut state = child.progress.lock().unwrap();
            if !state.mount_sent {
                state.mount_sent = true;
                drop(state);
                let prepared = (|| -> PluginResult<Value> {
                    let parent = self
                        .sessions
                        .get(&child.parent_session)
                        .ok_or("UnknownSession")?;
                    let lease = child.parent.upgrade().ok_or("NativeChildOwnerExpired")?;
                    let declared = parent
                        .descriptor
                        .inject
                        .iter()
                        .chain(parent.descriptor.services.iter().map(|s| &s.name))
                        .collect::<std::collections::BTreeSet<_>>();
                    let anchors = parent
                        .ports
                        .iter()
                        .filter(|(name, _)| {
                            !declared.contains(name) && name.starts_with("__cordis_native_anchor_")
                        })
                        .collect::<Vec<_>>();
                    if anchors.len() != 1 {
                        return Err("NativeOwnerAnchorRequired".into());
                    }
                    let mut inherited = parent.inherited.clone();
                    inherited.extend(parent.descriptor.inject.iter().filter_map(|name| {
                        parent.ports.get(name).map(|port| (name.clone(), *port))
                    }));
                    inherited.push((anchors[0].0.clone(), *anchors[0].1));
                    inherited.sort_by_key(|(name, port)| (name.clone(), port.key, port.realm));
                    inherited.dedup();
                    *child.inherited.lock().unwrap() = inherited.clone();
                    let mut factory = metadata(&child.descriptor, &child.factory());
                    factory["inherited"] =
                        json!(inherited.iter().map(|(_, port)| port).collect::<Vec<_>>());
                    self.registry.register(ChildFactory {
                        child: child.clone(),
                        parent: lease,
                    })?;
                    Ok(
                        json!({"kind":"mount","native":true,"session":child.parent_session.to_string(),"child":child.key.to_string(),"factory":factory,"config":child.config}),
                    )
                })();
                match prepared {
                    Ok(action) => actions.push(action),
                    Err(error) => {
                        let _ = self.native_child_rejected(&child.key.to_string(), error);
                    }
                }
                continue;
            }
            if let Some(id) = state.id {
                if state.retry {
                    state.retry = false;
                    actions.push(json!({"kind":"retry","native":true,"session":child.parent_session.to_string(),"child":child.key.to_string(),"id":id.to_string()}));
                } else if state.retiring && !state.retire_sent && !state.removed {
                    state.retire_sent = true;
                    actions.push(json!({"kind":"retire","native":true,"session":child.parent_session.to_string(),"child":child.key.to_string(),"id":id.to_string()}));
                }
            }
        }
        actions
    }
    fn native_child(&self, key: &str) -> PluginResult<Arc<Child>> {
        self.native_children
            .get(key.parse().map_err(|_| "InvalidNativeChild")?)
    }
    pub(crate) fn native_child_owner(
        &self,
        key: &str,
    ) -> PluginResult<(usize, u64, Option<usize>)> {
        let child = self.native_child(key)?;
        let (owner, generation) = self.owner(child.parent_session)?;
        let id = child.progress.lock().unwrap().id;
        Ok((owner, generation, id))
    }
    pub(crate) fn native_child_mounted(
        &mut self,
        key: &str,
        id: usize,
        ports: Ports,
    ) -> PluginResult<()> {
        let child = self.native_child(key)?;
        {
            let mut state = child.progress.lock().unwrap();
            if state.mounted {
                return Err("NativeChildAlreadyMounted".into());
            }
            state.id = Some(id);
            state.mounted = true;
            state.ports = ports.clone();
        }
        let declared = child
            .descriptor
            .inject
            .iter()
            .chain(child.descriptor.services.iter().map(|s| &s.name))
            .collect::<std::collections::BTreeSet<_>>();
        let valid = declared.iter().all(|name| ports.contains_key(*name));
        let extra = ports
            .keys()
            .filter(|name| !declared.contains(name))
            .collect::<Vec<_>>();
        if !valid || extra.len() != 1 || !extra[0].starts_with("__cordis_native_anchor_") {
            self.native_child_aborted(key, "NativeChildPortsInvalid".into())?;
            return Err("NativeChildPortsInvalid".into());
        }
        let provisions = child
            .descriptor
            .services
            .iter()
            .map(|service| ports[&service.name])
            .collect::<Vec<_>>();
        child
            .inherited
            .lock()
            .unwrap()
            .retain(|(_, port)| !provisions.contains(port));
        child.wake();
        self.native_children.changed();
        Ok(())
    }
    pub(crate) fn native_child_observed(
        &self,
        key: &str,
        active: bool,
        error: Option<String>,
        cleanup_failed: bool,
    ) -> PluginResult<()> {
        let child = self.native_child(key)?;
        {
            let mut state = child.progress.lock().unwrap();
            state.initialized = active;
            if let Some(error) = error {
                let error = bounded_error(error);
                state.history_error = Some(error.clone());
                state.error = Some(error);
            } else if active && !cleanup_failed {
                state.error = None;
            }
            state.cleanup_failed = cleanup_failed;
        }
        child.wake();
        Ok(())
    }
    pub(crate) fn native_child_aborted(&self, key: &str, error: String) -> PluginResult<()> {
        let child = self.native_child(key)?;
        {
            let mut state = child.progress.lock().unwrap();
            let error = bounded_error(error);
            state.history_error = Some(error.clone());
            state.error = Some(error);
            state.retiring = true;
        }
        child.wake();
        self.native_children.changed();
        Ok(())
    }
    pub(crate) fn native_child_rejected(&mut self, key: &str, error: String) -> PluginResult<()> {
        let child = self.native_child(key)?;
        if child.progress.lock().unwrap().mounted {
            return Err("NativeChildAlreadyMounted".into());
        }
        let parent = child.parent.upgrade().ok_or("NativeChildOwnerExpired")?;
        let finalized = match child.target {
            Target::Retained(definition) => parent
                .module
                .request(
                    json!({"op":"drop_definition","parent":parent.handle,"definition":definition}),
                )
                .map(|_| ()),
            Target::Module(_) => Ok(()),
        };
        {
            let mut state = child.progress.lock().unwrap();
            state.error = Some(bounded_error(
                finalized.as_ref().err().cloned().unwrap_or(error),
            ));
            state.removed = true;
            state.finalized = finalized.is_ok();
            state.cleanup_failed = finalized.is_err();
        }
        if finalized.is_ok() {
            self.registry.factories.remove(&child.factory());
        }
        child.wake();
        finalized
    }
    pub(crate) fn native_child_removed(&mut self, id: usize) -> PluginResult<()> {
        let children = self
            .native_children
            .records
            .lock()
            .unwrap()
            .children
            .values()
            .cloned()
            .collect::<Vec<_>>();
        let Some(child) = children
            .into_iter()
            .find(|child| child.progress.lock().unwrap().id == Some(id))
        else {
            return Ok(());
        };
        {
            let mut state = child.progress.lock().unwrap();
            if state.finalized {
                return Ok(());
            }
            state.removed = true;
            state.initialized = false;
        }
        let parent = child.parent.upgrade().ok_or("NativeChildOwnerExpired")?;
        let result = (|| -> PluginResult<()> {
            parent
                .module
                .request(json!({"op":"child_removed","parent":parent.handle,"child":child.key}))?;
            if let Target::Retained(definition) = child.target {
                parent.module.request(
                    json!({"op":"drop_definition","parent":parent.handle,"definition":definition}),
                )?;
            }
            Ok(())
        })();
        {
            let mut state = child.progress.lock().unwrap();
            state.finalized = result.is_ok();
            if result.is_ok() {
                state.error = None;
                state.cleanup_failed = false;
            }
            if let Err(error) = &result {
                state.error = Some(bounded_error(error.clone()));
                state.cleanup_failed = true;
            }
        }
        if result.is_ok() {
            self.registry.factories.remove(&child.factory());
        }
        child.wake();
        result
    }
}
