//! Explicit views of real `cordis::Plugin` declared services in this Driver's graph.
//! Rust values never cross JSON; adapters borrow the publication's original slot.
use super::*;
use cordis::runtime::static_host::{
    StaticBinding, StaticEpisode, StaticPlugin, StaticStart, TypedSlot,
};
use cordis::{Context as TypedContext, Plugin, Port, ServiceKey};
use std::any::{Any, TypeId};
use std::collections::BTreeSet;

/// A JSON/stream/object view of a typed service, with no independent lifecycle.
/// Calls receive the same Arc that a typed consumer obtains from Setup::get.
pub trait TypedService<T: Any + Send + Sync>: Send + Sync + 'static {
    fn methods(&self) -> Vec<MethodDescriptor>;
    fn call_sync(&self, _value: Arc<T>, _method: &str, _args: Value) -> PluginResult<Value> {
        Err("UnknownSyncMethod".into())
    }
    fn call_async(
        &self,
        _ctx: PluginContext,
        _value: Arc<T>,
        _method: &str,
        _args: Value,
    ) -> PluginFuture {
        Box::pin(async { Err("UnknownAsyncMethod".into()) })
    }
    fn open_stream(
        &self,
        _value: Arc<T>,
        _method: &str,
        _args: Value,
    ) -> PluginResult<Arc<dyn PluginStream>> {
        Err("UnknownStreamMethod".into())
    }
    fn open_object(
        &self,
        _value: Arc<T>,
        _method: &str,
        _args: Value,
    ) -> PluginResult<Arc<dyn PluginObject>> {
        Err("UnknownObjectMethod".into())
    }
}
trait ServiceView: Send + Sync {
    fn methods(&self) -> Vec<MethodDescriptor>;
    fn sync(&self, slot: &TypedSlot, method: &str, args: Value) -> PluginResult<Value>;
    fn asynchronous(
        &self,
        ctx: PluginContext,
        slot: &TypedSlot,
        method: &str,
        args: Value,
    ) -> PluginFuture;
    fn stream(
        &self,
        slot: &TypedSlot,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginStream>>;
    fn object(
        &self,
        slot: &TypedSlot,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginObject>>;
}
struct View<T, A> {
    adapter: A,
    marker: std::marker::PhantomData<fn() -> T>,
}
impl<T: Any + Send + Sync, A: TypedService<T>> ServiceView for View<T, A> {
    fn methods(&self) -> Vec<MethodDescriptor> {
        self.adapter.methods()
    }
    fn sync(&self, slot: &TypedSlot, method: &str, args: Value) -> PluginResult<Value> {
        self.adapter
            .call_sync(slot.get::<T>().ok_or("TypedServiceMismatch")?, method, args)
    }
    fn asynchronous(
        &self,
        ctx: PluginContext,
        slot: &TypedSlot,
        method: &str,
        args: Value,
    ) -> PluginFuture {
        match slot.get::<T>() {
            Some(value) => self.adapter.call_async(ctx, value, method, args),
            None => Box::pin(async { Err("TypedServiceMismatch".into()) }),
        }
    }
    fn stream(
        &self,
        slot: &TypedSlot,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginStream>> {
        self.adapter
            .open_stream(slot.get::<T>().ok_or("TypedServiceMismatch")?, method, args)
    }
    fn object(
        &self,
        slot: &TypedSlot,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginObject>> {
        self.adapter
            .open_object(slot.get::<T>().ok_or("TypedServiceMismatch")?, method, args)
    }
}
#[derive(Clone)]
struct Binding {
    key: u64,
    type_id: TypeId,
    name: String,
    view: Option<Arc<dyn ServiceView>>,
}
/// An explicit map from real ServiceKey identities to Node service names.
/// The builder constructs one Plugin definition per logical Fiber; restarting
/// that Fiber reuses its FnMut closure. Configuration changes require a new Fiber.
pub struct TypedFactory {
    name: String,
    make: Arc<dyn Fn(Value) -> PluginResult<Plugin> + Send + Sync>,
    bindings: Vec<Binding>,
    service_updates: bool,
}
impl TypedFactory {
    pub fn new(
        name: impl Into<String>,
        make: impl Fn(Value) -> PluginResult<Plugin> + Send + Sync + 'static,
    ) -> Self {
        Self {
            name: name.into(),
            make: Arc::new(make),
            bindings: vec![],
            service_updates: false,
        }
    }
    /// Enable checked declared services and live `AsyncSetup::set/refresh`.
    /// Does not enable `publish`, child plugins, effects or configuration hooks.
    pub fn with_service_updates(mut self) -> Self {
        self.service_updates = true;
        self
    }
    pub fn requires<T: Any + Send + Sync>(
        mut self,
        key: ServiceKey<T>,
        name: impl Into<String>,
    ) -> Self {
        self.bindings.push(Binding {
            key: TypedContext::new().port(key).key,
            type_id: TypeId::of::<T>(),
            name: name.into(),
            view: None,
        });
        self
    }
    pub fn provides<T: Any + Send + Sync>(
        mut self,
        key: ServiceKey<T>,
        name: impl Into<String>,
        adapter: impl TypedService<T>,
    ) -> Self {
        self.bindings.push(Binding {
            key: TypedContext::new().port(key).key,
            type_id: TypeId::of::<T>(),
            name: name.into(),
            view: Some(Arc::new(View {
                adapter,
                marker: std::marker::PhantomData,
            })),
        });
        self
    }
    pub(super) fn descriptor(&self) -> PluginResult<FactoryDescriptor> {
        let mut keys = BTreeSet::new();
        let mut names = BTreeSet::new();
        for binding in &self.bindings {
            if binding.name.is_empty()
                || !keys.insert(binding.key)
                || !names.insert(binding.name.clone())
            {
                return Err("DuplicateTypedBinding".into());
            }
        }
        Ok(FactoryDescriptor {
            name: self.name.clone(),
            inject: self
                .bindings
                .iter()
                .filter(|b| b.view.is_none())
                .map(|b| b.name.clone())
                .collect(),
            services: self
                .bindings
                .iter()
                .filter_map(|b| {
                    b.view.as_ref().map(|view| ServiceDescriptor {
                        name: b.name.clone(),
                        methods: view.methods(),
                    })
                })
                .collect(),
        })
    }
    pub(super) fn check_ports(
        &self,
        ports: &BTreeMap<String, cordis_driver::ServicePort>,
    ) -> PluginResult<()> {
        if ports.len() != self.bindings.len()
            || self.bindings.iter().any(|b| !ports.contains_key(&b.name))
        {
            return Err("TypedPortMapMismatch".into());
        }
        let mut seen = BTreeSet::new();
        if ports.values().any(|p| !seen.insert((p.key, p.realm))) {
            return Err("DuplicateTypedPort".into());
        }
        Ok(())
    }
}
pub(super) struct Mount {
    factory: String,
    config: Value,
    ports: BTreeMap<String, cordis_driver::ServicePort>,
    definition: StaticPlugin,
}
/// Data comes only from NativeDriver's committed-publication query.
pub(crate) struct ResolvedImport {
    pub name: String,
    pub port: cordis_driver::ServicePort,
    pub owner: usize,
    pub publication: usize,
}
pub(super) struct Instance {
    episode: StaticEpisode,
    start: Mutex<Option<cordis::runtime::static_host::StaticFuture>>,
    factory: Arc<TypedFactory>,
    ports: BTreeMap<String, cordis_driver::ServicePort>,
    service_dirty: Arc<AtomicBool>,
}
impl Instance {
    pub(super) fn take_service_notification(&self) -> bool {
        self.service_dirty.swap(false, Ordering::AcqRel)
    }
    pub(super) fn check_service(
        &self,
        service: &str,
        realms: &BTreeMap<String, cordis_driver::ServicePort>,
        config: &Value,
    ) -> PluginResult<bool> {
        if !self.factory.service_updates {
            return Err("TypedServiceUpdatesDisabled".into());
        }
        self.factory.check_ports(realms)?;
        // Service keys retain their typed identity; realms are explicitly mapped
        // from the checked consumer's Context by the Node host.
        if self
            .factory
            .bindings
            .iter()
            .any(|binding| realms[&binding.name].key != self.ports[&binding.name].key)
        {
            return Err("TypedCheckPortMismatch".into());
        }
        let context = TypedContext::with_realms(
            self.factory
                .bindings
                .iter()
                .map(|binding| (binding.key, realms[&binding.name].realm)),
        );
        let (_, slot) = self.value(service)?;
        // A pending notification invalidates this value observation. The next
        // host poll will issue fresh graph check tickets before reactivation.
        if self.service_dirty.load(Ordering::Acquire) {
            return Ok(false);
        }
        let available = slot.accepts(&context, config);
        Ok(available && !self.service_dirty.load(Ordering::Acquire))
    }
    pub(super) fn cancel(&self) {
        self.episode.cancel();
    }
    pub(super) fn check_publication(
        &self,
        service: &str,
        port: cordis_driver::ServicePort,
    ) -> PluginResult<()> {
        if self.ports.get(service) != Some(&port) {
            return Err("TypedPublicationPortMismatch".into());
        }
        Ok(())
    }
    fn value(&self, service: &str) -> PluginResult<(Arc<dyn ServiceView>, TypedSlot)> {
        let binding = self
            .factory
            .bindings
            .iter()
            .find(|b| b.name == service && b.view.is_some())
            .ok_or("UnknownTypedService")?;
        let port = self.ports.get(service).ok_or("TypedPortMapMismatch")?;
        let slot = self.slot(binding.key, binding.type_id, port.realm)?;
        Ok((binding.view.clone().unwrap(), slot))
    }
    fn slot(&self, key: u64, type_id: TypeId, realm: u64) -> PluginResult<TypedSlot> {
        if self.episode.is_closed() {
            return Err("TypedEpisodeClosed".into());
        }
        let slot = self
            .episode
            .provided()?
            .into_iter()
            .find(|(p, _)| p.key == key && p.realm == realm)
            .map(|(_, s)| s)
            .ok_or("TypedImportUnavailable")?;
        if slot.value().as_ref().type_id() != type_id {
            return Err("TypedServiceMismatch".into());
        }
        Ok(slot)
    }
}
impl PluginInstance for Instance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        let future = self.start.lock().unwrap().take();
        let factory = self.factory.clone();
        let episode = self.episode.clone();
        let ports = self.ports.clone();
        Box::pin(async move {
            future.ok_or("TypedSetupAlreadyStarted")?.await?;
            ctx.cancellation().check()?;
            let supplied = episode.provided()?;
            // Validate every slot before publishing any interface.
            for binding in factory.bindings.iter().filter(|b| b.view.is_some()) {
                let native = ports[&binding.name];
                let slot = supplied
                    .iter()
                    .find(|(p, _)| p.key == binding.key && p.realm == native.realm)
                    .ok_or("MissingTypedProvision")?;
                if slot.1.value().as_ref().type_id() != binding.type_id {
                    return Err("TypedServiceMismatch".into());
                }
            }
            for binding in factory.bindings.iter().filter(|b| b.view.is_some()) {
                let native = ports[&binding.name];
                let slot = supplied
                    .iter()
                    .find(|(p, _)| p.key == binding.key && p.realm == native.realm)
                    .unwrap();
                ctx.provide_with_check(&binding.name, slot.1.has_check())
                    .await?;
            }
            Ok(Value::Null)
        })
    }
    fn cleanup(&self, _ctx: PluginContext) -> PluginFuture {
        let future = self.episode.cleanup();
        Box::pin(async move {
            future?.await?;
            Ok(Value::Null)
        })
    }
    fn call_sync(&self, service: &str, method: &str, args: Value) -> PluginResult<Value> {
        let (view, slot) = self.value(service)?;
        view.sync(&slot, method, args)
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginFuture {
        match self.value(service) {
            Ok((view, slot)) => view.asynchronous(ctx, &slot, method, args),
            Err(error) => Box::pin(async move { Err(error) }),
        }
    }
    fn open_stream(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginStream>> {
        let (view, slot) = self.value(service)?;
        view.stream(&slot, method, args)
    }
    fn open_object(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn PluginObject>> {
        let (view, slot) = self.value(service)?;
        view.object(&slot, method, args)
    }
}
impl Backend {
    pub fn typed_descriptor(
        &self,
        factory: &str,
        ports: &BTreeMap<String, cordis_driver::ServicePort>,
    ) -> PluginResult<Option<FactoryDescriptor>> {
        let (descriptor, registered) = self
            .registry
            .factories
            .get(factory)
            .ok_or("UnknownFactory")?;
        match registered {
            RegisteredFactory::Native(_) => Ok(None),
            RegisteredFactory::Typed(factory) => {
                factory.check_ports(ports)?;
                Ok(Some(descriptor.clone()))
            }
        }
    }
    pub(super) fn typed_instance(
        &mut self,
        id: usize,
        generation: u64,
        factory: Arc<TypedFactory>,
        config: Value,
        ports: BTreeMap<String, cordis_driver::ServicePort>,
        resolved: Vec<ResolvedImport>,
    ) -> PluginResult<Arc<Instance>> {
        factory.check_ports(&ports)?;
        let mut imports = Vec::new();
        for binding in factory.bindings.iter().filter(|b| b.view.is_none()) {
            let resolved = resolved
                .iter()
                .find(|r| r.name == binding.name && r.port == ports[&binding.name])
                .ok_or("TypedImportUnavailable")?;
            let provider = self
                .sessions
                .values()
                .find(|s| {
                    s.id == resolved.owner
                        && s.publications.get(&binding.name)
                            == Some(&(resolved.publication, resolved.port))
                })
                .ok_or("TypedProviderRequired")?;
            let typed = provider.typed.as_ref().ok_or("TypedProviderRequired")?;
            let original = typed
                .factory
                .bindings
                .iter()
                .find(|b| b.name == binding.name && b.view.is_some())
                .ok_or("TypedImportUnavailable")?;
            if original.key != binding.key || original.type_id != binding.type_id {
                return Err("TypedServiceMismatch".into());
            }
            imports.push(StaticBinding {
                port: Port {
                    key: binding.key,
                    realm: resolved.port.realm,
                },
                provider: resolved.owner,
                slot: typed.slot(binding.key, binding.type_id, resolved.port.realm)?,
            });
        }
        if let Some(mount) = self.typed_mounts.get(&id) {
            if mount.factory != factory.name || mount.config != config || mount.ports != ports {
                return Err("TypedMountDefinitionChanged".into());
            }
        } else {
            let definition = StaticPlugin::new((factory.make)(config.clone())?)?;
            let declarations = definition.declarations();
            let expected = |owned: bool| {
                factory
                    .bindings
                    .iter()
                    .filter(|b| b.view.is_some() == owned)
                    .map(|b| b.key)
                    .collect::<BTreeSet<_>>()
            };
            if declarations
                .dependencies
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                != expected(false)
                || declarations
                    .provisions
                    .iter()
                    .copied()
                    .collect::<BTreeSet<_>>()
                    != expected(true)
            {
                return Err("TypedDeclarationsMismatch".into());
            }
            self.typed_mounts.insert(
                id,
                Mount {
                    factory: factory.name.clone(),
                    config,
                    ports: ports.clone(),
                    definition,
                },
            );
        }
        let context = TypedContext::with_realms(
            factory
                .bindings
                .iter()
                .map(|b| (b.key, ports[&b.name].realm)),
        );
        let dirty = Arc::new(AtomicBool::new(false));
        let definition = &mut self.typed_mounts.get_mut(&id).unwrap().definition;
        let StaticStart { episode, setup } = if factory.service_updates {
            let dirty = dirty.clone();
            let notify = self.notify.clone();
            let notifications = self.service_notifications.clone();
            definition.begin_with_service_updates(
                id,
                generation,
                context,
                imports,
                Arc::new(move || {
                    if !dirty.swap(true, Ordering::AcqRel) {
                        notifications.store(true, Ordering::Release);
                        notify();
                    }
                }),
            )?
        } else {
            definition.begin(id, generation, context, imports)?
        };
        Ok(Arc::new(Instance {
            episode,
            start: Mutex::new(Some(setup)),
            factory,
            ports,
            service_dirty: dirty,
        }))
    }
    pub fn typed_check(
        &self,
        session: u64,
        service: &str,
        realms: &BTreeMap<String, cordis_driver::ServicePort>,
        config: &Value,
    ) -> PluginResult<bool> {
        let session = self.sessions.get(&session).ok_or("UnknownSession")?;
        session.cancellation.check()?;
        session
            .typed
            .as_ref()
            .ok_or("TypedProviderRequired")?
            .check_service(service, realms, config)
    }
    pub(super) fn typed_notifications(&self) -> Vec<Value> {
        // Ordinary calls and idle polls do not scan the retained session graph.
        if !self.service_notifications.swap(false, Ordering::AcqRel) {
            return Vec::new();
        }
        self.sessions.iter().filter_map(|(id, session)| {
            let typed = session.typed.as_ref()?;
            if !typed.take_service_notification() || session.cancellation.is_cancelled() || typed.episode.is_closed() {
                return None;
            }
            Some(serde_json::json!({"session":id.to_string(), "generation":session.generation.to_string(),
                "ports":session.publications.values().map(|(_,port)| port).collect::<Vec<_>>() }))
        }).collect()
    }
    pub fn forget_typed(&mut self, id: usize) -> PluginResult<()> {
        if self.sessions.values().any(|s| s.id == id) {
            return Err("SessionBusy".into());
        }
        self.typed_mounts.remove(&id);
        Ok(())
    }
}
