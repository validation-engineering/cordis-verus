//! Explicit views of real `cordis::Plugin` declared services in this Driver's graph.
//! Rust values never cross JSON; adapters borrow the publication's original slot.
use super::*;
use cordis::runtime::static_host::{
    StaticBinding, StaticChildControl, StaticEpisode, StaticPlugin, StaticStart, TypedSlot,
};
use cordis::{Context as TypedContext, Plugin, Port, ServiceKey};
use std::any::{Any, TypeId};
use std::collections::BTreeSet;
#[path = "typed_children.rs"]
mod children;
pub(super) use children::Child;

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
    injection_config: Option<Value>,
}
/// An explicit map from real ServiceKey identities to Node service names.
/// The builder constructs one Plugin definition per logical Fiber; restarting
/// that Fiber reuses its FnMut closure. Configuration changes require a new Fiber.
#[derive(Clone)]
pub struct TypedFactory {
    name: String,
    make: Arc<dyn Fn(Value) -> PluginResult<Plugin> + Send + Sync>,
    bindings: Vec<Binding>,
    service_updates: bool,
    pub(super) dynamic_children: bool,
    catalog: Vec<Binding>,
    anchor: Option<Binding>,
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
            dynamic_children: false,
            catalog: vec![],
            anchor: None,
        }
    }
    /// Enable checked declared services and live `AsyncSetup::set/refresh`.
    /// Does not enable `publish`, child plugins, effects or configuration hooks.
    pub fn with_service_updates(mut self) -> Self {
        self.service_updates = true;
        self
    }
    /// Enable original typed publication and child APIs on the shared native graph.
    /// Every service a child may use must be in this factory's explicit catalog.
    pub fn with_dynamic_children(mut self) -> Self {
        self.dynamic_children = true;
        self.service_updates = true;
        self
    }
    /// Register a typed service capability for children without declaring that
    /// the parent itself requires or provides it.
    pub fn child_service<T: Any + Send + Sync>(
        mut self,
        key: ServiceKey<T>,
        name: impl Into<String>,
        adapter: impl TypedService<T>,
    ) -> Self {
        self.catalog.push(Binding {
            key: TypedContext::new().port(key).key,
            type_id: TypeId::of::<T>(),
            name: name.into(),
            view: Some(Arc::new(View {
                adapter,
                marker: std::marker::PhantomData,
            })),
            injection_config: None,
        });
        self
    }
    fn mapped(&self) -> Vec<Binding> {
        let mut bindings = self.catalog.clone();
        for binding in &self.bindings {
            if let Some(existing) = bindings.iter_mut().find(|item| {
                item.key == binding.key
                    && item.name == binding.name
                    && item.type_id == binding.type_id
            }) {
                if existing.view.is_none() {
                    existing.view = binding.view.clone();
                }
            } else {
                bindings.push(binding.clone());
            }
        }
        bindings
    }
    pub(super) fn metadata(&self) -> PluginResult<Value> {
        let mut value = serde_json::json!(self.descriptor()?);
        let injection = self.injection_config();
        if !injection.is_empty() {
            value["injectConfig"] = serde_json::json!(injection);
        }
        value["ports"] =
            serde_json::json!(self.mapped().iter().map(|b| &b.name).collect::<Vec<_>>());
        value["dynamic"] = Value::Bool(self.dynamic_children);
        Ok(value)
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
            injection_config: None,
        });
        self
    }
    /// Bind an original `Plugin::requires_with_config` declaration before the
    /// consumer can be admitted. Its JSON must exactly match the real Plugin.
    /// Values are fixed per registered factory; explicit null overrides any
    /// inherited Node service configuration.
    pub fn requires_with_config<T: Any + Send + Sync>(
        mut self,
        key: ServiceKey<T>,
        name: impl Into<String>,
        config: Value,
    ) -> Self {
        self.bindings.push(Binding {
            key: TypedContext::new().port(key).key,
            type_id: TypeId::of::<T>(),
            name: name.into(),
            view: None,
            injection_config: Some(config),
        });
        self
    }
    pub(super) fn injection_config(&self) -> BTreeMap<String, Value> {
        self.bindings
            .iter()
            .filter_map(|binding| {
                binding
                    .injection_config
                    .as_ref()
                    .map(|config| (binding.name.clone(), config.clone()))
            })
            .collect()
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
            injection_config: None,
        });
        self
    }
    pub(super) fn descriptor(&self) -> PluginResult<FactoryDescriptor> {
        let mut keys = BTreeSet::new();
        let mut names = BTreeSet::new();
        for binding in &self.mapped() {
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
        if ports.len() != self.mapped().len()
            || self.mapped().iter().any(|b| !ports.contains_key(&b.name))
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
    pub(super) factory: String,
    config: Value,
    ports: BTreeMap<String, cordis_driver::ServicePort>,
    definition: StaticPlugin,
    pub(super) adapter: Arc<TypedFactory>,
    context: TypedContext,
    realms: BTreeMap<u64, u64>,
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
    realms: BTreeMap<u64, u64>,
    anchor_slot: TypedSlot,
    dependencies: Vec<(Binding, cordis_driver::ServicePort, u64)>,
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
        typed_realms: BTreeMap<u64, u64>,
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
        let context = TypedContext::with_realms(typed_realms);
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
        if self.factory.anchor.as_ref().is_some_and(|b| b.key == key) {
            return Ok(self.anchor_slot.clone());
        }
        let native = self
            .factory
            .mapped()
            .into_iter()
            .find(|b| b.key == key)
            .ok_or("UnknownTypedKey")?;
        if self.ports[&native.name].realm != realm {
            return Err("TypedRealmMismatch".into());
        }
        let realm = self.realms[&key];
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
        let realms = self.realms.clone();
        Box::pin(async move {
            future.ok_or("TypedSetupAlreadyStarted")?.await?;
            ctx.cancellation().check()?;
            let supplied = episode.provided()?;
            // Validate every slot before publishing any interface.
            for binding in factory.bindings.iter().filter(|b| {
                b.view.is_some() && !factory.anchor.as_ref().is_some_and(|a| a.key == b.key)
            }) {
                let realm = realms[&binding.key];
                let slot = supplied
                    .iter()
                    .find(|(p, _)| p.key == binding.key && p.realm == realm)
                    .ok_or("MissingTypedProvision")?;
                if slot.1.value().as_ref().type_id() != binding.type_id {
                    return Err("TypedServiceMismatch".into());
                }
            }
            for binding in factory.bindings.iter().filter(|b| {
                b.view.is_some() && !factory.anchor.as_ref().is_some_and(|a| a.key == b.key)
            }) {
                let realm = realms[&binding.key];
                let slot = supplied
                    .iter()
                    .find(|(p, _)| p.key == binding.key && p.realm == realm)
                    .unwrap();
                ctx.provide_with_check(&binding.name, slot.1.has_check())
                    .await?;
            }
            if let Some(anchor) = &factory.anchor {
                ctx.provide(&anchor.name).await?;
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
        if let Some(child) = self.typed_children.get(factory) {
            let mounted = self
                .typed_mounts
                .get(&child.control.id().ok_or("TypedChildNotMounted")?)
                .ok_or("TypedChildNotMounted")?;
            mounted.adapter.check_ports(ports)?;
            return Ok(Some(mounted.adapter.descriptor()?));
        }
        let (descriptor, registered) = self
            .registry
            .factories
            .get(factory)
            .ok_or("UnknownFactory")?;
        match registered {
            RegisteredFactory::Native(_) => Ok(None),
            RegisteredFactory::Typed(factory) => {
                let mut expected = ports.clone();
                if factory.dynamic_children {
                    // The exact private anchor is validated against the mount at start.
                    expected.retain(|name, _| factory.mapped().iter().any(|b| &b.name == name));
                    if ports.len() != expected.len() + 1 {
                        return Err("TypedAnchorRequired".into());
                    }
                }
                factory.check_ports(&expected)?;
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
        let realms = if let Some(mount) = self.typed_mounts.get(&id) {
            mount.realms.clone()
        } else {
            factory
                .mapped()
                .into_iter()
                .map(|binding| {
                    let native = ports[&binding.name];
                    let realm = *self
                        .typed_realms
                        .entry((binding.key, native.realm))
                        .or_insert_with(|| {
                            let key = ServiceKey::<()>::new("external-realm");
                            TypedContext::new().isolate(key).port(key).realm
                        });
                    (binding.key, realm)
                })
                .collect()
        };
        let mut imports = Vec::new();
        let mut dependencies = Vec::new();
        for binding in factory.bindings.iter().filter(|b| b.view.is_none()) {
            if !resolved
                .iter()
                .any(|r| r.name == binding.name && r.port == ports[&binding.name])
            {
                return Err("TypedImportUnavailable".into());
            }
        }
        for resolved in &resolved {
            let binding = factory
                .mapped()
                .into_iter()
                .find(|b| b.name == resolved.name)
                .ok_or("UnknownTypedImport")?;
            let realm = *self
                .typed_realms
                .get(&(binding.key, resolved.port.realm))
                .ok_or("UnknownTypedRealm")?;
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
                    realm,
                },
                provider: resolved.owner,
                slot: typed.slot(binding.key, binding.type_id, resolved.port.realm)?,
            });
            dependencies.push((binding, resolved.port, realm));
        }
        if let Some(mount) = self.typed_mounts.get(&id) {
            if mount.factory != factory.name || mount.config != config || mount.ports != ports {
                return Err("TypedMountDefinitionChanged".into());
            }
        } else {
            let expected_config = factory
                .bindings
                .iter()
                .filter_map(|binding| {
                    binding
                        .injection_config
                        .as_ref()
                        .map(|value| (binding.key, value.clone()))
                })
                .collect::<BTreeMap<_, _>>();
            let plugin = (factory.make)(config.clone())?;
            let definition = if expected_config.is_empty() {
                StaticPlugin::new(plugin)?
            } else {
                StaticPlugin::new_with_injection_config(plugin, expected_config)?
            };
            let declarations = definition.declarations();
            let expected = |owned: bool| {
                factory
                    .bindings
                    .iter()
                    .filter(|b| {
                        b.view.is_some() == owned
                            && !factory.anchor.as_ref().is_some_and(|a| a.key == b.key)
                    })
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
                    adapter: factory.clone(),
                    context: TypedContext::with_realms(realms.clone()),
                    realms: realms.clone(),
                },
            );
        }
        let context = self.typed_mounts[&id].context.clone();
        let dirty = Arc::new(AtomicBool::new(false));
        let definition = &mut self.typed_mounts.get_mut(&id).unwrap().definition;
        let StaticStart { episode, setup } = if factory.service_updates {
            let dirty = dirty.clone();
            let notify = self.notify.clone();
            let notifications = self.service_notifications.clone();
            let children = self.child_notifications.clone();
            let dynamic = factory.dynamic_children;
            let callback: Arc<dyn Fn() + Send + Sync> = Arc::new(move || {
                dirty.store(true, Ordering::Release);
                notifications.store(true, Ordering::Release);
                if dynamic {
                    children.store(true, Ordering::Release);
                }
                notify();
            });
            if let Some(anchor) = &factory.anchor {
                definition.begin_with_dynamic_host(
                    id,
                    generation,
                    context,
                    imports,
                    Port {
                        key: anchor.key,
                        realm: realms[&anchor.key],
                    },
                    callback,
                )?
            } else {
                definition.begin_with_service_updates(id, generation, context, imports, callback)?
            }
        } else {
            definition.begin(id, generation, context, imports)?
        };
        Ok(Arc::new(Instance {
            episode,
            start: Mutex::new(Some(setup)),
            factory,
            ports,
            service_dirty: dirty,
            realms,
            anchor_slot: TypedSlot::from_arc(Arc::new(())),
            dependencies,
        }))
    }
    pub fn typed_check(
        &mut self,
        session: u64,
        service: &str,
        realms: &BTreeMap<String, cordis_driver::ServicePort>,
        config: &Value,
    ) -> PluginResult<bool> {
        let session = self.sessions.get(&session).ok_or("UnknownSession")?;
        session.cancellation.check()?;
        let instance = session.typed.clone().ok_or("TypedProviderRequired")?;
        instance.factory.check_ports(realms)?;
        let typed_realms = instance
            .factory
            .mapped()
            .iter()
            .map(|binding| {
                let realm = *self
                    .typed_realms
                    .entry((binding.key, realms[&binding.name].realm))
                    .or_insert_with(|| {
                        let key = ServiceKey::<()>::new("external-check-realm");
                        TypedContext::new().isolate(key).port(key).realm
                    });
                (binding.key, realm)
            })
            .collect();
        instance.check_service(service, realms, config, typed_realms)
    }
    pub(super) fn typed_notifications(&self) -> Vec<Value> {
        // Ordinary calls and idle polls do not scan the retained session graph.
        if !self.service_notifications.swap(false, Ordering::AcqRel) {
            return Vec::new();
        }
        self.sessions.iter().filter_map(|(id, session)| {
            let typed = session.typed.as_ref()?;
            if !typed.take_service_notification() || session.cancellation.is_cancelled() || typed.episode.is_closed() { return None; }
            let mut ids = BTreeSet::from([*id]);
            loop {
                let old = ids.len();
                for child in self.typed_children.values().filter(|c| ids.contains(&c.parent)).collect::<Vec<_>>() {
                    if let Some(owner) = child.control.id() {
                        for (id,s) in &self.sessions { if s.id==owner { ids.insert(*id); } }
                    }
                }
                if old==ids.len() {break;}
            }
            let ports = ids.iter().flat_map(|id| self.sessions[id].publications.values().map(|(_,port)| *port)).collect::<Vec<_>>();
            Some(serde_json::json!({"session":id.to_string(), "generation":session.generation.to_string(), "ports":ports }))
        }).collect()
    }
    pub fn forget_typed(&mut self, id: usize) -> PluginResult<()> {
        if self.sessions.values().any(|s| s.id == id) {
            return Err("SessionBusy".into());
        }
        if let Some(mount) = self.typed_mounts.remove(&id) {
            if let Some(anchor) = &mount.adapter.anchor {
                self.typed_realms.retain(|(key, _), _| *key != anchor.key);
            }
        }
        let key = self
            .typed_children
            .iter()
            .find(|(_, child)| child.control.id() == Some(id))
            .map(|(key, _)| key.clone());
        if let Some(key) = key {
            let child = self.typed_children.remove(&key).unwrap();
            child.control.removed()?;
        }
        Ok(())
    }
}
