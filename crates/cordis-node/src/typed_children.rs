//! Typed child definitions are retained here; only the native Driver schedules them.
use super::*;

pub(crate) type JobWaitSource = (u64, Option<(usize, u64)>, Vec<usize>);

struct AnchorView;
impl TypedService<()> for AnchorView {
    fn methods(&self) -> Vec<MethodDescriptor> {
        Vec::new()
    }
}
impl TypedFactory {
    pub(in super::super) fn with_native_anchor(
        &self,
        ports: &BTreeMap<String, cordis_driver::ServicePort>,
    ) -> PluginResult<Self> {
        let mapped = self.mapped();
        let extra = ports
            .keys()
            .filter(|name| !mapped.iter().any(|b| &b.name == *name))
            .collect::<Vec<_>>();
        if extra.len() != 1 || !extra[0].starts_with("__cordis_typed_anchor_") {
            return Err("TypedAnchorRequired".into());
        }
        let key = ServiceKey::<()>::new("external-owner-anchor");
        let binding = Binding {
            key: TypedContext::new().port(key).key,
            type_id: TypeId::of::<()>(),
            name: extra[0].clone(),
            view: Some(Arc::new(View {
                adapter: AnchorView,
                marker: std::marker::PhantomData,
            })),
            injection_config: None,
        };
        let mut factory = self.clone();
        factory.bindings.push(binding.clone());
        factory.anchor = Some(binding);
        factory.check_ports(ports)?;
        Ok(factory)
    }
}
impl Instance {
    pub(in super::super) fn realm_metadata(&self) -> Value {
        serde_json::json!(self.factory.mapped().iter().map(|b| serde_json::json!({"name":b.name,"key":b.key.to_string(),"realm":self.realms[&b.key].to_string()})).collect::<Vec<_>>())
    }
}
pub(in super::super) struct Child {
    pub(super) parent: u64,
    pub(super) control: StaticChildControl,
    factory: Arc<TypedFactory>,
    definition: Option<StaticPlugin>,
    context: TypedContext,
    realms: BTreeMap<u64, u64>,
    inherited: Vec<(String, cordis_driver::ServicePort)>,
    retirement_sent: bool,
}
impl Backend {
    pub fn take_typed_failures(&mut self) -> Vec<(u64, String)> {
        std::mem::take(&mut self.typed_failures)
    }
    pub fn typed_bind_job_caller(
        &mut self,
        job: u64,
        caller: Option<(usize, u64)>,
    ) -> PluginResult<()> {
        self.jobs.get_mut(&job).ok_or("UnknownJob")?.wait_source = caller;
        Ok(())
    }
    pub fn typed_job_wait_sources(&self) -> Vec<JobWaitSource> {
        if self.typed_children.is_empty() && self.native_children.is_empty() {
            return Vec::new();
        }
        self.jobs
            .iter()
            .map(|(id, job)| {
                let mut own_publications = if job.kind == JobKind::Setup {
                    self.typed_children
                        .values()
                        .filter(|child| {
                            child.parent == job.session && child.control.is_publication()
                        })
                        .filter_map(|child| child.control.id())
                        .collect()
                } else {
                    Vec::new()
                };
                if job.kind == JobKind::Setup {
                    own_publications.extend(self.native_children.owned_ids(job.session));
                }
                let source = job
                    .wait_source
                    .or_else(|| {
                        job.stream.and_then(|action| {
                            let (StreamAction::Next(id) | StreamAction::Close(id)) = action;
                            self.streams.get(&id).and_then(|s| s.caller)
                        })
                    })
                    .or_else(|| {
                        job.object.and_then(|action| {
                            let (ObjectAction::Call(id) | ObjectAction::Close(id)) = action;
                            self.objects.get(&id).and_then(|s| s.caller)
                        })
                    });
                (*id, source, own_publications)
            })
            .collect()
    }
    pub fn typed_job_join_blocks(&mut self, job: u64, blocked: BTreeSet<usize>) {
        if let Some(job) = self.jobs.get_mut(&job) {
            *job.context.join_blocked.lock().unwrap() = blocked.clone();
            job.join_blocked = blocked;
        }
    }
    pub(in super::super) fn typed_child_actions(&mut self) -> Vec<Value> {
        if !self.child_notifications.swap(false, Ordering::AcqRel) {
            return Vec::new();
        }
        let mut actions = Vec::new();
        let sessions = self
            .sessions
            .iter()
            .filter_map(|(id, s)| {
                s.typed
                    .clone()
                    .filter(|t| t.factory.dynamic_children)
                    .map(|t| (*id, t))
            })
            .collect::<Vec<_>>();
        for (session, instance) in sessions {
            let requests = match instance.episode.drain_child_requests() {
                Ok(requests) => requests,
                Err(error) => {
                    self.typed_failures.push((session, error.clone()));
                    actions.push(serde_json::json!({"kind":"error","session":session.to_string(),"error":error}));
                    continue;
                }
            };
            for mut request in requests {
                let control = request.control.clone();
                let prepared = (|| -> PluginResult<_> {
                    if control.owner() != instance.episode.owner()
                        || control.generation() != instance.episode.generation()
                    {
                        return Err("TypedChildOwnerMismatch".into());
                    }
                    let parent_ports = instance
                        .dependencies
                        .iter()
                        .map(|(b, _, realm)| Port {
                            key: b.key,
                            realm: *realm,
                        })
                        .collect();
                    let parent_config = self.typed_mounts[&control.owner()]
                        .definition
                        .declarations()
                        .injection_config
                        .clone();
                    request.plugin.inherit_dependencies(
                        &request.context,
                        parent_ports,
                        parent_config,
                    )?;
                    let declaration = request.plugin.declarations();
                    let catalog = instance.factory.mapped();
                    let mut bindings = Vec::new();
                    let mut keys = declaration.dependencies.clone();
                    keys.extend(
                        request
                            .plugin
                            .inherited_dependencies()
                            .iter()
                            .filter(|p| !declaration.provisions.contains(&p.key))
                            .map(|p| p.key),
                    );
                    keys.sort_unstable();
                    keys.dedup();
                    for (owned, keys) in [(false, keys), (true, declaration.provisions.clone())] {
                        for key in keys {
                            let mut binding = catalog
                                .iter()
                                .find(|b| b.key == key)
                                .ok_or("UnknownTypedChildService")?
                                .clone();
                            if owned && binding.view.is_none() {
                                return Err("TypedChildViewRequired".into());
                            }
                            if !owned {
                                binding.view = None;
                            }
                            binding.injection_config = (!owned)
                                .then(|| declaration.injection_config.get(&key).cloned())
                                .flatten();
                            bindings.push(binding);
                        }
                    }
                    let next = self
                        .next_typed_child
                        .checked_add(1)
                        .ok_or("TypedChildCapacity")?;
                    let name = format!("@cordis-child:{next}");
                    let factory = Arc::new(TypedFactory {
                        name: name.clone(),
                        make: Arc::new(|_| Err("TypedChildDefinitionRequired".into())),
                        bindings,
                        service_updates: true,
                        dynamic_children: true,
                        catalog,
                        anchor: None,
                    });
                    let mut metadata = factory.metadata()?;
                    metadata["name"] = Value::String(name.clone());
                    metadata["displayName"] = Value::String(declaration.name.clone());
                    let realms = factory
                        .mapped()
                        .iter()
                        .map(|b| (b.key, request.port(b.key).realm))
                        .collect::<BTreeMap<_, _>>();
                    metadata["realms"] = serde_json::json!(factory.mapped().iter().map(|b| serde_json::json!({"name":b.name,"key":b.key.to_string(),"realm":realms[&b.key].to_string()})).collect::<Vec<_>>());
                    let inherited = instance
                        .dependencies
                        .iter()
                        .filter(|(b, _, realm)| {
                            !declaration.provisions.contains(&b.key)
                                || request.port(b.key).realm != *realm
                        })
                        .map(|(b, port, _)| (b.name.clone(), *port))
                        .collect::<Vec<_>>();
                    metadata["inherited"] =
                        serde_json::json!(inherited.iter().map(|(_, p)| p).collect::<Vec<_>>());
                    self.next_typed_child = next;
                    self.typed_children.insert(
                        name.clone(),
                        Child {
                            parent: session,
                            control: control.clone(),
                            factory,
                            definition: Some(request.plugin),
                            context: request.context,
                            realms,
                            inherited,
                            retirement_sent: false,
                        },
                    );
                    Ok((name, metadata))
                })();
                match prepared {
                    Ok((name, factory)) => actions.push(serde_json::json!({"kind":"mount","session":session.to_string(),"child":name,"factory":factory})),
                    Err(error) => { if !control.is_publication() { self.typed_failures.push((session,error.clone())); actions.push(serde_json::json!({"kind":"error","session":session.to_string(),"error":error})); } let _ = control.complete_mount(Err(error)); }
                }
            }
        }
        for (name, child) in &mut self.typed_children {
            if child.control.retirement_requested()
                && child.control.id().is_some()
                && !child.retirement_sent
            {
                child.retirement_sent = true;
                actions.push(serde_json::json!({"kind":"retire","session":child.parent.to_string(),"child":name,"id":child.control.id().unwrap().to_string()}));
            }
        }
        actions
    }
    pub fn typed_child_owner(&self, child: &str) -> PluginResult<(usize, u64, Option<usize>)> {
        let child = self.typed_children.get(child).ok_or("UnknownTypedChild")?;
        Ok((
            child.control.owner(),
            child.control.generation(),
            child.control.id(),
        ))
    }
    pub fn typed_child_mounted(
        &mut self,
        child: &str,
        id: usize,
        ports: BTreeMap<String, cordis_driver::ServicePort>,
    ) -> PluginResult<()> {
        let child = self
            .typed_children
            .get_mut(child)
            .ok_or("UnknownTypedChild")?;
        if child.control.id().is_some() {
            return Err("TypedChildAlreadyMounted".into());
        }
        child.control.complete_mount(Ok(id))?;
        let adapter = Arc::new(child.factory.with_native_anchor(&ports)?);
        let mut realms = child.realms.clone();
        let anchor = adapter.anchor.as_ref().unwrap();
        let fresh = ServiceKey::<()>::new("external-child-realm");
        realms.insert(
            anchor.key,
            TypedContext::new().isolate(fresh).port(fresh).realm,
        );
        for binding in adapter.mapped() {
            let mapped = (binding.key, ports[&binding.name].realm);
            if self
                .typed_realms
                .get(&mapped)
                .is_some_and(|realm| *realm != realms[&binding.key])
            {
                return Err("TypedRealmAlias".into());
            }
        }
        for binding in adapter.mapped() {
            self.typed_realms.insert(
                (binding.key, ports[&binding.name].realm),
                realms[&binding.key],
            );
        }
        child.context = TypedContext::with_realms(realms.clone());
        self.typed_mounts.insert(
            id,
            Mount {
                factory: adapter.name.clone(),
                config: Value::Null,
                ports,
                definition: child
                    .definition
                    .take()
                    .ok_or("TypedChildDefinitionMissing")?,
                adapter,
                context: child.context.clone(),
                realms,
            },
        );
        Ok(())
    }
    pub fn typed_child_aborted(&mut self, child: &str, error: String) -> PluginResult<()> {
        let child = self.typed_children.get(child).ok_or("UnknownTypedChild")?;
        if child.control.id().is_none() {
            return Err("TypedChildNotMounted".into());
        }
        child.control.record_error(error.clone());
        if !child.control.is_publication() {
            self.typed_failures.push((child.parent, error));
        }
        Ok(())
    }
    pub fn typed_child_rejected(&mut self, child: &str, error: String) -> PluginResult<()> {
        let pending = self.typed_children.get(child).ok_or("UnknownTypedChild")?;
        if pending.control.id().is_some() {
            return Err("TypedChildAlreadyMounted".into());
        }
        let pending = self.typed_children.remove(child).unwrap();
        if !pending.control.is_publication() {
            self.typed_failures.push((pending.parent, error.clone()));
        }
        pending.control.complete_mount(Err(error))
    }
    pub fn typed_import_ports(
        &self,
        factory: &str,
        ports: &BTreeMap<String, cordis_driver::ServicePort>,
    ) -> PluginResult<Vec<(String, cordis_driver::ServicePort)>> {
        let descriptor = self
            .typed_descriptor(factory, ports)?
            .ok_or("TypedProviderRequired")?;
        let mut required = descriptor
            .inject
            .iter()
            .map(|name| (name.clone(), ports[name]))
            .collect::<Vec<_>>();
        if let Some(child) = self.typed_children.get(factory) {
            for port in &child.inherited {
                if !required.contains(port) {
                    required.push(port.clone());
                }
            }
        }
        Ok(required)
    }
    pub fn typed_child_observed(
        &self,
        child: &str,
        active: bool,
        failed: Option<String>,
        cleanup_failed: bool,
    ) -> PluginResult<()> {
        let child = self.typed_children.get(child).ok_or("UnknownTypedChild")?;
        if active {
            child.control.mark_initialized()?;
        }
        if let Some(error) = failed {
            if cleanup_failed {
                child.control.cleanup_failed(error);
            } else {
                child.control.record_error(error);
            }
        }
        Ok(())
    }
}
