//! Episode-owned children and retained factory definitions. Only the resident
//! graph may acknowledge allocation and actual removal; action completion does
//! not release these longer-lived capabilities.
use super::*;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ChildTarget {
    Module { factory: String },
    Retained { definition: u64 },
}
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ChildStatus {
    pub id: Option<String>,
    pub initialized: bool,
    pub retiring: bool,
    pub removed: bool,
    pub cleanup_failed: bool,
    pub error: Option<String>,
}
pub(super) struct Definition {
    owner: u64,
    value: Mutex<Option<Arc<dyn PluginFactory>>>,
    descriptor: Mutex<Option<FactoryDescriptor>>,
    instances: Mutex<BTreeSet<u64>>,
    child: Mutex<Option<u64>>,
    faulted: AtomicBool,
}
pub(super) struct ChildScope {
    instance: u64,
    records: Weak<Mutex<Records>>,
    factories: BTreeSet<String>,
}
pub(super) fn is_drained(state: &InstanceState) -> bool {
    state.child_instances.is_empty()
        && state.definitions.is_empty()
        && state.controls.values().all(|child| child.removed)
}
impl ChildScope {
    fn records(&self) -> PluginResult<Arc<Mutex<Records>>> {
        self.records.upgrade().ok_or_else(|| "ActionClosed".into())
    }
    fn owner(&self) -> PluginResult<Arc<InstanceEntry>> {
        self.records()?
            .lock()
            .unwrap()
            .instances
            .get(&self.instance)
            .cloned()
            .ok_or_else(|| "ActionClosed".into())
    }
    fn admission(&self, definition: bool) -> PluginResult<()> {
        let owner = self.owner()?;
        let mut state = owner.state.lock().unwrap();
        if !matches!(state.phase, Phase::Setup | Phase::Active) {
            return Err("InstanceNotActive".into());
        }
        if state.child_attempts >= MAX_CHILDREN
            || (definition && state.definition_attempts >= MAX_CHILDREN)
        {
            return Err("ChildCapacity".into());
        }
        state.child_attempts += 1;
        if definition {
            state.definition_attempts += 1;
        }
        Ok(())
    }
    fn retain(&self, value: Arc<dyn PluginFactory>) -> PluginResult<(u64, Arc<Definition>)> {
        let owner = self.owner()?;
        let records = self.records()?;
        let mut records = records.lock().unwrap();
        let id = records.next;
        records.next = id.checked_add(1).ok_or("HandleSpaceExhausted")?;
        let definition = Arc::new(Definition {
            owner: self.instance,
            value: Mutex::new(Some(value)),
            descriptor: Mutex::new(None),
            instances: Mutex::new(BTreeSet::new()),
            child: Mutex::new(None),
            faulted: AtomicBool::new(false),
        });
        records.definitions.insert(id, definition.clone());
        drop(records);
        owner.state.lock().unwrap().definitions.insert(id);
        Ok((id, definition))
    }
    fn reject_definition(&self, id: u64) -> PluginResult<()> {
        drop_definition(&self.records()?, self.instance, id, false).map(|_| ())
    }
    pub(super) fn allocated(&self, child: u64, definition: Option<u64>) -> PluginResult<()> {
        if child == 0 {
            return Err("InvalidChildHandle".into());
        }
        let owner = self.owner()?;
        {
            let mut state = owner.state.lock().unwrap();
            if !state.controls.contains_key(&child) && state.controls.len() >= MAX_CHILDREN {
                return Err("ChildCapacity".into());
            }
            if !state.control_acks.insert(child) {
                return Err("DuplicateChildHandle".into());
            }
            // A Removed acknowledgement may precede the original mount reply.
            state.controls.entry(child).or_default();
        }
        if let Some(id) = definition {
            if let Some(definition) = self.records()?.lock().unwrap().definitions.get(&id) {
                if definition.owner != self.instance {
                    return Err("WrongDefinitionOwner".into());
                }
                let mut assigned = definition.child.lock().unwrap();
                if assigned.is_some_and(|previous| previous != child) {
                    return Err("DefinitionAlreadyMounted".into());
                }
                *assigned = Some(child);
            } else if !owner.state.lock().unwrap().controls[&child].removed {
                return Err("UnknownDefinition".into());
            }
        }
        Ok(())
    }
    pub(super) fn completed(
        &self,
        operation: &ReverseOperation,
        result: &mut PluginResult<reverse::CallValue>,
    ) -> PluginResult<()> {
        if let (
            ReverseOperation::ChildStatus { child },
            Ok(reverse::CallValue::ChildState(status)),
        ) = (operation, &mut *result)
        {
            *status = self.observe(*child, status.clone())?;
            return Ok(());
        }
        if result.is_ok() {
            let (child, ready, retiring, removed) = match operation {
                ReverseOperation::ChildReady { child } => (*child, true, false, false),
                ReverseOperation::ChildRetire { child } => (*child, false, true, false),
                ReverseOperation::ChildJoin { child }
                | ReverseOperation::ChildRetryCleanup { child } => (*child, false, true, true),
                _ => return Ok(()),
            };
            let owner = self.owner()?;
            let mut state = owner.state.lock().unwrap();
            let status = state.controls.get_mut(&child).ok_or("UnknownChild")?;
            if !status.removed {
                status.initialized |= ready;
                status.retiring |= retiring;
                status.removed |= removed;
                if removed {
                    status.initialized = false;
                    status.cleanup_failed = false;
                    status.error = None;
                }
            }
        }
        Ok(())
    }
    pub(super) fn observe(&self, child: u64, status: ChildStatus) -> PluginResult<ChildStatus> {
        let owner = self.owner()?;
        let mut state = owner.state.lock().unwrap();
        let previous = state.controls.get_mut(&child).ok_or("UnknownChild")?;
        if previous.removed && !status.removed {
            // A host status snapshot can precede its actual Removed event but
            // arrive after that event's SDK acknowledgement. Keep the newer
            // tombstone, while preserving useful node identity from the reply.
            if previous.id.is_none() {
                previous.id = status.id;
            }
            return Ok(previous.clone());
        }
        *previous = status;
        Ok(previous.clone())
    }
}
/// A capability belonging to an instance episode, usable by later actions of
/// that same instance. Dropping it does not retire the actual child node.
#[derive(Clone)]
pub struct ChildHandle {
    owner: Arc<ChildScope>,
    child: u64,
}
impl ChildHandle {
    fn context<'a>(&self, ctx: &'a PluginContext) -> PluginResult<&'a Arc<CallAction>> {
        if !ctx
            .children
            .as_ref()
            .is_some_and(|owner| Arc::ptr_eq(owner, &self.owner))
        {
            return Err("WrongChildOwner".into());
        }
        self.owner.owner()?;
        ctx.calls.as_ref().ok_or_else(|| "ActionClosed".into())
    }
    pub async fn status(&self, ctx: &PluginContext) -> PluginResult<ChildStatus> {
        match self
            .context(ctx)?
            .enqueue_child(ReverseOperation::ChildStatus { child: self.child })?
            .await?
        {
            reverse::CallValue::ChildState(status) => Ok(status),
            _ => Err("InvalidReverseReply".into()),
        }
    }
    pub async fn initialized(&self, ctx: &PluginContext) -> PluginResult<()> {
        self.control(ctx, ReverseOperation::ChildReady { child: self.child })
            .await
    }
    /// Request retirement. Use join to wait for actual graph removal.
    pub async fn dispose(&self, ctx: &PluginContext) -> PluginResult<()> {
        self.control(ctx, ReverseOperation::ChildRetire { child: self.child })
            .await
    }
    pub async fn join(&self, ctx: &PluginContext) -> PluginResult<()> {
        self.control(ctx, ReverseOperation::ChildJoin { child: self.child })
            .await
    }
    pub async fn retry_cleanup(&self, ctx: &PluginContext) -> PluginResult<()> {
        self.control(
            ctx,
            ReverseOperation::ChildRetryCleanup { child: self.child },
        )
        .await
    }
    async fn control(&self, ctx: &PluginContext, operation: ReverseOperation) -> PluginResult<()> {
        self.context(ctx)?.enqueue_child(operation)?.await?.json()?;
        Ok(())
    }
}
impl PluginContext {
    fn child_admission(&self) -> PluginResult<(&Arc<ChildScope>, &Arc<CallAction>)> {
        if self.cleanup {
            return Err("CleanupCannotMount".into());
        }
        self.cancellation.check()?;
        let calls = self.calls.as_ref().ok_or("ActionClosed")?;
        calls.check_open()?;
        Ok((self.children.as_ref().ok_or("ActionClosed")?, calls))
    }
    /// Mount a named factory from this original library image. Completion
    /// acknowledges allocation; initialized() separately waits for readiness.
    pub async fn mount(&self, factory: &str, config: Value) -> PluginResult<ChildHandle> {
        let config = bounded_result(Ok(config))?;
        let (owner, calls) = self.child_admission()?;
        if !owner.factories.contains(factory) {
            return Err("UnknownFactory".into());
        }
        owner.admission(false)?;
        match calls
            .enqueue_child(ReverseOperation::ChildMount {
                factory: factory.into(),
                config,
            })?
            .await?
        {
            reverse::CallValue::Child(child) => Ok(ChildHandle {
                owner: owner.clone(),
                child,
            }),
            _ => Err("InvalidReverseReply".into()),
        }
    }
    /// Retain a factory inside this library and publish it through a dedicated
    /// provider child. Each graph activation calls create() for a fresh instance.
    pub async fn publish(
        &self,
        factory: impl PluginFactory,
        config: Value,
    ) -> PluginResult<ChildHandle> {
        let config = bounded_result(Ok(config))?;
        let (owner, calls) = self.child_admission()?;
        owner.admission(true)?;
        let (id, definition) = owner.retain(Arc::new(factory))?;
        let factory = definition.value.lock().unwrap().as_ref().unwrap().clone();
        let descriptor = catch_user(|| factory.descriptor());
        drop(factory);
        let descriptor = match descriptor {
            Ok(descriptor) => validate_descriptor(descriptor),
            Err(error) => {
                definition.faulted.store(true, Ordering::Release);
                owner.owner()?.state.lock().unwrap().phase = Phase::Faulted;
                return Err(error);
            }
        };
        let descriptor = match descriptor {
            Ok(descriptor) => descriptor,
            Err(error) => {
                owner.reject_definition(id)?;
                return Err(error);
            }
        };
        *definition.descriptor.lock().unwrap() = Some(descriptor);
        let reply = match calls.enqueue_child(ReverseOperation::ChildPublish {
            definition: id,
            config,
        }) {
            Ok(reply) => reply,
            Err(error) => {
                owner.reject_definition(id)?;
                return Err(error);
            }
        };
        match reply.await? {
            reverse::CallValue::Child(child) => Ok(ChildHandle {
                owner: owner.clone(),
                child,
            }),
            _ => Err("InvalidReverseReply".into()),
        }
    }
}
fn validate_descriptor(descriptor: FactoryDescriptor) -> PluginResult<FactoryDescriptor> {
    if descriptor.name.is_empty() {
        return Err("EmptyFactoryName".into());
    }
    let mut inject = BTreeSet::new();
    if descriptor
        .inject
        .iter()
        .any(|name| name.is_empty() || !inject.insert(name))
    {
        return Err("DuplicateOrEmptyInjection".into());
    }
    let mut services = BTreeSet::new();
    for service in &descriptor.services {
        if service.name.is_empty() || !services.insert(&service.name) {
            return Err("DuplicateOrEmptyService".into());
        }
        let mut methods = BTreeSet::new();
        if service
            .methods
            .iter()
            .any(|method| method.name.is_empty() || !methods.insert(&method.name))
        {
            return Err("DuplicateOrEmptyMethod".into());
        }
    }
    if serde_json::to_vec(&descriptor).map_or(true, |bytes| bytes.len() > MAX_MESSAGE_BYTES / 2) {
        return Err("DescriptorTooLarge".into());
    }
    Ok(descriptor)
}
fn drop_definition(
    records: &Arc<Mutex<Records>>,
    parent: u64,
    id: u64,
    external: bool,
) -> PluginResult<Value> {
    let (definition, owner) = {
        let records = records.lock().unwrap();
        (
            records
                .definitions
                .get(&id)
                .cloned()
                .ok_or("UnknownDefinition")?,
            records
                .instances
                .get(&parent)
                .cloned()
                .ok_or("UnknownInstance")?,
        )
    };
    if definition.owner != parent {
        return Err("WrongDefinitionOwner".into());
    }
    let _gate = if external {
        Some(owner.gate.try_lock().map_err(|_| "InstanceBusy")?)
    } else {
        None
    };
    if !external && definition.child.lock().unwrap().is_some() {
        return Err("DefinitionHasChild".into());
    }
    if definition.faulted.load(Ordering::Acquire) {
        return Err("DefinitionFaulted".into());
    }
    if !definition.instances.lock().unwrap().is_empty() {
        return Err("DefinitionHasInstances".into());
    }
    if let Some(child) = *definition.child.lock().unwrap() {
        if !owner
            .state
            .lock()
            .unwrap()
            .controls
            .get(&child)
            .is_some_and(|status| status.removed)
        {
            return Err("DefinitionHasChild".into());
        }
    }
    let value = definition
        .value
        .lock()
        .unwrap()
        .take()
        .ok_or("DefinitionAlreadyReleased")?;
    if let Err(error) = catch_user(|| drop(value)) {
        definition.faulted.store(true, Ordering::Release);
        owner.state.lock().unwrap().phase = Phase::Faulted;
        return Err(error);
    }
    records.lock().unwrap().definitions.remove(&id);
    owner.state.lock().unwrap().definitions.remove(&id);
    Ok(Value::Null)
}
impl Runtime {
    pub(super) fn create_instance(
        &self,
        factory: Arc<dyn PluginFactory>,
        descriptor: FactoryDescriptor,
        config: Value,
        parent: Option<u64>,
        definition: Option<u64>,
    ) -> PluginResult<Value> {
        let id = self.allocate()?;
        let value = catch_user(|| factory.create(config))??;
        let entry = Arc::new(InstanceEntry {
            value: Mutex::new(Some(value)),
            descriptor,
            state: Mutex::new(InstanceState {
                phase: Phase::Created,
                jobs: BTreeSet::new(),
                resources: BTreeSet::new(),
                child_instances: BTreeSet::new(),
                controls: BTreeMap::new(),
                control_acks: BTreeSet::new(),
                definitions: BTreeSet::new(),
                child_attempts: 0,
                definition_attempts: 0,
                checkpoint: None,
                restore_attempted: false,
            }),
            gate: Mutex::new(()),
            children: Arc::new(ChildScope {
                instance: id,
                records: Arc::downgrade(&self.records),
                factories: self.factories.keys().cloned().collect(),
            }),
            parent,
            definition,
        });
        self.records.lock().unwrap().instances.insert(id, entry);
        if let Some(parent) = parent {
            self.instance(parent)?
                .state
                .lock()
                .unwrap()
                .child_instances
                .insert(id);
        }
        if let Some(definition) = definition {
            self.records.lock().unwrap().definitions[&definition]
                .instances
                .lock()
                .unwrap()
                .insert(id);
        }
        Ok(json!({"instance":id}))
    }
    pub(super) fn describe_definition(&self, parent: u64, id: u64) -> PluginResult<Value> {
        let definition = self
            .records
            .lock()
            .unwrap()
            .definitions
            .get(&id)
            .cloned()
            .ok_or("UnknownDefinition")?;
        if definition.owner != parent {
            return Err("WrongDefinitionOwner".into());
        }
        let descriptor = definition
            .descriptor
            .lock()
            .unwrap()
            .clone()
            .ok_or("DefinitionNotReady")?;
        serde_json::to_value(descriptor).map_err(|_| "InvalidDescriptor".into())
    }
    pub(super) fn create_child(
        &self,
        parent: u64,
        target: ChildTarget,
        config: Value,
    ) -> PluginResult<Value> {
        let owner = self.instance(parent)?;
        let _gate = owner.gate.try_lock().map_err(|_| "InstanceBusy")?;
        {
            let state = owner.state.lock().unwrap();
            if !matches!(state.phase, Phase::Setup | Phase::Active) {
                return Err("InstanceNotActive".into());
            }
            if state.child_instances.len() >= MAX_CHILDREN {
                return Err("ChildCapacity".into());
            }
        }
        let (factory, descriptor, definition) = match target {
            ChildTarget::Module { factory } => {
                let value = self
                    .factories
                    .get(&factory)
                    .cloned()
                    .ok_or("UnknownFactory")?;
                let descriptor = self
                    .descriptor
                    .factories
                    .iter()
                    .find(|entry| entry.name == factory)
                    .unwrap()
                    .clone();
                (value, descriptor, None)
            }
            ChildTarget::Retained { definition } => {
                let value = self
                    .records
                    .lock()
                    .unwrap()
                    .definitions
                    .get(&definition)
                    .cloned()
                    .ok_or("UnknownDefinition")?;
                if value.owner != parent {
                    return Err("WrongDefinitionOwner".into());
                }
                let descriptor = value
                    .descriptor
                    .lock()
                    .unwrap()
                    .clone()
                    .ok_or("DefinitionNotReady")?;
                let factory = value
                    .value
                    .lock()
                    .unwrap()
                    .as_ref()
                    .cloned()
                    .ok_or("DefinitionAlreadyReleased")?;
                (factory, descriptor, Some(definition))
            }
        };
        self.create_instance(
            factory,
            descriptor,
            bounded_result(Ok(config))?,
            Some(parent),
            definition,
        )
    }
    pub(super) fn drop_definition(&self, parent: u64, definition: u64) -> PluginResult<Value> {
        drop_definition(&self.records, parent, definition, true)
    }
    pub(super) fn child_removed(&self, parent: u64, child: u64) -> PluginResult<Value> {
        if child == 0 {
            return Err("InvalidChildHandle".into());
        }
        let owner = self.instance(parent)?;
        let mut state = owner.state.lock().unwrap();
        if !state.controls.contains_key(&child) && state.controls.len() >= MAX_CHILDREN {
            return Err("ChildCapacity".into());
        }
        let status = state.controls.entry(child).or_default();
        status.removed = true;
        status.retiring = true;
        status.initialized = false;
        status.cleanup_failed = false;
        status.error = None;
        Ok(Value::Null)
    }
    pub(super) fn child_instance_destroyed(&self, entry: &InstanceEntry, id: u64) {
        if let Some(parent) = entry.parent {
            if let Ok(owner) = self.instance(parent) {
                owner.state.lock().unwrap().child_instances.remove(&id);
            }
        }
        if let Some(definition) = entry.definition {
            if let Some(definition) = self.records.lock().unwrap().definitions.get(&definition) {
                definition.instances.lock().unwrap().remove(&id);
            }
        }
    }
}

#[cfg(test)]
#[path = "children_tests.rs"]
mod tests;
