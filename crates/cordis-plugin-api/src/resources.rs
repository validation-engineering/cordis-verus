//! Resource handles remain in their originating library and instance. The
//! resident host owns caller/generation checks; this table independently owns
//! close, pending jobs and the creating allocator's final reference release.
use super::*;

pub type StreamFuture = Pin<Box<dyn Future<Output = PluginResult<Option<Value>>> + Send + 'static>>;
pub trait PluginStream: Send + Sync + 'static {
    fn next(&self, ctx: PluginContext) -> StreamFuture;
    /// Request cancellation only. Pending pulls must still actually complete.
    fn cancel(&self) {}
    fn close(&self, _ctx: PluginContext) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum ObjectOwnership {
    Borrowed,
    Owned,
}
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ObjectDescriptor {
    type_name: String,
    methods: Vec<String>,
    ownership: ObjectOwnership,
}
impl ObjectDescriptor {
    pub fn new(
        type_name: impl Into<String>,
        methods: impl IntoIterator<Item = impl Into<String>>,
        ownership: ObjectOwnership,
    ) -> PluginResult<Self> {
        let descriptor = Self {
            type_name: type_name.into(),
            methods: methods.into_iter().map(Into::into).collect(),
            ownership,
        };
        let mut names = BTreeSet::new();
        if descriptor.type_name.is_empty()
            || descriptor.methods.is_empty()
            || descriptor
                .methods
                .iter()
                .any(|method| method.is_empty() || !names.insert(method))
        {
            return Err("InvalidObjectDescriptor".into());
        }
        if serde_json::to_vec(&descriptor).map_or(true, |bytes| bytes.len() > MAX_MESSAGE_BYTES / 2)
        {
            return Err("ObjectDescriptorTooLarge".into());
        }
        Ok(descriptor)
    }
    pub(super) fn from_value(value: Value) -> PluginResult<Self> {
        #[derive(Deserialize)]
        #[serde(rename_all = "camelCase", deny_unknown_fields)]
        struct Raw {
            type_name: String,
            methods: Vec<String>,
            ownership: String,
        }
        let raw: Raw = serde_json::from_value(value).map_err(|_| "InvalidObjectDescriptor")?;
        let ownership = match raw.ownership.as_str() {
            "owned" => ObjectOwnership::Owned,
            "borrowed" => ObjectOwnership::Borrowed,
            _ => return Err("InvalidObjectDescriptor".into()),
        };
        Self::new(raw.type_name, raw.methods, ownership)
    }
    pub fn callback(
        type_name: impl Into<String>,
        ownership: ObjectOwnership,
    ) -> PluginResult<Self> {
        Self::new(type_name, ["call"], ownership)
    }
    pub fn type_name(&self) -> &str {
        &self.type_name
    }
    pub fn methods(&self) -> &[String] {
        &self.methods
    }
    pub fn ownership(&self) -> ObjectOwnership {
        self.ownership
    }
}
pub trait PluginObject: Send + Sync + 'static {
    fn descriptor(&self) -> ObjectDescriptor;
    fn call(&self, ctx: PluginContext, method: &str, args: Value) -> PluginFuture;
    fn close(&self, _ctx: PluginContext) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ResourceAction {
    StreamNext(u64),
    StreamClose(u64),
    ObjectCall(u64),
    ObjectClose(u64),
}
impl ResourceAction {
    pub(super) fn id(self) -> u64 {
        match self {
            Self::StreamNext(id)
            | Self::StreamClose(id)
            | Self::ObjectCall(id)
            | Self::ObjectClose(id) => id,
        }
    }
    pub(super) fn is_close(self) -> bool {
        matches!(self, Self::StreamClose(_) | Self::ObjectClose(_))
    }
    fn is_object(self) -> bool {
        matches!(self, Self::ObjectCall(_) | Self::ObjectClose(_))
    }
}
#[derive(Clone)]
enum Implementation {
    Stream(Arc<dyn PluginStream>),
    Object(Arc<dyn PluginObject>),
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Status {
    Open,
    Closing,
    Closed,
    Faulted,
    Removed,
}
struct ResourceState {
    status: Status,
    ended: bool,
    cancelled: bool,
    jobs: BTreeSet<u64>,
    descriptor: Option<ObjectDescriptor>,
}
pub(super) struct ResourceEntry {
    instance: u64,
    owner: Arc<InstanceEntry>,
    object: bool,
    identity: Option<Weak<dyn PluginObject>>,
    implementation: Mutex<Option<Implementation>>,
    state: Mutex<ResourceState>,
    gate: Mutex<()>,
}
impl Runtime {
    fn resource(&self, instance: u64, id: u64, object: bool) -> PluginResult<Arc<ResourceEntry>> {
        let entry = self
            .records
            .lock()
            .unwrap()
            .resources
            .get(&id)
            .cloned()
            .ok_or("UnknownResource")?;
        if entry.instance != instance {
            return Err("WrongResourceOwner".into());
        }
        if entry.object != object {
            return Err("WrongResourceKind".into());
        }
        Ok(entry)
    }
    pub(super) fn open_resource(
        &self,
        instance: u64,
        service: &str,
        method: &str,
        args: Value,
        object: bool,
    ) -> PluginResult<Value> {
        let owner = self.instance(instance)?;
        let _gate = owner.gate.try_lock().map_err(|_| "InstanceBusy")?;
        {
            let state = owner.state.lock().unwrap();
            if state.phase != Phase::Active {
                return Err("InstanceNotActive".into());
            }
            if state.resources.len() >= 1024 {
                return Err("ResourceCapacity".into());
            }
        }
        check_method(
            &owner.descriptor,
            service,
            method,
            if object {
                MethodKind::Object
            } else {
                MethodKind::Stream
            },
        )?;
        let id = self.allocate()?;
        let instance_value = owner.value.lock().unwrap().as_ref().unwrap().clone();
        let created = catch_user(|| {
            if object {
                instance_value
                    .open_object(service, method, args)
                    .map(Implementation::Object)
            } else {
                instance_value
                    .open_stream(service, method, args)
                    .map(Implementation::Stream)
            }
        });
        let implementation = match created {
            Ok(value) => value?,
            Err(error) => {
                owner.state.lock().unwrap().phase = Phase::Faulted;
                return Err(error);
            }
        };
        let entry = Arc::new(ResourceEntry {
            instance,
            owner: owner.clone(),
            object,
            identity: match &implementation {
                Implementation::Object(value) => Some(Arc::downgrade(value)),
                Implementation::Stream(_) => None,
            },
            implementation: Mutex::new(Some(implementation.clone())),
            state: Mutex::new(ResourceState {
                status: Status::Open,
                ended: false,
                cancelled: false,
                jobs: BTreeSet::new(),
                descriptor: None,
            }),
            gate: Mutex::new(()),
        });
        owner.state.lock().unwrap().resources.insert(id);
        self.records
            .lock()
            .unwrap()
            .resources
            .insert(id, entry.clone());
        if let Implementation::Object(value) = implementation {
            // Register first: a descriptor panic after resource acquisition may
            // not erase that obligation or silently drop the acquired object.
            let descriptor = match catch_user(|| value.descriptor()) {
                Ok(descriptor) => descriptor,
                Err(error) => {
                    entry.state.lock().unwrap().status = Status::Faulted;
                    owner.state.lock().unwrap().phase = Phase::Faulted;
                    return Err(error);
                }
            };
            let conflict = {
                // The original Arc identity belongs to this library; host-side
                // wrapper addresses cannot detect aliases across instances.
                let identity = entry.identity.as_ref().unwrap();
                let mut records = self.records.lock().unwrap();
                records
                    .owned_objects
                    .retain(|value| value.strong_count() > 0);
                let conflict = records
                    .owned_objects
                    .iter()
                    .any(|value| value.ptr_eq(identity))
                    || (descriptor.ownership == ObjectOwnership::Owned
                        && records.resources.iter().any(|(other_id, other)| {
                            *other_id != id
                                && other
                                    .identity
                                    .as_ref()
                                    .is_some_and(|value| value.ptr_eq(identity))
                        }));
                if !conflict && descriptor.ownership == ObjectOwnership::Owned {
                    records.owned_objects.push(identity.clone());
                }
                conflict
            };
            if conflict {
                // This is an extra reference, not another close obligation.
                // Release outside the table lock, retaining even this record if
                // it becomes the final reference and its destructor panics.
                let implementation = entry.implementation.lock().unwrap().take();
                if let Err(error) = catch_user(|| drop((implementation, value))) {
                    entry.state.lock().unwrap().status = Status::Faulted;
                    owner.state.lock().unwrap().phase = Phase::Faulted;
                    return Err(error);
                }
                self.records.lock().unwrap().resources.remove(&id);
                owner.state.lock().unwrap().resources.remove(&id);
                return Err("ObjectOwnershipConflict".into());
            }
            entry.state.lock().unwrap().descriptor = Some(descriptor.clone());
            Ok(json!({"object":id,"descriptor":descriptor}))
        } else {
            Ok(json!({"stream":id}))
        }
    }
    pub(super) fn resource_job(
        &self,
        instance: u64,
        action: ResourceAction,
        call: Option<(String, Value)>,
    ) -> PluginResult<Value> {
        let resource = self.resource(instance, action.id(), action.is_object())?;
        let _gate = resource.gate.try_lock().map_err(|_| "ResourceBusy")?;
        let id = self.allocate()?;
        {
            let mut state = resource.state.lock().unwrap();
            if resource.owner.state.lock().unwrap().phase != Phase::Active {
                return Err("InstanceNotActive".into());
            }
            if action.is_close() {
                if !state.jobs.is_empty() {
                    return Err("ResourceBusy".into());
                }
                if !matches!(state.status, Status::Open | Status::Closing) {
                    return Err("ResourceNotOpen".into());
                }
                state.status = Status::Closing;
            } else {
                if state.status != Status::Open || state.ended {
                    return Err("ResourceNotOpen".into());
                }
                if !action.is_object() && !state.jobs.is_empty() {
                    return Err("StreamBusy".into());
                }
                if let Some((method, _)) = &call {
                    if !state
                        .descriptor
                        .as_ref()
                        .unwrap()
                        .methods
                        .iter()
                        .any(|name| name == method)
                    {
                        return Err("UndeclaredObjectMethod".into());
                    }
                }
            }
            state.jobs.insert(id);
        }
        resource.owner.state.lock().unwrap().jobs.insert(id);
        let implementation = resource
            .implementation
            .lock()
            .unwrap()
            .as_ref()
            .unwrap()
            .clone();
        let borrowed = resource
            .state
            .lock()
            .unwrap()
            .descriptor
            .as_ref()
            .is_some_and(|descriptor| descriptor.ownership == ObjectOwnership::Borrowed);
        self.start_reserved_job(
            resource.owner.clone(),
            JobKind::Resource(action),
            id,
            move |context| match (action, implementation) {
                (ResourceAction::StreamNext(_), Implementation::Stream(stream)) => {
                    let future = stream.next(context);
                    Box::pin(async move {
                        match future.await? {
                            Some(value) => bounded_result(Ok(value))
                                .map(|value| json!({"done":false,"value":value})),
                            None => Ok(json!({"done":true})),
                        }
                    })
                }
                (ResourceAction::StreamClose(_), Implementation::Stream(stream)) => {
                    stream.close(context)
                }
                (ResourceAction::ObjectCall(_), Implementation::Object(object)) => {
                    let (method, args) = call.unwrap();
                    object.call(context, &method, args)
                }
                (ResourceAction::ObjectClose(_), Implementation::Object(object)) => {
                    if borrowed {
                        Box::pin(async { Ok(Value::Null) })
                    } else {
                        object.close(context)
                    }
                }
                _ => unreachable!("resource kind was validated"),
            },
        )
    }
    pub(super) fn cancel_stream(&self, instance: u64, stream: u64) -> PluginResult<Value> {
        let resource = self.resource(instance, stream, false)?;
        let _gate = resource.gate.try_lock().map_err(|_| "ResourceBusy")?;
        let jobs = {
            let mut state = resource.state.lock().unwrap();
            if matches!(state.status, Status::Faulted | Status::Removed) {
                return Err("ResourceNotOpen".into());
            }
            if state.cancelled || state.status == Status::Closed {
                return Ok(Value::Null);
            }
            state.cancelled = true;
            state.status = Status::Closing;
            state.jobs.iter().copied().collect::<Vec<_>>()
        };
        for job in jobs {
            let job = self.job(job)?;
            if matches!(job.kind, JobKind::Resource(ResourceAction::StreamNext(_))) {
                job.cancellation.cancel();
            }
        }
        let implementation = resource
            .implementation
            .lock()
            .unwrap()
            .as_ref()
            .unwrap()
            .clone();
        if let Implementation::Stream(stream) = implementation {
            if let Err(error) = catch_user(|| stream.cancel()) {
                resource.state.lock().unwrap().status = Status::Faulted;
                resource.owner.state.lock().unwrap().phase = Phase::Faulted;
                return Err(error);
            }
        }
        Ok(Value::Null)
    }
    pub(super) fn destroy_resource(
        &self,
        instance: u64,
        id: u64,
        object: bool,
    ) -> PluginResult<Value> {
        let resource = self.resource(instance, id, object)?;
        let _gate = resource.gate.try_lock().map_err(|_| "ResourceBusy")?;
        {
            let mut state = resource.state.lock().unwrap();
            if !state.jobs.is_empty() {
                return Err("ResourceBusy".into());
            }
            if state.status != Status::Closed {
                return Err("ResourceNotClosed".into());
            }
            state.status = Status::Removed;
        }
        let implementation = resource.implementation.lock().unwrap().take();
        if let Err(error) = catch_user(|| drop(implementation)) {
            resource.state.lock().unwrap().status = Status::Faulted;
            resource.owner.state.lock().unwrap().phase = Phase::Faulted;
            return Err(error);
        }
        self.records.lock().unwrap().resources.remove(&id);
        resource.owner.state.lock().unwrap().resources.remove(&id);
        Ok(Value::Null)
    }
    pub(super) fn finish_resource_job(&self, kind: JobKind, result: &PluginResult<Value>) {
        let JobKind::Resource(action) = kind else {
            return;
        };
        let resource = self
            .records
            .lock()
            .unwrap()
            .resources
            .get(&action.id())
            .cloned()
            .unwrap();
        let mut state = resource.state.lock().unwrap();
        if state.status == Status::Faulted {
            return;
        }
        if action.is_close() && result.is_ok() {
            state.status = Status::Closed;
        }
        if matches!(action, ResourceAction::StreamNext(_))
            && result.as_ref().is_ok_and(|value| value["done"] == true)
        {
            state.ended = true;
        }
    }
    pub(super) fn drop_resource_job(&self, kind: JobKind, job: u64) {
        if let JobKind::Resource(action) = kind {
            if let Some(resource) = self
                .records
                .lock()
                .unwrap()
                .resources
                .get(&action.id())
                .cloned()
            {
                resource.state.lock().unwrap().jobs.remove(&job);
            }
        }
    }
    pub(super) fn fault_resource_job(&self, kind: JobKind) {
        if let JobKind::Resource(action) = kind {
            if let Some(resource) = self
                .records
                .lock()
                .unwrap()
                .resources
                .get(&action.id())
                .cloned()
            {
                resource.state.lock().unwrap().status = Status::Faulted;
            }
        }
    }
}
