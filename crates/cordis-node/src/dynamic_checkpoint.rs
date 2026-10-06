//! Bounded host-owned logical state. Tokens outlive native instances, but never
//! retain their resources or grant an earlier instance's execution authority.
use super::*;
use cordis_plugin_api::{Checkpoint, CheckpointSchema};
use std::sync::Weak;
static NEXT_CHECKPOINT: AtomicU64 = AtomicU64::new(1);
const MAX_TOKENS: usize = 64;
const MAX_BYTES: usize = 16 * 1024 * 1024;
#[derive(Clone)]
struct Source {
    plugin_id: String,
    factory: String,
    factory_ref: String,
    schema: CheckpointSchema,
    session: u64,
    id: usize,
    generation: u64,
}
impl Source {
    fn value(&self) -> Value {
        json!({"pluginId":self.plugin_id,"factory":self.factory,"factoryRef":self.factory_ref,"schema":self.schema.schema,"version":self.schema.version,"session":self.session.to_string(),"id":self.id.to_string(),"generation":self.generation.to_string()})
    }
}
struct Entry {
    source: Source,
    value: Option<Checkpoint>,
    error: Option<String>,
    capturing: bool,
    retired: bool,
    bytes: usize,
}
#[derive(Default)]
struct Records {
    bytes: usize,
    reserved: usize,
    entries: BTreeMap<u64, Entry>,
    instances: BTreeMap<u64, Weak<InstanceState>>,
}
#[derive(Default)]
pub(crate) struct Journal(Mutex<Records>);
pub(super) struct InstanceState {
    pub(super) journal: Arc<Journal>,
    plugin_id: String,
    factory: String,
    factory_ref: String,
    schema: Option<CheckpointSchema>,
    session: AtomicU64,
    token: AtomicU64,
    setup_done: AtomicBool,
    retired: AtomicBool,
    restore: Mutex<Option<Checkpoint>>,
}
impl InstanceState {
    pub(super) fn new(
        journal: Arc<Journal>,
        module: &Module,
        factory: &str,
        root: bool,
    ) -> Arc<Self> {
        Arc::new(Self {
            journal,
            plugin_id: module.description.module_id.clone(),
            factory: factory.into(),
            factory_ref: module.factory_ref(factory),
            schema: root
                .then(|| module.description.checkpoint_schemas.get(factory).cloned())
                .flatten(),
            session: AtomicU64::new(0),
            token: AtomicU64::new(0),
            setup_done: AtomicBool::new(false),
            retired: AtomicBool::new(false),
            restore: Mutex::new(None),
        })
    }
    pub(super) fn bind(self: &Arc<Self>, session: u64) {
        self.session.store(session, Ordering::Release);
        self.journal
            .0
            .lock()
            .unwrap()
            .instances
            .insert(session, Arc::downgrade(self));
    }
    pub(super) fn setup_done(&self) {
        self.setup_done.store(true, Ordering::Release);
    }
    pub(super) fn restore(&self, module: &Module, handle: u64) -> PluginResult<()> {
        let checkpoint = self.restore.lock().unwrap().take();
        if let Some(checkpoint) = checkpoint {
            module.request(json!({"op":"restore","instance":handle,"checkpoint":checkpoint}))?;
        }
        Ok(())
    }
    pub(super) fn capture(&self, module: &Module, handle: u64) -> PluginResult<()> {
        let token = self.token.load(Ordering::Acquire);
        if token == 0 {
            return Ok(());
        }
        {
            let mut records = self.journal.0.lock().unwrap();
            let Some(entry) = records.entries.get(&token) else {
                return Ok(());
            };
            if entry.value.is_some() {
                return Ok(());
            }
            if entry.capturing {
                return Err("NativeCheckpointBusy".into());
            }
            // Reserve protocol maximum before user code, never discard a
            // completed snapshot merely because later captures fill storage.
            if records.bytes + records.reserved + MAX_MESSAGE_BYTES > MAX_BYTES {
                records.entries.get_mut(&token).unwrap().error =
                    Some("NativeCheckpointByteCapacity".into());
                return Err("NativeCheckpointByteCapacity".into());
            }
            records.reserved += MAX_MESSAGE_BYTES;
            records.entries.get_mut(&token).unwrap().capturing = true;
        }
        let result = (|| -> PluginResult<(Checkpoint, usize)> {
            let value = module.request(json!({"op":"checkpoint","instance":handle}))?;
            let checkpoint: Checkpoint =
                serde_json::from_value(value).map_err(|_| "NativeCheckpointInvalid")?;
            checkpoint.validate()?;
            let schema = self.schema.as_ref().ok_or("NativeCheckpointUnsupported")?;
            if checkpoint.schema != schema.schema || checkpoint.version != schema.version {
                return Err("NativeCheckpointSchemaMismatch".into());
            }
            let bytes = serde_json::to_vec(&checkpoint)
                .map_err(|_| "NativeCheckpointInvalid")?
                .len();
            if bytes > MAX_MESSAGE_BYTES {
                return Err("NativeCheckpointTooLarge".into());
            }
            Ok((checkpoint, bytes))
        })();
        let mut records = self.journal.0.lock().unwrap();
        records.reserved -= MAX_MESSAGE_BYTES;
        let entry = records
            .entries
            .get_mut(&token)
            .expect("capturing token cannot be dropped");
        entry.capturing = false;
        match result {
            Ok((checkpoint, bytes)) => {
                entry.value = Some(checkpoint);
                entry.error = None;
                entry.bytes += bytes;
                records.bytes += bytes;
                Ok(())
            }
            Err(error) => {
                let error = bounded_reverse_result(Err(error)).unwrap_err();
                entry.error = Some(error.clone());
                Err(error)
            }
        }
    }
    pub(super) fn destroyed(&self) {
        self.retired.store(true, Ordering::Release);
        let session = self.session.load(Ordering::Acquire);
        for entry in self
            .journal
            .0
            .lock()
            .unwrap()
            .entries
            .values_mut()
            .filter(|e| e.source.session == session)
        {
            entry.retired = true;
        }
    }
}
impl Journal {
    fn instance(&self, session: u64) -> PluginResult<Arc<InstanceState>> {
        self.0
            .lock()
            .unwrap()
            .instances
            .get(&session)
            .and_then(Weak::upgrade)
            .ok_or("NativeCheckpointUnsupported".into())
    }
    pub(super) fn arm(&self, session: u64, id: usize, generation: u64) -> PluginResult<Value> {
        let instance = self.instance(session)?;
        let schema = instance
            .schema
            .clone()
            .ok_or("NativeCheckpointUnsupported")?;
        if !instance.setup_done.load(Ordering::Acquire) || instance.retired.load(Ordering::Acquire)
        {
            return Err("NativeCheckpointNotActive".into());
        }
        if instance.token.load(Ordering::Acquire) != 0 {
            return Err("NativeCheckpointAlreadyArmed".into());
        }
        let mut records = self.0.lock().unwrap();
        if records.entries.len() >= MAX_TOKENS {
            return Err("NativeCheckpointTokenCapacity".into());
        }
        let token = allocate(&NEXT_CHECKPOINT, "NativeCheckpointTokenCapacity")?;
        let source = Source {
            plugin_id: instance.plugin_id.clone(),
            factory: instance.factory.clone(),
            factory_ref: instance.factory_ref.clone(),
            schema,
            session,
            id,
            generation,
        };
        let bytes = serde_json::to_vec(&source.value())
            .map_err(|_| "NativeCheckpointInvalid")?
            .len();
        if records.bytes + records.reserved + bytes > MAX_BYTES {
            return Err("NativeCheckpointByteCapacity".into());
        }
        records.bytes += bytes;
        records.entries.insert(
            token,
            Entry {
                source,
                value: None,
                error: None,
                capturing: false,
                retired: false,
                bytes,
            },
        );
        instance.token.store(token, Ordering::Release);
        Ok(json!({"token":token.to_string()}))
    }
    pub(crate) fn read(&self, token: &str) -> PluginResult<Value> {
        let token = parse(token)?;
        let records = self.0.lock().unwrap();
        let entry = records
            .entries
            .get(&token)
            .ok_or("UnknownNativeCheckpoint")?;
        let source = &entry.source;
        let mut reply = json!({"token":token.to_string(),"state":if entry.value.is_some(){"captured"}else if entry.error.is_some(){"failed"}else{"armed"},"retired":entry.retired,"source":source.value()});
        if let Some(value) = &entry.value {
            reply["value"] = json!(value);
        }
        if let Some(error) = &entry.error {
            reply["failure"] = json!(error);
        }
        Ok(reply)
    }
    pub(crate) fn drop_token(&self, token: &str) -> PluginResult<()> {
        let token = parse(token)?;
        let mut records = self.0.lock().unwrap();
        let entry = records
            .entries
            .get(&token)
            .ok_or("UnknownNativeCheckpoint")?;
        if entry.capturing {
            return Err("NativeCheckpointBusy".into());
        }
        let entry = records.entries.remove(&token).unwrap();
        records.bytes -= entry.bytes;
        if let Some(instance) = records
            .instances
            .get(&entry.source.session)
            .and_then(Weak::upgrade)
        {
            let _ = instance
                .token
                .compare_exchange(token, 0, Ordering::AcqRel, Ordering::Acquire);
        }
        Ok(())
    }
    pub(crate) fn release_session(&self, session: u64) {
        self.0.lock().unwrap().instances.remove(&session);
    }
    pub(super) fn prepare_restore(
        &self,
        token: &str,
        module: &Module,
        factory: &str,
    ) -> PluginResult<Checkpoint> {
        let token = parse(token)?;
        let records = self.0.lock().unwrap();
        let entry = records
            .entries
            .get(&token)
            .ok_or("UnknownNativeCheckpoint")?;
        let value = entry.value.as_ref().ok_or("NativeCheckpointNotCaptured")?;
        if !entry.retired {
            return Err("NativeCheckpointSourceNotRetired".into());
        }
        if entry.source.plugin_id != module.description.module_id || entry.source.factory != factory
        {
            return Err("NativeCheckpointIdentityMismatch".into());
        }
        let schema = module
            .description
            .checkpoint_schemas
            .get(factory)
            .ok_or("NativeCheckpointUnsupported")?;
        if !schema.accepts(value) {
            return Err("NativeCheckpointSchemaMismatch".into());
        }
        Ok(value.clone())
    }
    pub(super) fn bind_restore(&self, session: u64, value: Checkpoint) -> PluginResult<()> {
        *self.instance(session)?.restore.lock().unwrap() = Some(value);
        Ok(())
    }
    pub(crate) fn info(&self) -> Value {
        let records = self.0.lock().unwrap();
        json!({"tokens":records.entries.len(),"bytes":records.bytes,"tokenLimit":MAX_TOKENS,"byteLimit":MAX_BYTES})
    }
}
fn parse(token: &str) -> PluginResult<u64> {
    token
        .parse::<u64>()
        .ok()
        .filter(|v| *v > 0)
        .ok_or("InvalidNativeCheckpoint".into())
}
impl super::super::Backend {
    pub(crate) fn checkpoint_read(&self, token: &str) -> PluginResult<Value> {
        self.native_checkpoints.read(token)
    }
    pub(crate) fn checkpoint_drop(&self, token: &str) -> PluginResult<()> {
        self.native_checkpoints.drop_token(token)
    }
    pub(crate) fn checkpoint_arm(&self, session: u64) -> PluginResult<Value> {
        let owner = self.sessions.get(&session).ok_or("UnknownSession")?;
        if owner.cleanup_done || owner.cancellation.is_cancelled() {
            return Err("NativeCheckpointNotActive".into());
        }
        self.native_checkpoints
            .arm(session, owner.id, owner.generation)
    }
    pub(crate) fn checkpoint_restore(
        &self,
        factory: &str,
        token: Option<&str>,
    ) -> PluginResult<Option<Checkpoint>> {
        let Some(token) = token else {
            return Ok(None);
        };
        let (module, name) = self
            .modules
            .values()
            .find_map(|module| {
                module
                    .description
                    .factories
                    .iter()
                    .find(|d| module.factory_ref(&d.name) == factory)
                    .map(|d| (module, &d.name))
            })
            .ok_or("NativeCheckpointUnsupported")?;
        self.native_checkpoints
            .prepare_restore(token, module, name)
            .map(Some)
    }
}
