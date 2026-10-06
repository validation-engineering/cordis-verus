//! Explicit, bounded logical state migration. No library-owned memory escapes.
use super::*;

/// One factory's output schema and the versions its restore hook accepts.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct CheckpointSchema {
    pub schema: String,
    pub version: u32,
    pub accepts: Vec<u32>,
}
impl CheckpointSchema {
    pub fn validate(&self) -> PluginResult<()> {
        let versions: BTreeSet<_> = self.accepts.iter().copied().collect();
        if self.schema.is_empty()
            || self.schema.len() > 256
            || self.version == 0
            || self.accepts.len() > 64
            || versions.len() != self.accepts.len()
            || versions.contains(&0)
        {
            return Err("InvalidCheckpointSchema".into());
        }
        Ok(())
    }
    pub fn accepts(&self, checkpoint: &Checkpoint) -> bool {
        self.schema == checkpoint.schema
            && (self.version == checkpoint.version || self.accepts.contains(&checkpoint.version))
    }
}

/// Portable logical state, never a native address, resource, or child handle.
/// Only `data` is charged against the 512 KiB / 64-container value limits.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct Checkpoint {
    pub schema: String,
    pub version: u32,
    pub data: Value,
}
impl Checkpoint {
    pub fn validate(&self) -> PluginResult<()> {
        if self.schema.is_empty() || self.schema.len() > 256 || self.version == 0 {
            return Err("InvalidCheckpointSchema".into());
        }
        if !has_valid_depth(&self.data) {
            return Err("ValueTooDeep".into());
        }
        if serde_json::to_vec(&self.data).map_or(true, |bytes| bytes.len() > MAX_MESSAGE_BYTES / 2)
        {
            return Err("ResultTooLarge".into());
        }
        Ok(())
    }
}

impl Runtime {
    fn checkpoint_schema(&self, entry: &InstanceEntry) -> PluginResult<&CheckpointSchema> {
        if entry.parent.is_some() {
            return Err("CheckpointRequiresModuleRoot".into());
        }
        self.descriptor
            .checkpoint_schemas
            .get(&entry.descriptor.name)
            .ok_or_else(|| "CheckpointUnsupported".into())
    }
    pub(super) fn checkpoint(&self, instance: u64) -> PluginResult<Value> {
        let entry = self.instance(instance)?;
        let _gate = entry.gate.try_lock().map_err(|_| "InstanceBusy")?;
        let schema = self.checkpoint_schema(&entry)?;
        {
            let state = entry.state.lock().unwrap();
            if state.phase == Phase::Checkpointed {
                return serde_json::to_value(state.checkpoint.as_ref().unwrap())
                    .map_err(|_| "InvalidCheckpoint".into());
            }
            if state.phase != Phase::Active {
                return Err("InvalidLifecycleState".into());
            }
            if !state.jobs.is_empty()
                || !state.resources.is_empty()
                || !children::is_drained(&state)
            {
                return Err("CheckpointNotDrained".into());
            }
        }
        let value = entry.value.lock().unwrap().as_ref().unwrap().clone();
        let result = match catch_user(|| value.checkpoint()) {
            Ok(result) => bounded_result(result),
            Err(error) => {
                entry.state.lock().unwrap().phase = Phase::Faulted;
                return Err(error);
            }
        }?;
        let checkpoint = Checkpoint {
            schema: schema.schema.clone(),
            version: schema.version,
            data: result,
        };
        let output = serde_json::to_value(&checkpoint).map_err(|_| "InvalidCheckpoint")?;
        let mut state = entry.state.lock().unwrap();
        state.checkpoint = Some(checkpoint);
        state.phase = Phase::Checkpointed;
        Ok(output)
    }
    pub(super) fn restore(&self, instance: u64, checkpoint: Checkpoint) -> PluginResult<Value> {
        let entry = self.instance(instance)?;
        let _gate = entry.gate.try_lock().map_err(|_| "InstanceBusy")?;
        {
            let mut state = entry.state.lock().unwrap();
            if state.phase != Phase::Created || state.restore_attempted {
                return Err("InvalidLifecycleState".into());
            }
            state.restore_attempted = true;
            // All ordinary failures are cleanup-only, including schema validation.
            state.phase = Phase::SetupFailed;
        }
        let schema = self.checkpoint_schema(&entry)?;
        if !has_valid_depth(&checkpoint.data) {
            discard_deep_value(checkpoint.data);
            return Err("ValueTooDeep".into());
        }
        checkpoint.validate()?;
        if !schema.accepts(&checkpoint) {
            return Err("CheckpointSchemaMismatch".into());
        }
        let value = entry.value.lock().unwrap().as_ref().unwrap().clone();
        match catch_user(|| value.restore(checkpoint)) {
            Ok(Ok(())) => {
                entry.state.lock().unwrap().phase = Phase::Created;
                Ok(Value::Null)
            }
            Ok(Err(error)) => Err(error),
            Err(error) => {
                entry.state.lock().unwrap().phase = Phase::Faulted;
                Err(error)
            }
        }
    }
}

#[cfg(test)]
#[path = "checkpoint_tests.rs"]
mod tests;
