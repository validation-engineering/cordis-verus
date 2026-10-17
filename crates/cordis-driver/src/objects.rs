//! Host-reference operations use the same NodeRuntime as metadata commands.
use crate::*;
use cordis_kernel::node_runtime::bridge::BridgeError;
pub use cordis_kernel::node_runtime::bridge::{Bridge as HostBridge, Call as HostCall, ObjectKey};
fn bridge_error(error: BridgeError) -> DriverError {
    DriverError::new("HostBridge", format!("{error:?}"))
}
pub use cordis_kernel::node_runtime::reads::Selected as HostSelection;
impl Driver {
    pub fn can_enable_host_bridge(&self) -> bool {
        self.kernel.core.interfaces().is_empty()
    }

    pub fn validate_host_snapshot<T>(&self, bridge: &HostBridge<T>) -> Result<(), DriverError> {
        bridge
            .snapshot(&self.kernel.core)
            .map(|_| ())
            .map_err(bridge_error)
    }

    pub fn select_host_import(
        &mut self,
        port: ServicePort,
        consumer: usize,
        generation: u64,
    ) -> Result<Option<HostSelection>, DriverError> {
        self.kernel
            .core
            .select(port.into(), Some(consumer), Some(generation))
            .map_err(|error| DriverError::new("StaticImport", format!("{error:?}")))
    }

    pub fn host_bridge<T>(&self) -> HostBridge<T> {
        HostBridge::new(&self.kernel.core)
    }
    pub fn bind_host_fiber<T>(
        &self,
        bridge: &mut HostBridge<T>,
        id: usize,
        key: ObjectKey,
    ) -> Result<(), DriverError> {
        bridge
            .bind_fiber(&self.kernel.core, id, key)
            .map_err(bridge_error)
    }
    pub fn unbind_host_fiber<T>(
        &self,
        bridge: &mut HostBridge<T>,
        id: usize,
    ) -> Result<Option<u64>, DriverError> {
        bridge
            .unbind_fiber(&self.kernel.core, id)
            .map_err(bridge_error)
    }
    pub fn remove_host_object<T>(
        &self,
        bridge: &mut HostBridge<T>,
        id: u64,
    ) -> Result<Option<T>, DriverError> {
        bridge.remove(&self.kernel.core, id).map_err(bridge_error)
    }
    pub fn begin_host_call<T>(
        &self,
        bridge: &mut HostBridge<T>,
        ticket: ActionTicket,
        fiber: ObjectKey,
        recipe: ObjectKey,
    ) -> Result<HostCall, DriverError> {
        bridge
            .begin_call(
                &self.kernel.core,
                shared::kernel_ticket(&ticket),
                fiber,
                recipe,
            )
            .map_err(bridge_error)
    }
    pub fn complete_host_call<T>(
        &mut self,
        bridge: &mut HostBridge<T>,
        call: &HostCall,
        success: bool,
        error: Option<String>,
    ) -> Result<(), DriverError> {
        if !bridge.validate_call(call) {
            return Err(bridge_error(BridgeError::Stale));
        }
        let ticket = shared::host_ticket(call.ticket());
        // Completion may consume the ticket before a subsequent Finish/Unload
        // reports an error. Do not leave a completed dispatch permanently pinned.
        let result = self.complete(ticket, success, error);
        if !self.kernel.state().pending_matches(call.ticket()) {
            bridge
                .finish_call(&self.kernel.core, call)
                .map_err(bridge_error)?;
        }
        result
    }
    pub fn publish_host_object<T>(
        &mut self,
        bridge: &HostBridge<T>,
        id: usize,
        generation: u64,
        port: ServicePort,
        key: ObjectKey,
        check: bool,
    ) -> Result<usize, DriverError> {
        use cordis_kernel::node_runtime::interfaces::PublishError;
        let publication = bridge
            .publish(&mut self.kernel.core, id, generation, port.into(), key)
            .map_err(bridge_error)?
            .map_err(|error| match error {
                PublishError::Access(error) => DriverError::from(error),
                PublishError::Declaration(error) => DriverError::from(error),
                PublishError::Publication(error) => DriverError::from(error),
            })?;
        if check {
            self.kernel.core.set_checked(publication.0, true);
        }
        Ok(publication.0)
    }
    pub fn set_host_object<T>(
        &mut self,
        bridge: &HostBridge<T>,
        id: usize,
        generation: u64,
        publication: usize,
        key: ObjectKey,
    ) -> Result<(), DriverError> {
        self.validate(id, generation)?;
        let entry = self.owned_publication(id, generation, publication)?;
        if !entry.visible {
            return Err(PublicationError::Revoked.into());
        }
        bridge
            .replace(
                &mut self.kernel.core,
                id,
                generation,
                PublicationId(publication),
                key,
            )
            .map_err(bridge_error)?
            .map_err(|rejected| DriverError::from(rejected.error))?;
        Ok(())
    }
    pub fn resolve_host_object<'a, T>(
        &mut self,
        bridge: &'a HostBridge<T>,
        port: ServicePort,
        consumer: Option<usize>,
        generation: Option<u64>,
    ) -> Result<Option<(usize, usize, &'a T)>, DriverError> {
        bridge
            .resolve(&mut self.kernel.core, port.into(), consumer, generation)
            .map_err(bridge_error)
            .map(|found| found.map(|(read, value)| (read.publication.0, read.owner, value)))
    }
}
