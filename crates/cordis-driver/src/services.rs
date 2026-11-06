//! Node service commands: wire conversion around the verified state owner.
//! Ownership, generation and dynamic declaration transitions are checked by
//! NodeRuntime; JS object contents and command decoding remain host boundaries.
use super::*;
use cordis_kernel::node_runtime::services::ServiceError;

fn admission_error(error: EpisodeError) -> DriverError {
    match error {
        EpisodeError::Stale => DriverError::new("StaleEpisode", "plugin generation is not current"),
        _ => DriverError::new("AdmissionClosed", "episode cannot acquire new resources"),
    }
}
pub(super) fn service_error(error: ServiceError) -> DriverError {
    match error {
        ServiceError::Access(error) => admission_error(error),
        ServiceError::StalePublication => DriverError::new(
            "StalePublication",
            "publication does not belong to this episode",
        ),
        ServiceError::Publication(error) => error.into(),
        ServiceError::Declaration(error) => error.into(),
    }
}

impl Driver {
    /// Validate admission for new resource work, including escaped async calls.
    pub fn validate(&self, id: usize, generation: u64) -> Result<(), DriverError> {
        self.kernel
            .core
            .validate(id, generation)
            .map_err(admission_error)
    }

    /// Publish an opaque value while retaining the logical provider identity.
    pub fn publish(
        &mut self,
        id: usize,
        generation: u64,
        port: ServicePort,
        value: u64,
    ) -> Result<usize, DriverError> {
        use cordis_kernel::node_runtime::interfaces::PublishError;
        self.kernel
            .core
            .publish_service(id, generation, port.into(), value)
            .map(|publication| publication.0)
            .map_err(|error| match error {
                PublishError::Access(error) => admission_error(error),
                PublishError::Declaration(error) => error.into(),
                PublishError::Publication(error) => error.into(),
            })
    }

    /// Replace one slot without changing publication identity or notifying peers.
    pub fn set(
        &mut self,
        id: usize,
        generation: u64,
        publication: usize,
        value: u64,
    ) -> Result<(), DriverError> {
        self.kernel
            .core
            .replace_service(id, generation, PublicationId(publication), value)
            .map_err(service_error)
    }

    /// Withdrawal allows existing committed consumers to keep the old slot.
    /// Cleanup may idempotently revoke an already withdrawn publication.
    pub fn revoke(
        &mut self,
        id: usize,
        generation: u64,
        publication: usize,
    ) -> Result<(), DriverError> {
        self.kernel
            .core
            .revoke_service(id, generation, PublicationId(publication))
            .map_err(service_error)
    }

    /// Read a committed binding during setup, use, and cleanup. An unowned root
    /// lookup uses current visibility and confers no lifecycle consumer lease.
    pub fn resolve(
        &mut self,
        port: ServicePort,
        consumer: Option<usize>,
        generation: Option<u64>,
    ) -> Result<Option<Value>, DriverError> {
        use cordis_kernel::node_runtime::reads::ReadError;
        let out = self
            .kernel
            .core
            .resolve(port.into(), consumer, generation)
            .map_err(|error| match error {
                ReadError::Unknown => DriverError::from(KernelError::Unknown),
                ReadError::Stale => {
                    DriverError::new("StaleEpisode", "lookup belongs to an earlier episode")
                }
            })?;
        Ok(out.map(|read| {
            json!({
                "publication":read.publication.0.to_string(),
                "value":read.value.to_string(),
                "owner":read.owner.to_string(),
            })
        }))
    }

    pub(super) fn reconcile_publications(&mut self) -> Result<(), DriverError> {
        self.kernel
            .core
            .reconcile_declarations()
            .map_err(Into::into)
    }
    pub(super) fn reclaim(
        &mut self,
        id: usize,
        generation: u64,
        publication: usize,
    ) -> Result<bool, DriverError> {
        self.kernel
            .core
            .reclaim_service(id, generation, PublicationId(publication))
            .map_err(service_error)
    }
}
