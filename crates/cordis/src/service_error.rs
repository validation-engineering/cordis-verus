//! Structured errors at the ordinary Rust service-read boundary.
use crate::{PluginId, Port};
use std::fmt;
use std::panic::Location;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ServiceReadFailure {
    Undeclared,
    ClosedEpisode,
    MissingValue,
    TypeMismatch,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct ServiceReadError {
    pub reason: ServiceReadFailure,
    pub service: &'static str,
    pub value_type: &'static str,
    pub port: Port,
    pub plugin: PluginId,
    pub generation: u64,
    pub provider: Option<PluginId>,
    pub location: &'static Location<'static>,
}
impl ServiceReadError {
    fn message(&self) -> String {
        match self.reason {
            ServiceReadFailure::Undeclared => format!("undeclared dependency: {}", self.service),
            ServiceReadFailure::ClosedEpisode => "owner episode has completed".into(),
            ServiceReadFailure::MissingValue | ServiceReadFailure::TypeMismatch => {
                format!("service has no value: {}", self.service)
            }
        }
    }
}
impl fmt::Display for ServiceReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} ({:?}, type {}, port {:?}, plugin {}, generation {}, provider {:?}, at {})",
            self.message(),
            self.reason,
            self.value_type,
            self.port,
            self.plugin,
            self.generation,
            self.provider,
            self.location
        )
    }
}
impl std::error::Error for ServiceReadError {}
