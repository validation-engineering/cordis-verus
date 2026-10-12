//! Typed host adapter for the executable, verified Cordis kernel.
pub mod callback_error;
pub use callback_error::{CallbackError, CallbackErrorKind};
pub mod config;
pub mod diagnostics;
pub mod events;
mod future_support;
pub mod loader;
pub mod owned_events;
pub mod persistence;
pub mod process_plugin;
pub mod resources;
pub mod runtime;
pub mod service_error;
pub mod typed;
pub use service_error::{ServiceReadError, ServiceReadFailure};
pub use typed::{ConfiguredDependency, Dependencies, TypedPluginBuilder};
pub mod timer;
pub use cordis_kernel::{Binding, Error as KernelError, Phase, Port};
pub use events::{Event, EventScope, Subscription};
pub use runtime::*;

#[cfg(feature = "tokio")]
pub mod app;
#[cfg(feature = "tokio")]
pub use app::{App, AppError, PluginHandle};
