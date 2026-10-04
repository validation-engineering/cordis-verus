//! Typed host adapter for the executable, verified Cordis kernel.
pub mod config;
pub mod diagnostics;
pub mod events;
mod future_support;
pub mod loader;
pub mod owned_events;
pub mod persistence;
pub mod resources;
pub mod runtime;
pub mod timer;
pub use cordis_kernel::{Binding, Error as KernelError, Phase, Port};
pub use events::{Event, EventScope, Subscription};
pub use runtime::*;
