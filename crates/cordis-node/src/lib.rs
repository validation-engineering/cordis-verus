//! Node-API boundary for the value-independent lifecycle driver.
//!
//! Graph commands carry metadata; the optional Rust plugin executor has a
//! separate, explicitly described JSON DTO service boundary. Neither command
//! path invokes JavaScript while holding a Driver or executor borrow.

mod interop;
pub mod plugin;
use cordis_driver::Driver;
use napi::{bindgen_prelude::Function, Env, Error, Result, Status};
use napi_derive::napi;
use std::cell::{Cell, RefCell};
use std::panic::{catch_unwind, AssertUnwindSafe};

/// A Node-owned lifecycle domain. The executor drains returned actions only
/// after `command` returns and the mutable driver borrow has been released.
#[napi]
pub struct NativeDriver {
    driver: RefCell<Driver>,
    faulted: Cell<bool>,
    backend: RefCell<plugin::Backend>,
    wake: interop::WakeSlot,
}

#[napi]
impl NativeDriver {
    /// Construct a fresh domain; completion tickets cannot cross domains.
    #[napi(constructor)]
    pub fn new() -> Result<Self> {
        Self::with_factories(plugin::FactoryRegistry::new())
    }

    /// Describe the explicitly registered JSON DTO service interfaces.
    #[napi]
    pub fn rust_info(&self) -> Result<String> {
        self.check_fault()?;
        let backend = self
            .backend
            .try_borrow()
            .map_err(|e| Error::new(Status::GenericFailure, e.to_string()))?;
        Ok(backend.info().to_string())
    }
    /// Poll Rust work or dispatch one interop request, outside the graph borrow.
    #[napi]
    pub fn rust_command(&self, env: Env, input: String) -> Result<String> {
        self.native_command(env, input)
    }
    /// Install an event-driven wake callback. Pending futures retain Node's loop;
    /// idle domains do not. The callback is never invoked inside a Rust borrow.
    #[napi]
    pub fn rust_wake(&self, env: Env, callback: Function<'_, (), ()>) -> Result<()> {
        self.install_wake(env, callback)
    }

    /// Submit one metadata command. No plugin value is serialized by this API.
    #[napi]
    pub fn command(&self, input: String) -> Result<String> {
        if self.faulted.get() {
            return Err(Error::new(
                Status::GenericFailure,
                "DomainFaulted: create a new domain",
            ));
        }
        let mut driver = self.driver.try_borrow_mut().map_err(|_| {
            Error::new(
                Status::GenericFailure,
                "ReentrantCommand: driver is already borrowed",
            )
        })?;
        // A panic is a domain fault, never a partially successful command or a
        // recoverable plugin exception. It must not unwind across Node's ABI.
        match catch_unwind(AssertUnwindSafe(|| driver.command(&input))) {
            Ok(Ok(reply)) => Ok(reply),
            Ok(Err(error)) => Err(Error::new(Status::InvalidArg, error.to_string())),
            Err(payload) => {
                std::mem::forget(payload);
                self.faulted.set(true);
                if let Ok(mut wake) = self.wake.lock() {
                    *wake = None;
                }
                Err(Error::new(
                    Status::GenericFailure,
                    "DomainFaulted: native command panicked",
                ))
            }
        }
    }
}

impl NativeDriver {
    fn check_fault(&self) -> Result<()> {
        if self.faulted.get() {
            Err(Error::new(
                Status::GenericFailure,
                "DomainFaulted: create a new domain",
            ))
        } else {
            Ok(())
        }
    }
}

impl Drop for NativeDriver {
    fn drop(&mut self) {
        if let Ok(mut wake) = self.wake.lock() {
            *wake = None;
        }
        // Backend's Drop contains arbitrary plugin/future destructors separately.
    }
}

/// The binding protocol is intentionally separate from Cordis package versions.
#[napi]
pub fn binding_info() -> String {
    concat!(
        "{\"abi\":1,\"package\":\"cordis-node\",",
        "\"version\":\"",
        env!("CARGO_PKG_VERSION"),
        "\",",
        "\"profile\":\"cordis-4.0.0-rc.10-experimental\",",
        "\"profiles\":[\"cordis\",\"harness\"],",
        "\"values\":\"javascript-object-table\"}"
    )
    .to_owned()
}
