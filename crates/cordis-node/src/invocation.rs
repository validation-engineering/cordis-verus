//! Native callback paths. No JavaScript callback runs while the driver is borrowed.
use crate::NativeDriver;
use cordis_driver::InvocationPath as Path;
use cordis_driver::{Driver, DriverError};
use napi::{Error, Result, Status};
use napi_derive::napi;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[napi]
pub struct NativeInvocation {
    path: Path,
}
fn decimal<T: std::str::FromStr>(value: String, label: &str) -> Result<T> {
    value
        .parse()
        .map_err(|_| Error::new(Status::InvalidArg, format!("Invalid {label}")))
}
impl NativeDriver {
    fn scope_command<T>(
        &self,
        call: impl FnOnce(&mut Driver) -> std::result::Result<T, DriverError>,
    ) -> Result<T> {
        self.check_fault()?;
        let mut driver = self.driver.try_borrow_mut().map_err(|_| {
            Error::new(
                Status::GenericFailure,
                "ReentrantCommand: driver is already borrowed",
            )
        })?;
        match catch_unwind(AssertUnwindSafe(|| call(&mut driver))) {
            Ok(Ok(result)) => Ok(result),
            Ok(Err(error)) => Err(Error::new(Status::InvalidArg, error.to_string())),
            Err(payload) => {
                std::mem::forget(payload);
                self.faulted.set(true);
                if let Ok(mut wake) = self.wake.lock() {
                    *wake = None;
                }
                Err(Error::new(
                    Status::GenericFailure,
                    "DomainFaulted: invocation command panicked",
                ))
            }
        }
    }
}
#[napi]
impl NativeDriver {
    /// The complete native parent path is captured, including inactive ancestors.
    #[napi]
    pub fn begin_invocation(
        &self,
        id: String,
        generation: String,
        parent: Option<&NativeInvocation>,
    ) -> Result<NativeInvocation> {
        let id = decimal(id, "fiber ID")?;
        let generation = decimal(generation, "generation")?;
        self.scope_command(|driver| {
            driver.begin_invocation(id, generation, parent.map(|parent| &parent.path))
        })
        .map(|path| NativeInvocation { path })
    }
    #[napi]
    pub fn finish_invocation(&self, invocation: &NativeInvocation) -> Result<()> {
        self.scope_command(|driver| driver.finish_invocation(&invocation.path))
    }
    #[napi]
    pub fn invocation_live(&self, invocation: &NativeInvocation) -> Result<bool> {
        self.scope_command(|driver| driver.invocation_live(&invocation.path))
    }
    #[napi]
    pub fn invocation_own_live(&self, invocation: &NativeInvocation) -> Result<bool> {
        self.scope_command(|driver| driver.invocation_own_live(&invocation.path))
    }
    #[napi]
    pub fn check_invocation_wait(
        &self,
        invocation: &NativeInvocation,
        target: String,
    ) -> Result<String> {
        let target = decimal(target, "target ID")?;
        self.scope_command(|driver| driver.check_invocation_wait(&invocation.path, target))
            .map(|value| value.to_string())
    }
}
