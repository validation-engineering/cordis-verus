//! Ordinary Rust services adapter; callback and scheduling behavior is a host boundary.
use super::*;

impl<T> Clone for ServiceHandle<T> {
    fn clone(&self) -> Self {
        Self {
            child: self.child.clone(),
            slot: self.slot.clone(),
            status: self.status.clone(),
            marker: PhantomData,
        }
    }
}
impl<T: Any + Send + Sync> ServiceHandle<T> {
    pub fn id(&self) -> Option<PluginId> {
        self.child.id()
    }
    pub fn initialized(&self) -> bool {
        self.status.initialized()
    }
    pub fn finished(&self) -> bool {
        self.status.finished()
    }
    pub fn errors(&self) -> Vec<CallbackError> {
        self.status.errors()
    }
    pub fn get(&self) -> Result<Arc<T>, CallbackError> {
        self.slot
            .get()
            .ok_or_else(|| "service value type mismatch".into())
    }
    pub fn set(&self, value: T) -> CallbackResult {
        let mut status = lock(&self.status.status);
        if status.checked().observe().cancelled() || status.checked().observe().finished() {
            return Err(CANCELLED.into());
        }
        let previous = match self.slot.replace(Arc::new(value)) {
            Ok(previous) => previous,
            Err(rejected) => {
                drop(status);
                drop(rejected.value);
                return Err(rejected.message.into());
            }
        };
        let driver = status.driver.take();
        let notify = status.notify.clone();
        drop(status);
        drop(previous);
        if let Some(notify) = notify {
            notify();
        }
        if let Some(driver) = driver {
            driver.wake();
        }
        Ok(())
    }
    pub fn refresh(&self) {
        let (driver, notify) = {
            let mut status = lock(&self.status.status);
            (status.driver.take(), status.notify.clone())
        };
        if let Some(notify) = notify {
            notify();
        }
        if let Some(driver) = driver {
            driver.wake();
        }
    }
    pub fn dispose(&self) {
        self.status.cancel();
    }
    /// A certified observation of the actual status in its execution domain.
    /// Wakers and OS scheduling are outside this trajectory.
    pub fn execution_snapshot(&self) -> cordis_kernel::reversible_value::joint::Snapshot {
        self.status.execution_snapshot()
    }
    pub fn join(&self) -> EffectJoin {
        self.status.join()
    }
}
