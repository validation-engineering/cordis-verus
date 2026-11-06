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
        self.status
            .replace_service_value(&self.slot, Arc::new(value))
    }
    pub fn refresh(&self) {
        self.status.refresh_driver();
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
