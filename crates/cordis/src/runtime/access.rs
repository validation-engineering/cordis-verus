//! A mutable operation view that preserves the Loader's runtime identity.
use super::{
    AsyncSetup, CallbackResult, Context, EffectHandle, EffectIterator, Join, Plugin, PluginId,
    Runtime, RuntimeError, ServiceKey, Settle, Setup, ShutdownError,
};
use crate::diagnostics::Compaction;
use std::any::Any;
use std::future::Future;
use std::ops::Deref;

/// Mutable runtime operations borrowed from a Loader. Read methods are
/// available through `Deref`; there is deliberately no `DerefMut` or method
/// returning `&mut Runtime`. This keeps its configuration in the same domain.
///
/// Futures consume the view and borrow the Loader for their entire lifetime,
/// so `let pending = loader.runtime_mut().settle();` remains valid. Dropping a
/// future releases that borrow and preserves the runtime's usual recovery state.
///
/// A runtime cannot be swapped out through this view:
/// ```compile_fail,E0596
/// use cordis::{Context, Runtime};
/// use cordis::loader::{FactoryRegistry, Loader};
/// let mut loader = Loader::new(Context::new(), FactoryRegistry::default());
/// let _old = std::mem::replace(&mut *loader.runtime_mut(), Runtime::new());
/// ```
/// Inspection and ordinary runtime operations remain available:
/// ```
/// use cordis::Context;
/// use cordis::loader::{FactoryRegistry, Loader};
/// let mut loader = Loader::new(Context::new(), FactoryRegistry::default());
/// assert!(loader.runtime_mut().ids().is_empty());
/// loader.runtime_mut().dispose_all().unwrap();
/// let pending = loader.runtime_mut().settle();
/// drop(pending);
/// let _checkpoint = loader.execution_snapshot();
/// ```
pub struct RuntimeAccess<'a> {
    inner: &'a mut Runtime,
}
impl Deref for RuntimeAccess<'_> {
    type Target = Runtime;
    fn deref(&self) -> &Runtime {
        self.inner
    }
}
impl<'a> RuntimeAccess<'a> {
    pub(crate) fn new(inner: &'a mut Runtime) -> Self {
        Self { inner }
    }
    pub fn compact(&mut self) -> Compaction {
        self.inner.compact()
    }
    pub fn mount(
        &mut self,
        context: &Context,
        parent: Option<PluginId>,
        plugin: Plugin,
    ) -> Result<PluginId, RuntimeError> {
        self.inner.mount(context, parent, plugin)
    }
    pub fn retry_cleanup(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        self.inner.retry_cleanup(id)
    }
    pub fn on_cleanup(
        &mut self,
        id: PluginId,
        cleanup: impl FnOnce() -> CallbackResult + Send + 'static,
    ) -> Result<(), RuntimeError> {
        self.inner.on_cleanup(id, cleanup)
    }
    pub fn on_cleanup_async<F, Fut>(&mut self, id: PluginId, cleanup: F) -> Result<(), RuntimeError>
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.inner.on_cleanup_async(id, cleanup)
    }
    pub fn on_cleanup_retryable(
        &mut self,
        id: PluginId,
        cleanup: impl FnMut() -> CallbackResult + Send + 'static,
    ) -> Result<(), RuntimeError> {
        self.inner.on_cleanup_retryable(id, cleanup)
    }
    pub fn on_cleanup_retryable_async<F, Fut>(
        &mut self,
        id: PluginId,
        cleanup: F,
    ) -> Result<(), RuntimeError>
    where
        F: FnMut() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.inner.on_cleanup_retryable_async(id, cleanup)
    }
    pub fn effect(
        &mut self,
        id: PluginId,
        effect: impl EffectIterator,
    ) -> Result<EffectHandle, RuntimeError> {
        self.inner.effect(id, effect)
    }
    pub fn set<T: Any + Send + Sync>(
        &mut self,
        id: PluginId,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<(), RuntimeError> {
        self.inner.set(id, key, value)
    }
    pub fn dispose(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        self.inner.dispose(id)
    }
    pub fn cancel(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        self.inner.cancel(id)
    }
    pub fn dispose_all(&mut self) -> Result<(), RuntimeError> {
        self.inner.dispose_all()
    }
    pub fn restart(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        self.inner.restart(id)
    }
    pub fn update(
        &mut self,
        id: PluginId,
        setup: impl FnMut(&mut Setup<'_>) -> CallbackResult + Send + 'static,
    ) -> Result<(), RuntimeError> {
        self.inner.update(id, setup)
    }
    pub fn update_async<F, Fut>(&mut self, id: PluginId, setup: F) -> Result<(), RuntimeError>
    where
        F: FnMut(AsyncSetup) -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.inner.update_async(id, setup)
    }
    pub fn update_plugin(&mut self, id: PluginId, plugin: Plugin) -> Result<(), RuntimeError> {
        self.inner.update_plugin(id, plugin)
    }
    pub fn prepare_config_update(
        &mut self,
        id: PluginId,
        previous: serde_json::Value,
        next: serde_json::Value,
    ) -> Result<crate::config::ConfigUpdate, RuntimeError> {
        self.inner.prepare_config_update(id, previous, next)
    }
    pub fn take_cleanup_errors(&mut self) -> Vec<RuntimeError> {
        self.inner.take_cleanup_errors()
    }
    pub fn settle(self) -> Settle<'a> {
        self.inner.settle()
    }
    pub fn join(self, id: PluginId) -> Join<'a> {
        self.inner.join(id)
    }
    pub async fn shutdown(self) -> Result<(), ShutdownError> {
        self.inner.shutdown().await
    }
    pub async fn replace(self, id: PluginId, plugin: Plugin) -> Result<PluginId, RuntimeError> {
        self.inner.replace(id, plugin).await
    }
}
