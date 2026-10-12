//! Optional Tokio application driver. One task exclusively owns Runtime; all
//! commands and polls use its existing lifecycle and committed-binding guards.
//!
//! Requests enqueue at the method call. Dropping a returned future cancels only
//! the wait, not the operation. Explicit shutdown is required before stopping
//! Tokio. Callbacks must not await their own readiness/disposal or a provider's
//! disposal: those operations may depend on the callback itself completing.
use crate::diagnostics::{Blocker, PluginSnapshot, RuntimeSnapshot};
use crate::{
    AsyncSetup, CallbackResult, Context, Phase, Plugin, PluginId, Runtime, RuntimeError,
    ServiceKey, Setup, ShutdownError,
};
use std::any::Any;
use std::fmt;
use std::future::{poll_fn, Future};
use std::pin::Pin;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::task::{Context as TaskContext, Poll};
use tokio::sync::{mpsc, oneshot};

type Reply<T> = oneshot::Sender<Result<T, AppError>>;
type SetupFuture = Pin<Box<dyn Future<Output = CallbackResult> + Send>>;
type SyncCallback = Box<dyn FnMut(&mut Setup<'_>) -> CallbackResult + Send>;
type AsyncCallback = Box<dyn FnMut(AsyncSetup) -> SetupFuture + Send>;

#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum AppError {
    NoExecutor,
    Closed,
    DriverStopped,
    Runtime(RuntimeError),
    Cleanup(Vec<RuntimeError>),
    Shutdown(ShutdownError),
}
impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoExecutor => f.write_str(
                "App requires a running Tokio runtime; use App::with_handle to supply one",
            ),
            Self::Closed => f.write_str("application admission is closed"),
            Self::DriverStopped => {
                f.write_str("application driver stopped before completing the request")
            }
            Self::Runtime(error) => error.fmt(f),
            Self::Cleanup(errors) => {
                write!(f, "{} cleanup callback(s) failed: {errors:?}", errors.len())
            }
            Self::Shutdown(error) => error.fmt(f),
        }
    }
}
impl std::error::Error for AppError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Runtime(error) => Some(error),
            Self::Cleanup(errors) => errors.first().map(|error| error as _),
            Self::Shutdown(error) => Some(error),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct App {
    sender: mpsc::UnboundedSender<Command>,
    sealed: Arc<AtomicBool>,
    context: Context,
}
impl App {
    pub fn new() -> Result<Self, AppError> {
        let handle = tokio::runtime::Handle::try_current().map_err(|_| AppError::NoExecutor)?;
        Ok(Self::with_handle(&handle))
    }
    pub fn with_handle(handle: &tokio::runtime::Handle) -> Self {
        let (sender, receiver) = mpsc::unbounded_channel();
        let sealed = Arc::new(AtomicBool::new(false));
        let mut driver = Driver {
            runtime: Runtime::new(),
            receiver,
            sealed: sealed.clone(),
            waiters: Vec::new(),
            cleanup_errors: Vec::new(),
            shutdown_waiters: Vec::new(),
            closing: false,
            shutting_down: false,
            finished: false,
            disconnected: false,
        };
        handle.spawn(async move { poll_fn(|cx| driver.poll(cx)).await });
        Self {
            sender,
            sealed,
            context: Context::new(),
        }
    }
    pub fn context(&self) -> &Context {
        &self.context
    }
    /// A view into the same application with a different default service realm.
    /// Shutdown and admission remain application-wide.
    pub fn scoped(&self, context: Context) -> Self {
        Self {
            context,
            ..self.clone()
        }
    }
    fn request<T: Send + 'static>(
        &self,
        admission: bool,
        command: impl FnOnce(Reply<T>) -> Command,
    ) -> impl Future<Output = Result<T, AppError>> + Send + 'static {
        let (reply, response) = oneshot::channel();
        if admission && self.sealed.load(Ordering::Acquire) {
            let _ = reply.send(Err(AppError::Closed));
        } else {
            // A failed send drops the reply, reported as DriverStopped below.
            let _ = self.sender.send(command(reply));
        }
        async move { response.await.unwrap_or(Err(AppError::DriverStopped)) }
    }
    /// Register a root plugin. Registration is not activation: call ready() on
    /// the returned handle when its service dependencies must be available.
    pub fn plugin(
        &self,
        plugin: Plugin,
    ) -> impl Future<Output = Result<PluginHandle, AppError>> + Send + 'static {
        self.plugin_in(self.context.clone(), plugin)
    }
    pub fn plugin_in(
        &self,
        context: Context,
        plugin: Plugin,
    ) -> impl Future<Output = Result<PluginHandle, AppError>> + Send + 'static {
        self.mount_in(context, None, plugin)
    }
    fn mount_in(
        &self,
        context: Context,
        parent: Option<PluginId>,
        plugin: Plugin,
    ) -> impl Future<Output = Result<PluginHandle, AppError>> + Send + 'static {
        let app = self.scoped(context.clone());
        let mounted = self.request(true, move |reply| Command::Mount {
            context,
            parent,
            plugin,
            reply,
        });
        async move {
            Ok(PluginHandle {
                id: mounted.await?,
                app,
            })
        }
    }
    /// An external snapshot, not a registered lifecycle dependency.
    pub fn get<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
    ) -> impl Future<Output = Result<Option<Arc<T>>, AppError>> + Send + 'static {
        self.get_in(self.context.clone(), key)
    }
    /// Read a snapshot in an explicit context; this does not acquire a lease.
    pub fn get_in<T: Any + Send + Sync>(
        &self,
        context: Context,
        key: ServiceKey<T>,
    ) -> impl Future<Output = Result<Option<Arc<T>>, AppError>> + Send + 'static {
        self.request(false, move |reply| {
            Command::Read(Box::new(move |runtime| {
                let _ = reply.send(Ok(runtime.get(&context, key)));
            }))
        })
    }
    pub fn snapshot(
        &self,
    ) -> impl Future<Output = Result<RuntimeSnapshot, AppError>> + Send + 'static {
        self.request(false, move |reply| {
            Command::Read(Box::new(move |runtime| {
                let _ = reply.send(Ok(runtime.snapshot()));
            }))
        })
    }
    /// Historical cleanup errors since the last shutdown report. Reading this
    /// snapshot does not consume errors or retry any callback.
    pub fn cleanup_errors(
        &self,
    ) -> impl Future<Output = Result<Vec<RuntimeError>, AppError>> + Send + 'static {
        self.request(false, Command::CleanupErrors)
    }
    /// Seal admission and drain all owned plugins. The driver continues if a
    /// waiter is dropped. A cleanup failure leaves the driver and retained
    /// resources available for handle.retry_cleanup(), then another shutdown().
    pub fn shutdown(&self) -> impl Future<Output = Result<(), AppError>> + Send + 'static {
        self.sealed.store(true, Ordering::Release);
        self.request(false, Command::Shutdown)
    }
}

#[derive(Clone, Debug)]
pub struct PluginHandle {
    id: PluginId,
    app: App,
}
impl PluginHandle {
    pub fn id(&self) -> PluginId {
        self.id
    }
    pub fn context(&self) -> &Context {
        self.app.context()
    }
    /// Inspect this plugin without driving callbacks. None means registry removal.
    pub fn snapshot(
        &self,
    ) -> impl Future<Output = Result<Option<PluginSnapshot>, AppError>> + Send + 'static {
        let id = self.id;
        self.app.request(false, move |reply| {
            Command::Read(Box::new(move |runtime| {
                let _ = reply.send(Ok(runtime
                    .snapshot()
                    .plugins
                    .into_iter()
                    .find(|plugin| plugin.id == id)));
            }))
        })
    }
    /// Register an owned child in this plugin's context. Ownership controls
    /// disposal; services are still governed by declared and inherited bindings.
    pub fn plugin(
        &self,
        plugin: Plugin,
    ) -> impl Future<Output = Result<PluginHandle, AppError>> + Send + 'static {
        self.app
            .mount_in(self.context().clone(), Some(self.id), plugin)
    }
    pub fn plugin_in(
        &self,
        context: Context,
        plugin: Plugin,
    ) -> impl Future<Output = Result<PluginHandle, AppError>> + Send + 'static {
        self.app.mount_in(context, Some(self.id), plugin)
    }
    fn request(
        &self,
        action: Action,
        mode: WaitMode,
        admission: bool,
    ) -> impl Future<Output = Result<(), AppError>> + Send + 'static {
        let id = self.id;
        self.app.request(admission, move |reply| Command::Owner {
            id,
            action,
            mode,
            reply,
        })
    }
    /// Current setup/restoration has settled. Missing dependencies may leave
    /// the plugin Inactive; use ready() to wait for Active.
    pub fn settled(&self) -> impl Future<Output = Result<(), AppError>> + Send + 'static {
        self.request(Action::None, WaitMode::Settled, false)
    }
    /// Wait for an Active, settled episode. This can wait indefinitely for a
    /// missing provider. Disposing the plugin ends the wait with Retired.
    pub fn ready(&self) -> impl Future<Output = Result<(), AppError>> + Send + 'static {
        self.request(Action::None, WaitMode::Ready, false)
    }
    /// Retire and wait until cleanup and registry removal complete. One-shot
    /// failures in this plugin are reported even when removal succeeds; retryable
    /// cleanup failures keep their resources and require explicit retry.
    /// Inspect App::cleanup_errors or shutdown for errors in other affected plugins.
    pub fn dispose(&self) -> impl Future<Output = Result<(), AppError>> + Send + 'static {
        self.request(Action::Dispose, WaitMode::Removed, false)
    }
    pub fn restart(&self) -> impl Future<Output = Result<(), AppError>> + Send + 'static {
        self.request(Action::Restart, WaitMode::Settled, true)
    }
    /// Replace synchronous setup, retaining declarations.
    pub fn update(
        &self,
        setup: impl FnMut(&mut Setup<'_>) -> CallbackResult + Send + 'static,
    ) -> impl Future<Output = Result<(), AppError>> + Send + 'static {
        self.request(Action::UpdateSync(Box::new(setup)), WaitMode::Settled, true)
    }
    /// Replace a complete recipe, including typed setup inputs. A declaration or
    /// injection-configuration change is rejected before disturbing the old plugin.
    pub fn update_plugin(
        &self,
        plugin: Plugin,
    ) -> impl Future<Output = Result<(), AppError>> + Send + 'static {
        self.request(Action::UpdatePlugin(plugin), WaitMode::Settled, true)
    }
    /// Replace setup with the same declared ports and dependencies.
    pub fn update_async<F, Fut>(
        &self,
        mut setup: F,
    ) -> impl Future<Output = Result<(), AppError>> + Send + 'static
    where
        F: FnMut(AsyncSetup) -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.request(
            Action::Update(Box::new(move |ctx| Box::pin(setup(ctx)))),
            WaitMode::Settled,
            true,
        )
    }
    pub fn retry_cleanup(&self) -> impl Future<Output = Result<(), AppError>> + Send + 'static {
        self.request(Action::Retry, WaitMode::Settled, false)
    }
}

enum Command {
    Mount {
        context: Context,
        parent: Option<PluginId>,
        plugin: Plugin,
        reply: Reply<PluginId>,
    },
    Owner {
        id: PluginId,
        action: Action,
        mode: WaitMode,
        reply: Reply<()>,
    },
    Read(Box<dyn FnOnce(&Runtime) + Send>),
    Shutdown(Reply<()>),
    CleanupErrors(Reply<Vec<RuntimeError>>),
}
enum Action {
    None,
    Dispose,
    Restart,
    Retry,
    Update(AsyncCallback),
    UpdateSync(SyncCallback),
    UpdatePlugin(Plugin),
}
#[derive(Clone, Copy)]
enum WaitMode {
    Settled,
    Ready,
    Removed,
}
struct Waiter {
    cleanup_errors: Vec<RuntimeError>,
    id: PluginId,
    mode: WaitMode,
    reply: Reply<()>,
}
struct Driver {
    runtime: Runtime,
    receiver: mpsc::UnboundedReceiver<Command>,
    sealed: Arc<AtomicBool>,
    waiters: Vec<Waiter>,
    cleanup_errors: Vec<RuntimeError>,
    shutdown_waiters: Vec<Reply<()>>,
    closing: bool,
    shutting_down: bool,
    finished: bool,
    disconnected: bool,
}
impl Driver {
    fn command(&mut self, command: Command) {
        match command {
            Command::Mount {
                context,
                parent,
                plugin,
                reply,
            } => {
                let result = if self.closing {
                    Err(AppError::Closed)
                } else {
                    self.runtime
                        .mount(&context, parent, plugin)
                        .map_err(AppError::Runtime)
                };
                let _ = reply.send(result);
            }
            Command::Read(read) => read(&self.runtime),
            Command::CleanupErrors(reply) => {
                let _ = reply.send(Ok(self.cleanup_errors.clone()));
            }
            Command::Shutdown(reply) => {
                if self.finished {
                    let _ = reply.send(Ok(()));
                } else {
                    self.closing = true;
                    self.shutting_down = true;
                    self.shutdown_waiters.push(reply);
                }
            }
            Command::Owner {
                id,
                action,
                mode,
                reply,
            } => {
                let result = match action {
                    Action::None => Ok(()),
                    Action::Dispose => self.runtime.dispose(id).map_err(AppError::Runtime),
                    Action::Retry => self.runtime.retry_cleanup(id).map_err(AppError::Runtime),
                    Action::Restart
                    | Action::Update(_)
                    | Action::UpdateSync(_)
                    | Action::UpdatePlugin(_)
                        if self.closing =>
                    {
                        Err(AppError::Closed)
                    }
                    Action::Restart => self.runtime.restart(id).map_err(AppError::Runtime),
                    Action::UpdateSync(setup) => {
                        self.runtime.update(id, setup).map_err(AppError::Runtime)
                    }
                    Action::UpdatePlugin(plugin) => self
                        .runtime
                        .update_plugin(id, plugin)
                        .map_err(AppError::Runtime),
                    Action::Update(setup) => self
                        .runtime
                        .update_async(id, setup)
                        .map_err(AppError::Runtime),
                };
                match result {
                    Ok(()) => self.waiters.push(Waiter {
                        id,
                        mode,
                        reply,
                        cleanup_errors: Vec::new(),
                    }),
                    Err(error) => {
                        let _ = reply.send(Err(error));
                    }
                }
            }
        }
    }
    fn blocking_cleanup_error(&self, id: PluginId) -> Option<RuntimeError> {
        let snapshot = self.runtime.snapshot();
        let mut pending = vec![id];
        let mut visited = std::collections::BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            if let Some(error) = self.runtime.cleanup_error(id) {
                return Some(RuntimeError::Cleanup {
                    plugin: id,
                    error: error.clone(),
                });
            }
            if let Some(plugin) = snapshot.plugins.iter().find(|plugin| plugin.id == id) {
                for blocker in &plugin.blockers {
                    match blocker {
                        Blocker::CommittedConsumers(ids) | Blocker::RetiringChildren(ids) => {
                            pending.extend(ids)
                        }
                        _ => (),
                    }
                }
            }
        }
        None
    }
    fn poll(&mut self, cx: &mut TaskContext<'_>) -> Poll<()> {
        // Bound command processing so a producer cannot starve lifecycle polls.
        for n in 0..64 {
            match self.receiver.poll_recv(cx) {
                Poll::Ready(Some(command)) => self.command(command),
                Poll::Ready(None) => {
                    self.disconnected = true;
                    if !self.closing {
                        self.closing = true;
                        self.shutting_down = true;
                        self.sealed.store(true, Ordering::Release);
                    }
                    break;
                }
                Poll::Pending => break,
            }
            if n == 63 {
                cx.waker().wake_by_ref();
            }
        }
        let (driven, mut shutdown) = if self.shutting_down {
            match Box::pin(self.runtime.shutdown()).as_mut().poll(cx) {
                Poll::Ready(result) => (
                    Poll::Ready(result.as_ref().map(|_| ()).map_err(|error| {
                        error
                            .lifecycle
                            .clone()
                            .or_else(|| error.cleanup.first().cloned())
                            .or_else(|| error.setup.first().cloned())
                            .unwrap_or(RuntimeError::Stalled)
                    })),
                    Some(result),
                ),
                Poll::Pending => (Poll::Pending, None),
            }
        } else if self.finished {
            (Poll::Ready(Ok(())), None)
        } else {
            (self.runtime.poll_settle(cx), None)
        };
        // Runtime drains one-shot failures without making them blockers. Keep
        // their receipts even across polls, dropped waiters and a pending shutdown.
        let mut cleanup = self.runtime.take_cleanup_errors();
        if let Some(Err(error)) = &mut shutdown {
            cleanup.append(&mut error.cleanup);
        }
        for waiter in &mut self.waiters {
            waiter.cleanup_errors.extend(cleanup.iter().filter(|error| {
                matches!(error, RuntimeError::Cleanup { plugin, .. } if *plugin == waiter.id)
            }).cloned());
        }
        self.cleanup_errors.extend(cleanup);
        let mut index = 0;
        while index < self.waiters.len() {
            let waiter = &self.waiters[index];
            if waiter.reply.is_closed() {
                self.waiters.swap_remove(index);
                continue;
            }
            let local = match waiter.mode {
                WaitMode::Settled => self.runtime.settled_result(waiter.id),
                WaitMode::Ready
                    if self.runtime.retired(waiter.id) || !self.runtime.contains(waiter.id) =>
                {
                    Some(Err(RuntimeError::Retired(waiter.id)))
                }
                WaitMode::Ready => match self.runtime.settled_result(waiter.id) {
                    Some(Err(error)) => Some(Err(error)),
                    result if self.runtime.phase(waiter.id) == Some(Phase::Active) => result,
                    _ => None,
                },
                WaitMode::Removed if !self.runtime.contains(waiter.id) => Some(Ok(())),
                WaitMode::Removed => None,
            };
            let result = local.or_else(|| match &driven {
                Poll::Ready(Err(RuntimeError::Cleanup { .. })) => {
                    self.blocking_cleanup_error(waiter.id).map(Err)
                }
                Poll::Ready(Err(error @ RuntimeError::Kernel(_)))
                | Poll::Ready(Err(error @ RuntimeError::Stalled)) => Some(Err(error.clone())),
                // Another plugin's setup failure must not fail a waiting handle.
                _ => None,
            });
            if let Some(result) = result {
                let waiter = self.waiters.swap_remove(index);
                let result = match result {
                    Err(error) => Err(AppError::Runtime(error)),
                    Ok(()) if !waiter.cleanup_errors.is_empty() => {
                        Err(AppError::Cleanup(waiter.cleanup_errors))
                    }
                    Ok(()) => Ok(()),
                };
                let _ = waiter.reply.send(result);
            } else {
                index += 1;
            }
        }
        if let Some(result) = shutdown {
            let cleanup = std::mem::take(&mut self.cleanup_errors);
            let result = match result {
                Ok(()) if cleanup.is_empty() => Ok(()),
                Ok(()) => Err(ShutdownError {
                    lifecycle: None,
                    setup: Vec::new(),
                    cleanup,
                }),
                Err(mut error) => {
                    error.cleanup = cleanup;
                    Err(error)
                }
            };
            self.shutting_down = false;
            self.finished = result.is_ok();
            for reply in self.shutdown_waiters.drain(..) {
                let _ = reply.send(result.clone().map_err(AppError::Shutdown));
            }
        }
        if self.disconnected && !self.shutting_down {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}
