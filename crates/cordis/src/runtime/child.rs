//! Child admission and the original handle/request/inverse ownership.
//! Native identities remain owned by the verified SharedChild. External child
//! reports use one ordinary-host control, never a second native identity store.
use super::*;
mod external;
pub use external::StaticChildControl;

#[derive(Clone)]
enum ChildState {
    Native {
        slot: SharedChild,
        error: Arc<Mutex<Option<String>>>,
    },
    External(StaticChildControl),
}

/// A child request becomes an ID after the current callback's poll returns.
#[derive(Clone)]
pub struct ChildHandle(ChildState);
impl ChildHandle {
    pub fn id(&self) -> Option<PluginId> {
        match &self.0 {
            ChildState::Native { slot, .. } => slot.snapshot().identity().map(|child| child.id()),
            ChildState::External(control) => control.id(),
        }
    }
    pub fn error(&self) -> Option<String> {
        match &self.0 {
            ChildState::Native { error, .. } => lock(error).clone(),
            ChildState::External(control) => control.error(),
        }
    }
}

pub(super) type ChildRequest = ChildDispatch<NativeChildInput, ExternalChildRequest>;
pub(super) struct NativeChildInput {
    context: Context,
    plugin: Plugin,
    service: Option<EffectHandle>,
    error: Arc<Mutex<Option<String>>>,
}
pub(super) struct ExternalChildRequest {
    context: Context,
    plugin: Plugin,
    control: StaticChildControl,
}
impl ExternalChildRequest {
    // The external host takes the complete original request exactly once. Only
    // mount_request constructs it, together with its handle and cleanup inverse.
    pub(super) fn into_parts(self) -> (Context, Plugin, StaticChildControl) {
        (self.context, self.plugin, self.control)
    }
}

/// Retain accepted external controls until rejection/removal or episode sealing.
/// Insertion stays with admission; snapshots do not confer graph authority.
#[derive(Default)]
pub(super) struct ExternalChildren(Vec<StaticChildControl>);
impl ExternalChildren {
    fn insert(&mut self, control: StaticChildControl) {
        self.0.push(control);
    }
    pub(super) fn snapshot(&self) -> Vec<StaticChildControl> {
        self.0.clone()
    }
    pub(super) fn prune_removed(&mut self) {
        self.0.retain(|child| !child.is_removed());
    }
}

impl AsyncSetup {
    pub fn mount(&self, plugin: Plugin) -> Result<ChildHandle, CallbackError> {
        self.mount_in(self.state.context(), plugin)
    }
    pub fn mount_in(
        &self,
        context: &Context,
        plugin: Plugin,
    ) -> Result<ChildHandle, CallbackError> {
        self.mount_request(context, plugin, None)
    }
    pub(super) fn mount_request(
        &self,
        context: &Context,
        plugin: Plugin,
        service: Option<EffectHandle>,
    ) -> Result<ChildHandle, CallbackError> {
        self.require_dynamic(Feature::Mount)?;
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        if state.phase() == EpisodePhase::Restoring
            || !state.execution.accepts_acquisition(self.scope.group())
        {
            return Err(CANCELLED.into());
        }
        if !state.execution.contains(self.scope.group()) {
            return Err("effect group has completed".into());
        }
        let handle = if state.execution.lifecycle_ticket().is_some() {
            let error = Arc::new(Mutex::new(None));
            let request = NativeChildInput {
                context: context.clone(),
                plugin,
                service,
                error: error.clone(),
            };
            match state
                .execution
                .enqueue_native_child(self.scope.group(), request)
            {
                Ok((slot, _token)) => ChildHandle(ChildState::Native { slot, error }),
                Err(rejected) => {
                    drop(state);
                    drop(rejected);
                    return Err("child request admission is closed or exhausted".into());
                }
            }
        } else {
            // Dynamic capability and live-admission checks above establish that
            // an external request has a host. One control is shared by the
            // returned handle, request, inverse and retained-child registry.
            let control = StaticChildControl::new(
                self.state.services().owner(),
                self.state.generation(),
                service,
                state.child_host().expect("dynamic child host"),
            );
            let handle = ChildHandle(ChildState::External(control.clone()));
            let request = ChildDispatch::External(ExternalChildRequest {
                context: context.clone(),
                plugin,
                control: control.clone(),
            });
            if let Err(rejected) = state.execution.enqueue_owned_child(
                self.scope.group(),
                request,
                CleanupAction::External(control),
            ) {
                drop(state);
                drop(rejected);
                return Err("child request admission is closed or exhausted".into());
            }
            handle
        };
        if let ChildState::External(control) = &handle.0 {
            state.external_children.insert(control.clone());
        }
        let notification = state.child_notification();
        drop(state);
        notification.wake();
        Ok(handle)
    }
}

impl Runtime {
    pub(super) fn apply_child_request(&mut self, id: PluginId, request: ChildRequest) {
        let ChildDispatch::Native(request) = request else {
            self.latch(id, "ExternalChildInNativeRuntime".into());
            return;
        };
        let (request, child_slot) = request.into_parts();
        if request
            .service
            .as_ref()
            .is_some_and(|service| service.cancelled())
        {
            if let Some(service) = &request.service {
                service.finish_service();
            }
            return;
        }
        let result = self.mount_inner(
            &request.context,
            Some(id),
            request.plugin,
            false,
            Some(&child_slot),
        );
        match result {
            Ok((child, _)) => {
                self.kernel.host_mut(child).unwrap().service = request.service;
            }
            Err(error) => {
                let message = CallbackError::new(error);
                {
                    let mut error = lock(&request.error);
                    if child_slot.reject().result {
                        *error = Some(message.to_string());
                    }
                }
                if let Some(service) = &request.service {
                    service.record_error(message);
                    service.finish_service();
                } else {
                    self.latch(id, message);
                }
            }
        }
    }
}
