//! External Child allocation reports, retirement requests and removal observations.
//! Allocation is decided once under this control's lock. These host reports do
//! not replace the embedding graph's checked registration or cleanup authority.
use super::*;

struct StaticChildProgress {
    owner: PluginId,
    generation: u64,
    allocation: Option<Result<PluginId, String>>,
    retiring: bool,
    removed: bool,
    cleanup_error: Option<String>,
    service: Option<EffectHandle>,
    notify: Option<Arc<dyn Fn() + Send + Sync>>,
    cleanup_waiter: Option<Waker>,
}
impl StaticChildProgress {
    fn id(&self) -> Option<PluginId> {
        self.allocation.as_ref()?.as_ref().ok().copied()
    }
}
/// Exact-episode acknowledgement for an externally allocated child. These are
/// host authority operations, not evidence that arbitrary callbacks are proved.
/// IDs must come from the embedding graph; `removed` requires its Removed
/// observation and must never be substituted with a retirement request.
#[derive(Clone)]
pub struct StaticChildControl(Arc<Mutex<StaticChildProgress>>);
impl StaticChildControl {
    pub(super) fn new(
        owner: PluginId,
        generation: u64,
        service: Option<EffectHandle>,
        notify: Arc<dyn Fn() + Send + Sync>,
    ) -> Self {
        Self(Arc::new(Mutex::new(StaticChildProgress {
            owner,
            generation,
            allocation: None,
            retiring: false,
            removed: false,
            cleanup_error: None,
            service,
            notify: Some(notify),
            cleanup_waiter: None,
        })))
    }
    pub fn owner(&self) -> PluginId {
        lock(&self.0).owner
    }
    pub fn generation(&self) -> u64 {
        lock(&self.0).generation
    }
    pub fn id(&self) -> Option<PluginId> {
        lock(&self.0).id()
    }
    pub(super) fn error(&self) -> Option<String> {
        lock(&self.0).allocation.as_ref()?.as_ref().err().cloned()
    }
    pub fn retirement_requested(&self) -> bool {
        let state = lock(&self.0);
        state.retiring
            || state
                .service
                .as_ref()
                .is_some_and(|service| service.cancelled())
    }
    pub fn is_removed(&self) -> bool {
        lock(&self.0).removed
    }
    /// A rejected dynamic publication reports through its ServiceHandle; a
    /// rejected ordinary child request is a setup error of its owner.
    pub fn is_publication(&self) -> bool {
        lock(&self.0).service.is_some()
    }
    /// Resolve allocation exactly once. `Err` is only a pre-allocation rejection:
    /// once a graph node exists, acknowledge its ID and retire/remove it normally.
    /// An allocation that races cancellation
    /// still receives its real ID and must then be retired; it is not discarded.
    pub fn complete_mount(&self, result: Result<PluginId, String>) -> Result<(), String> {
        let assigned_id = result.as_ref().ok().copied();
        let (wake, service, error, notify) = {
            let mut state = lock(&self.0);
            if state.allocation.is_some() {
                return Err("StaticChildAlreadyAssigned".into());
            }
            let error = result.as_ref().err().cloned();
            if error.is_some() {
                state.removed = true;
            }
            state.allocation = Some(result);
            let notify = if error.is_some() {
                state.notify.take()
            } else {
                None
            };
            (
                state.cleanup_waiter.take(),
                state.service.clone(),
                error,
                notify,
            )
        };
        drop(notify);
        if let Some(service) = service {
            if let Some(id) = assigned_id {
                service.assign_service_child(id);
            }
            if let Some(error) = error {
                if error != CANCELLED {
                    service.record_error(error.into());
                }
                service.finish_service();
            }
        }
        if let Some(wake) = wake {
            wake.wake();
        }
        Ok(())
    }
    /// Mark a service child initialized only after native setup activation.
    pub fn mark_initialized(&self) -> Result<(), String> {
        let service = {
            let state = lock(&self.0);
            if state.id().is_none() || state.removed {
                return Err("StaticChildNotMounted".into());
            }
            state.service.clone()
        };
        if let Some(service) = service {
            service.initialize_service(true);
        }
        Ok(())
    }
    pub fn request_retirement(&self) {
        let (notify, service) = {
            let mut state = lock(&self.0);
            if state.removed || state.retiring {
                return;
            }
            state.retiring = true;
            (state.notify.clone(), state.service.clone())
        };
        if let Some(service) = service {
            service.cancel();
        }
        if let Some(notify) = notify {
            notify();
        }
    }
    /// Record setup/application failure for service status and eventual join.
    /// This alone does not say that child cleanup failed or removal occurred.
    pub fn record_error(&self, error: String) {
        let service = {
            let state = lock(&self.0);
            if state.removed {
                return;
            }
            state.service.clone()
        };
        if let Some(service) = service {
            service.record_unique_error(error);
        }
    }
    /// A failed child inverse blocks owner restoration and keeps the node's
    /// resources/lease alive. Legacy FnOnce cleanup failures remain sticky.
    /// A service join reports the failure while `finished()` remains false:
    /// failure is not an acknowledgement of restoration.
    pub fn cleanup_failed(&self, error: String) {
        let wake = {
            let mut state = lock(&self.0);
            if state.removed {
                return;
            }
            state.retiring = true;
            state.cleanup_error.get_or_insert_with(|| error.clone());
            state.cleanup_waiter.take()
        };
        self.record_error(error.clone());
        let service = lock(&self.0).service.clone();
        if let Some(service) = service {
            service.fail_service_cleanup(error.into());
        }
        if let Some(wake) = wake {
            wake.wake();
        }
    }
    /// Acknowledge actual registry removal. A previously failed inverse cannot
    /// be turned into success by calling this method.
    pub fn removed(&self) -> Result<(), String> {
        let (wake, notify, service) = {
            let mut state = lock(&self.0);
            if let Some(error) = &state.cleanup_error {
                return Err(error.clone());
            }
            if state.id().is_none() {
                return Err("StaticChildNotMounted".into());
            }
            state.removed = true;
            (
                state.cleanup_waiter.take(),
                state.notify.take(),
                state.service.clone(),
            )
        };
        drop(notify);
        if let Some(service) = service {
            service.finish_service();
        }
        if let Some(wake) = wake {
            wake.wake();
        }
        Ok(())
    }
    pub(in super::super) fn poll_retired(&self, cx: &mut TaskContext<'_>) -> Poll<CallbackResult> {
        let wake = cx.waker().clone();
        let (result, previous) = {
            let mut state = lock(&self.0);
            if let Some(error) = &state.cleanup_error {
                return Poll::Ready(Err(error.clone().into()));
            }
            if state.removed {
                return Poll::Ready(Ok(()));
            }
            (Poll::Pending, state.cleanup_waiter.replace(wake))
        };
        drop(previous);
        result
    }
}
