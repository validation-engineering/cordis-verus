//! Effect/service observations and their ordinary host wait registrations.
//! Semantic state remains owned by HostStatus and the actual Execution.
use super::*;
use cordis_kernel::effect_work::EffectRun;
use std::sync::Weak;

#[derive(Default)]
struct EffectStatus {
    // None exists only while enqueueing under the Episode mutex; no handle
    // escapes until the checked owner is bound to the actual allocated group.
    checked: Option<cordis_kernel::host_status::HostStatus<CallbackError>>,
    // Weak identity pins the allocation without retaining the Episode payload
    // or creating Episode -> group -> handle -> Episode ownership cycles.
    episode: Weak<SharedEpisode>,
    next_waiter: u64,
    wakers: BTreeMap<u64, Waker>,
    driver: Option<Waker>,
    notify: Option<Arc<dyn Fn() + Send + Sync>>,
}
impl EffectStatus {
    fn belongs_to(&self, episode: &Arc<SharedEpisode>) -> bool {
        self.episode.ptr_eq(&Arc::downgrade(episode))
    }
    fn checked(&self) -> &cordis_kernel::host_status::HostStatus<CallbackError> {
        self.checked
            .as_ref()
            .expect("status bound before handle escapes")
    }
    fn checked_mut(&mut self) -> &mut cordis_kernel::host_status::HostStatus<CallbackError> {
        self.checked
            .as_mut()
            .expect("status bound before handle escapes")
    }
    fn notification(&mut self) -> Notification {
        Notification::new(self.driver.take(), self.notify.clone())
    }
}

fn wake_waiters(wakers: BTreeMap<u64, Waker>) {
    for waker in wakers.into_values() {
        waker.wake();
    }
}
/// A cancellation/join handle for one owner-bound effect group. Cancellation is
/// idempotent; join completes after the in-flight stage and every inverse land.
#[derive(Clone)]
pub struct EffectHandle {
    status: Arc<Mutex<EffectStatus>>,
}

// Pending work or retained cleanup is a normal outcome, not an adapter error.
// Return the same checkout without boxing it or dropping its actual payload.
pub(super) enum Retirement {
    Finished(GroupState),
    Retained(EffectRun<GroupState>),
}

impl EffectHandle {
    pub fn cancel(&self) {
        let notification = {
            let mut status = lock(&self.status);
            status.checked_mut().cancel();
            status.notification()
        };
        notification.wake();
    }
    pub fn dispose(&self) {
        self.cancel();
    }
    pub fn initialized(&self) -> bool {
        lock(&self.status).checked().observe().initialized()
    }
    pub fn finished(&self) -> bool {
        lock(&self.status).checked().observe().finished()
    }
    pub fn errors(&self) -> Vec<CallbackError> {
        lock(&self.status).checked().errors().clone()
    }
    /// A certified observation of the actual status in its execution domain.
    /// Wakers and OS scheduling are outside this trajectory.
    pub fn execution_snapshot(&self) -> cordis_kernel::reversible_value::joint::Snapshot {
        lock(&self.status).checked().execution_snapshot()
    }
    pub fn join(&self) -> EffectJoin {
        EffectJoin {
            handle: self.clone(),
            waiter: None,
        }
    }

    pub(super) fn service(episode: &Arc<SharedEpisode>) -> Self {
        let state = lock(episode);
        Self {
            status: Arc::new(Mutex::new(EffectStatus {
                checked: Some(state.execution.service_status()),
                episode: Arc::downgrade(episode),
                notify: state.child_host(),
                ..EffectStatus::default()
            })),
        }
    }

    pub(super) fn cancelled(&self) -> bool {
        lock(&self.status).checked().observe().cancelled()
    }

    // The driver is already applying retirement; preserve its no-notify path.
    pub(super) fn mark_cancelled(&self) {
        lock(&self.status).checked_mut().cancel();
    }

    pub(super) fn poll_driver(&self, cx: &TaskContext<'_>, cancel: bool) -> bool {
        // Clone and drop custom wakers outside the status lock.
        let driver = cx.waker().clone();
        let (cancelled, previous) = {
            let mut status = lock(&self.status);
            let previous = status.driver.replace(driver);
            if cancel {
                status.checked_mut().cancel();
            }
            (status.checked().observe().cancelled(), previous)
        };
        drop(previous);
        cancelled
    }

    pub(super) fn record_error(&self, error: CallbackError) {
        lock(&self.status).checked_mut().push_error(error);
    }

    pub(super) fn record_unique_error(&self, error: String) {
        let mut status = lock(&self.status);
        if !status
            .checked()
            .errors()
            .iter()
            .any(|existing| existing.message() == error)
        {
            status.checked_mut().push_error(error.into());
        }
    }

    pub(super) fn assign_service_child(&self, id: PluginId) {
        let waiters = {
            let mut status = lock(&self.status);
            assert!(
                status.checked_mut().assign_child(id),
                "one service child assignment"
            );
            std::mem::take(&mut status.wakers)
        };
        // Recheck a pending join's newly allocated external wait edge.
        wake_waiters(waiters);
    }

    pub(super) fn initialize_service(&self, wake_joiners: bool) {
        let waiters = {
            let mut status = lock(&self.status);
            assert!(status.checked_mut().report_service_initialized());
            // Static hosts wake on initialization; native joins keep waiting
            // until removal. Retain these existing notification policies.
            if wake_joiners {
                std::mem::take(&mut status.wakers)
            } else {
                BTreeMap::new()
            }
        };
        wake_waiters(waiters);
    }

    pub(super) fn fail_service_cleanup(&self, error: CallbackError) {
        let (waiters, unused) = {
            let mut status = lock(&self.status);
            let unused = status.checked_mut().report_terminal(error);
            (std::mem::take(&mut status.wakers), unused)
        };
        drop(unused);
        wake_waiters(waiters);
    }

    pub(super) fn finish_service(&self) {
        let (waiters, driver, notify) = {
            let mut status = lock(&self.status);
            assert!(
                status.checked_mut().report_service_finished(),
                "service completion report"
            );
            (
                std::mem::take(&mut status.wakers),
                status.driver.take(),
                status.notify.take(),
            )
        };
        drop(driver);
        drop(notify);
        wake_waiters(waiters);
    }

    pub(super) fn replace_service_value(&self, slot: &ServiceSlot, value: Value) -> CallbackResult {
        let mut status = lock(&self.status);
        if status.checked().observe().cancelled() || status.checked().observe().finished() {
            return Err(CANCELLED.into());
        }
        let previous = match slot.replace(value) {
            Ok(previous) => previous,
            Err(rejected) => {
                drop(status);
                drop(rejected.value);
                return Err(rejected.message.into());
            }
        };
        let notification = status.notification();
        drop(status);
        drop(previous);
        notification.wake();
        Ok(())
    }

    pub(super) fn refresh_driver(&self) {
        let notification = lock(&self.status).notification();
        notification.wake();
    }

    pub(super) fn matches_episode(&self, episode: &Arc<SharedEpisode>) -> bool {
        let state = lock(episode);
        let status = lock(&self.status);
        status.belongs_to(episode) && status.checked().matches_episode(&state.execution)
    }

    pub(super) fn initialize_effect(&self, episode: &Arc<SharedEpisode>, group: usize) {
        let waiters = {
            // Episode -> status -> checked cell -> Journal. Never acquire
            // Episode while holding status; invoke wakers after both unlock.
            let state = lock(episode);
            let mut status = lock(&self.status);
            if status.belongs_to(episode)
                && !status.checked().observe().initialized()
                && state.execution.initialize_effect_status(group).is_some()
            {
                std::mem::take(&mut status.wakers)
            } else {
                BTreeMap::new()
            }
        };
        wake_waiters(waiters);
    }

    pub(super) fn retire_effect(
        episode: &Arc<SharedEpisode>,
        group: EffectRun<GroupState>,
    ) -> Retirement {
        let handle = group.get().handle.clone();
        let retired = {
            let mut state = lock(episode);
            let status = lock(&handle.status);
            if status.belongs_to(episode) {
                state.execution.retire_observed_effect(group)
            } else {
                Err(group)
            }
        };
        match retired {
            Ok((payload, _observation)) => {
                let waiters = {
                    let mut status = lock(&payload.handle.status);
                    std::mem::take(&mut status.wakers)
                };
                wake_waiters(waiters);
                // Return the actual payload for destruction after the locks.
                Retirement::Finished(payload)
            }
            Err(retained) => Retirement::Retained(retained),
        }
    }
}
/// Wait for an effect's stage and inverses to finish. Dropping this wait removes
/// its waker registration; it does not cancel the effect itself.
#[must_use = "poll or await join to wait for effect cleanup"]
pub struct EffectJoin {
    handle: EffectHandle,
    waiter: Option<u64>,
}
impl Future for EffectJoin {
    type Output = CallbackResult;
    fn poll(self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();
        // A custom waker can reenter an effect handle from clone or Drop too.
        let mut waker = Some(cx.waker().clone());
        let (result, previous) = {
            let mut status = lock(&this.handle.status);
            if status.checked().observe().finished() || status.checked().terminal_error().is_some()
            {
                let result = if status.checked().errors().is_empty() {
                    Ok(())
                } else {
                    Err(CallbackError::multiple(status.checked().errors().clone()))
                };
                let previous = this.waiter.take().and_then(|id| status.wakers.remove(&id));
                (Poll::Ready(result), previous)
            } else if status
                .checked()
                .external_child_id()
                .is_some_and(static_host::child_join_blocked)
            {
                // A pending join cannot retain a provider whose removal it
                // awaits. This rejects only this wait, not the child's cleanup.
                let previous = this.waiter.take().and_then(|id| status.wakers.remove(&id));
                (Poll::Ready(Err("ReentrantServiceJoin".into())), previous)
            } else {
                let id = *this.waiter.get_or_insert_with(|| {
                    let id = status.next_waiter;
                    status.next_waiter =
                        id.checked_add(1).expect("effect join identities exhausted");
                    id
                });
                (
                    Poll::Pending,
                    status.wakers.insert(id, waker.take().unwrap()),
                )
            }
        };
        drop(previous);
        result
    }
}
impl Drop for EffectJoin {
    fn drop(&mut self) {
        let previous = self
            .waiter
            .take()
            .and_then(|id| lock(&self.handle.status).wakers.remove(&id));
        drop(previous);
    }
}

impl AsyncSetup {
    pub fn effect(&self, effect: impl EffectIterator) -> Result<EffectHandle, CallbackError> {
        self.require_dynamic(Feature::Effect)?;
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
        let handle = EffectHandle {
            status: Arc::new(Mutex::new(EffectStatus {
                episode: Arc::downgrade(&self.state),
                ..EffectStatus::default()
            })),
        };
        let payload = GroupState {
            iterator: Some(Box::new(effect)),
            running: None,
            handle: handle.clone(),
        };
        let domain = fresh(&NEXT_CLEANUP);
        let admitted = match self.state.services() {
            SetupServices::Native(_) => {
                state
                    .execution
                    .enqueue_native_effect(self.scope.group(), domain, payload)
            }
            SetupServices::External(context) => state
                .execution
                .enqueue_effect(
                    self.scope.group(),
                    domain,
                    context.committed().to_vec(),
                    payload,
                )
                .map_err(|(_, payload)| payload),
        };
        let group = match admitted {
            Ok(group) => group,
            Err(rejected) => {
                drop(state);
                drop(rejected);
                return Err("effect request admission is closed or exhausted".into());
            }
        };
        lock(&handle.status).checked = Some(
            state
                .execution
                .effect_status(group)
                .expect("native effect admission allocated its real cleanup group"),
        );
        let waker = state.take_driver();
        drop(state);
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(handle)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mounted_effect() -> (Runtime, PluginId, AsyncSetup, EffectHandle) {
        let mut runtime = Runtime::new();
        let escaped = Arc::new(Mutex::new(None));
        let out = escaped.clone();
        let id = runtime
            .mount(
                &Context::new(),
                None,
                Plugin::new("binding", move |setup| {
                    let context = setup.to_async();
                    let handle = context.effect(Effect::new())?;
                    *lock(&out) = Some((context, handle));
                    Ok(())
                }),
            )
            .unwrap();
        assert_eq!(
            Pin::new(&mut runtime.settle()).poll(&mut TaskContext::from_waker(Waker::noop())),
            Poll::Ready(Ok(()))
        );
        let (context, handle) = lock(&escaped).take().unwrap();
        (runtime, id, context, handle)
    }
    #[test]
    fn polling_a_crosswired_handle_retains_its_group_without_touching_the_foreign_owner() {
        let (mut runtime, id, context, own) = mounted_effect();
        let (_other, _other_id, foreign_context, foreign) = mounted_effect();
        let group_id = *lock(&context.state)
            .execution
            .effects()
            .keys()
            .next()
            .unwrap();
        let mut run = lock(&context.state)
            .execution
            .take_effect(group_id)
            .unwrap();
        run.get_mut().handle = foreign.clone();
        assert!(lock(&context.state).execution.put_effect(run).is_ok());
        let _ = runtime.poll_groups(id, true, true, &mut TaskContext::from_waker(Waker::noop()));
        assert!(!lock(&foreign.status).checked().observe().cancelled());
        assert!(!foreign.finished());
        assert!(lock(&context.state).execution.contains(group_id));
        assert_eq!(
            runtime.failure(id),
            Some("effect handle belongs to another episode")
        );
        // Also corrupt only the shared allocation: numeric provenance remains
        // the owner's exact Begin, so the Weak check is independently necessary.
        let mut run = lock(&context.state)
            .execution
            .take_effect(group_id)
            .unwrap();
        run.get_mut().handle = own.clone();
        assert!(lock(&context.state).execution.put_effect(run).is_ok());
        lock(&own.status).episode = Arc::downgrade(&foreign_context.state);
        let _ = runtime.poll_groups(id, true, true, &mut TaskContext::from_waker(Waker::noop()));
        assert!(!lock(&own.status).checked().observe().cancelled());
        assert!(!own.finished());
        lock(&own.status).episode = Arc::downgrade(&context.state);
        runtime.dispose(id).unwrap();
        let _ = Pin::new(&mut runtime.settle()).poll(&mut TaskContext::from_waker(Waker::noop()));
        assert!(own.finished());
        assert!(!foreign.finished());
    }
    #[test]
    fn escaped_handle_does_not_keep_episode_payload_alive_or_bind_a_new_allocation() {
        let (mut runtime, id, context, handle) = mounted_effect();
        let episode = Arc::downgrade(&context.state);
        assert!(lock(&handle.status).belongs_to(&context.clone().state));
        runtime.dispose(id).unwrap();
        assert_eq!(
            Pin::new(&mut runtime.settle()).poll(&mut TaskContext::from_waker(Waker::noop())),
            Poll::Ready(Ok(()))
        );
        drop(context);
        drop(runtime);
        assert!(episode.upgrade().is_none());
        let (_next, _, new_context, _) = mounted_effect();
        assert!(!lock(&handle.status).belongs_to(&new_context.state));
        assert!(handle.finished());
    }
    #[test]
    fn foreign_setup_scope_is_rejected_before_resource_registration() {
        let (_runtime, _, own, _) = mounted_effect();
        let (_foreign, _, foreign, _) = mounted_effect();
        assert_eq!(own.scope.group(), foreign.scope.group());
        let forged = AsyncSetup {
            state: own.state.clone(),
            scope: foreign.scope,
        };
        assert!(forged.ensure_active().is_err());
        assert!(forged.is_cancelled());
        assert!(forged
            .on_cleanup(|| panic!("must not be registered"))
            .is_err());
        assert!(forged.effect(Effect::new()).is_err());
        assert!(own.ensure_active().is_ok());
    }
    #[test]
    fn nested_and_escaped_setup_share_context_and_execution_allocation() {
        let (mut runtime, id, root, _) = mounted_effect();
        let nested = Arc::new(Mutex::new(None));
        let output = nested.clone();
        root.effect(Effect::new().step(move |setup| {
            *lock(&output) = Some(setup.clone());
            async { Ok(Inverse::empty()) }
        }))
        .unwrap();
        assert_eq!(
            Pin::new(&mut runtime.settle()).poll(&mut TaskContext::from_waker(Waker::noop())),
            Poll::Ready(Ok(()))
        );
        let child = lock(&nested).take().unwrap();
        assert_ne!(child.scope.group(), root.scope.group());
        assert!(Arc::ptr_eq(&child.state, &root.state));
        assert!(std::ptr::eq(child.context(), root.context()));
        assert_eq!(child.owner(), id);
        let SetupServices::Native(context) = root.state.services() else {
            panic!("native context")
        };
        assert!(Arc::ptr_eq(
            context,
            &lock(&root.state).execution.native_context().unwrap()
        ));
        std::thread::scope(|scope| {
            let escaped = child.clone();
            scope
                .spawn(move || {
                    assert_eq!(escaped.owner(), id);
                    assert!(std::ptr::eq(escaped.context(), child.context()));
                })
                .join()
                .unwrap();
        });
        runtime.dispose(id).unwrap();
        assert_eq!(
            Pin::new(&mut runtime.settle()).poll(&mut TaskContext::from_waker(Waker::noop())),
            Poll::Ready(Ok(()))
        );
        assert!(root.is_cancelled());
        assert!(root.ensure_active().is_err());
        assert_eq!(context.owner(), id);
        assert!(lock(&root.state).execution.native().unwrap().is_closed());
    }
}
