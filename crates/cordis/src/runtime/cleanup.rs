//! Ordinary Rust cleanup dispatch and effect polling.
//!
//! The verified queue owns admission and receipt validation. This adapter
//! polls user code and drops returned payloads outside bookkeeping locks.
//! Callback completion and scheduler progress remain host responsibilities.
use super::*;

impl Runtime {
    fn record_cleanup(
        &mut self,
        id: PluginId,
        group: Option<&EffectHandle>,
        message: CallbackError,
    ) {
        if let Some(handle) = group {
            lock(&handle.status)
                .checked_mut()
                .push_error(message.clone());
        }
        self.cleanup_errors.push(RuntimeError::Cleanup {
            plugin: id,
            error: message,
        });
    }
    fn finish_callback(
        &mut self,
        id: PluginId,
        group: usize,
        handle: Option<&EffectHandle>,
        ticket: RestoreTicket,
        result: CallbackResult,
        retry: Option<RetryCleanup>,
    ) {
        let episode = self
            .kernel
            .host(id)
            .unwrap()
            .episode
            .as_ref()
            .unwrap()
            .clone();
        let completed = lock(&episode.state).cleanups.complete_result(
            group,
            ticket,
            result,
            retry,
            CleanupPolicy::DrainConsumed,
        );
        let report = match completed {
            Ok(report) => report,
            Err(rejected) => {
                drop(rejected);
                panic!("exact issued restoration receipt");
            }
        };
        // User factories leave the bookkeeping lock before they are dropped.
        drop(report.discarded);
        if let Err(message) = report.result {
            if report.outcome == RestoreOutcome::Failed {
                drop(
                    self.kernel
                        .host_mut(id)
                        .unwrap()
                        .control_mut()
                        .record_cleanup_failure(message.clone()),
                );
            }
            self.record_cleanup(id, handle, message);
        }
    }
    fn finish_reply(
        &mut self,
        id: PluginId,
        group: usize,
        handle: Option<&EffectHandle>,
        reply: CleanupReply,
        retry: Option<RetryCleanup>,
    ) {
        let episode = self
            .kernel
            .host(id)
            .unwrap()
            .episode
            .as_ref()
            .unwrap()
            .clone();
        let completed = lock(&episode.state).cleanups.complete_reply(
            group,
            reply,
            retry,
            CleanupPolicy::DrainConsumed,
        );
        // Both discarded and rejected user payloads leave the bookkeeping lock.
        let report = match completed {
            Ok(report) => report,
            Err(rejected) => {
                rejected.discard();
                panic!("exact issued restoration receipt");
            }
        };
        drop(report.discarded);
        if let Err(message) = report.result {
            if report.outcome == RestoreOutcome::Failed {
                drop(
                    self.kernel
                        .host_mut(id)
                        .unwrap()
                        .control_mut()
                        .record_cleanup_failure(message.clone()),
                );
            }
            self.record_cleanup(id, handle, message);
        }
    }
    fn finish_value(
        &mut self,
        id: PluginId,
        handle: Option<&EffectHandle>,
        completion: ValueCleanupReport<CleanupCallback, ChildHandle>,
    ) {
        if let Err(error) = completion.report.result {
            let message = value_error(error);
            drop(
                self.kernel
                    .host_mut(id)
                    .unwrap()
                    .control_mut()
                    .record_cleanup_failure(message.clone()),
            );
            self.record_cleanup(id, handle, message);
        }
    }
    fn finish_payload(
        &mut self,
        id: PluginId,
        handle: Option<&EffectHandle>,
        completion: PayloadCompletion,
    ) {
        let result = completion.report.result;
        // Both the old value and the slot retention guard may reenter the host.
        drop(completion.restored);
        drop(completion.report.discarded);
        if let Err(error) = result {
            let message = payload_restore_error(error);
            drop(
                self.kernel
                    .host_mut(id)
                    .unwrap()
                    .control_mut()
                    .record_cleanup_failure(message.clone()),
            );
            self.record_cleanup(id, handle, message);
        }
    }
    // Independent groups can progress, but a failed retryable inverse blocks
    // every earlier inverse in its own group until an explicit retry.
    pub(super) fn poll_cleanup(
        &mut self,
        id: PluginId,
        group: usize,
        running: &mut Option<RunningCleanup>,
        handle: Option<&EffectHandle>,
        cx: &mut TaskContext<'_>,
    ) -> (bool, bool) {
        let episode = self
            .kernel
            .host(id)
            .unwrap()
            .episode
            .as_ref()
            .unwrap()
            .clone();
        let mut progress = false;
        if running.is_none() {
            let action = lock(&episode.state).cleanups.pop(group);
            if let Some(dispatch) = action {
                progress = true;
                let dispatch = match dispatch {
                    PayloadDispatch::Payload(completion) => {
                        self.finish_payload(id, handle, completion);
                        return (true, false);
                    }
                    PayloadDispatch::Other(dispatch) => dispatch,
                };
                let (ticket, action) = match dispatch {
                    CleanupDispatch::Value { completion, .. } => {
                        self.finish_value(id, handle, completion);
                        return (true, false);
                    }
                    CleanupDispatch::Host { ticket, action } => (ticket, action),
                };
                match action {
                    CleanupAction::Value(_) => {
                        unreachable!("value inverse runs inside the checked dispatcher")
                    }
                    CleanupAction::Native(child) => {
                        let retired = self
                            .kernel
                            .retire_shared_child(&child)
                            .map_err(|error| CallbackError::new(kernel_error(error)));
                        let result = match retired {
                            Ok(Some(identity)) if self.contains(identity.id()) => self
                                .after_retirement(identity.id())
                                .map_err(CallbackError::new),
                            Ok(_) => Ok(()),
                            Err(error) => Err(error),
                        };
                        self.finish_callback(id, group, handle, ticket, result, None);
                    }
                    CleanupAction::External(_) => self.finish_callback(
                        id,
                        group,
                        handle,
                        ticket,
                        Err("ExternalChildInNativeRuntime".into()),
                        None,
                    ),
                    CleanupAction::Callback(cleanup) => match initialize_cleanup(ticket, cleanup) {
                        Ok(future) => *running = Some(future),
                        Err(failure) => self.finish_reply(
                            id,
                            group,
                            handle,
                            CleanupReply::Failed(failure.ticket, failure.message),
                            failure.retry,
                        ),
                    },
                }
            }
        }
        if let Some(attempt) = running.as_mut() {
            match poll_cleanup_callback(attempt, cx) {
                Poll::Pending => return (progress, true),
                Poll::Ready(result) => {
                    let attempt = running.take().unwrap();
                    self.finish_reply(id, group, handle, result, attempt.retry);
                    progress = true;
                }
            }
        }
        (progress, false)
    }

    pub(super) fn poll_groups(
        &mut self,
        id: PluginId,
        unloading: bool,
        cleanup_allowed: bool,
        cx: &mut TaskContext<'_>,
    ) -> (bool, bool) {
        let mut progress = false;
        let mut pending = false;
        let episode = self
            .kernel
            .host(id)
            .unwrap()
            .episode
            .as_ref()
            .unwrap()
            .clone();
        let keys: Vec<_> = lock(&episode.state)
            .cleanups
            .protocol
            .effects()
            .keys()
            .copied()
            .collect();
        for key in keys {
            // Another provider may have departed earlier in this same driver
            // pass. Recheck immediately before a fresh iterator stage.
            let can_start = matches!(self.phase(id), Some(Phase::Active | Phase::Loading))
                && self.coherent(id)
                && self.services_available(id)
                && self.kernel.host(id).unwrap().control().failed().is_none()
                && self
                    .kernel
                    .host(id)
                    .unwrap()
                    .control()
                    .cleanup_failure()
                    .is_none();
            let mut group = lock(&episode.state)
                .cleanups
                .protocol
                .take_effect(key)
                .unwrap();
            let associated = {
                let state = lock(&episode.state);
                let status = lock(&group.get().handle.status);
                status.belongs_to(&episode.state)
                    && status.checked().matches_episode(&state.cleanups.protocol)
            };
            if !associated {
                // Reject before polling, cancellation, error forwarding or any
                // mutation of a handle belonging to another shared Episode.
                let returned = lock(&episode.state).cleanups.protocol.put_effect(group);
                assert!(returned.is_ok(), "retain the foreign-handle group");
                self.latch(id, "effect handle belongs to another episode".into());
                continue;
            }
            let driver = cx.waker().clone();
            let (cancelled, previous) = {
                let mut status = lock(&group.get().handle.status);
                let previous = status.driver.replace(driver);
                if unloading || !can_start {
                    status.checked_mut().cancel();
                }
                (status.checked().observe().cancelled(), previous)
            };
            drop(previous);
            if cancelled {
                let mut state = lock(
                    &self
                        .kernel
                        .host(id)
                        .unwrap()
                        .episode
                        .as_ref()
                        .unwrap()
                        .state,
                );
                // Completed iterators also pass through abstract Leave before
                // their accumulator is restored. In-flight cancellation still
                // keeps the delayed abstract Reloading state until landing.
                state.cleanups.protocol.cancel(group.id());
            }
            if group.get().iterator.is_some() {
                let mut setup = self
                    .kernel
                    .host(id)
                    .unwrap()
                    .episode
                    .as_ref()
                    .unwrap()
                    .clone();
                let target = if can_start {
                    self.kernel.target(id)
                } else {
                    None
                };
                let admitted = {
                    let mut state = lock(&setup.state);
                    state
                        .cleanups
                        .protocol
                        .admit_scoped_effect(&mut group, target.as_deref())
                };
                if let Some(scope) = admitted {
                    let called = group.call_scoped(
                        (scope, (&mut *cx, &mut setup)),
                        |mut payload, (scope, (cx, setup))| {
                            setup.scope = scope;
                            let result = catch_unwind(AssertUnwindSafe(|| {
                                payload.iterator.as_mut().unwrap().poll_next(cx, setup)
                            }));
                            let result = normalize_effect_poll(
                                result,
                                |inverse: Inverse| CleanupAction::Callback(inverse.0),
                                |panic| CallbackError::panic(panic_message(panic)),
                            );
                            (payload, result)
                        },
                    );
                    let (returned, reply) = match called {
                        Ok(called) => called,
                        Err(_) => panic!("one actual call per admitted poll"),
                    };
                    group = returned;
                    let landed = lock(&setup.state)
                        .cleanups
                        .protocol
                        .land_effect(&mut group, reply);
                    let report = match landed {
                        Ok(report) => report,
                        Err(rejected) => {
                            drop(rejected);
                            panic!("actual reply for this admitted effect poll");
                        }
                    };
                    if let Some(report) = report {
                        if let Some(message) = report.error {
                            if !(cancelled && message.is_cancelled()) {
                                lock(&group.get().handle.status)
                                    .checked_mut()
                                    .push_error(message.clone());
                                self.latch(id, message);
                            }
                        }
                        if !report.continue_iteration {
                            group.get_mut().iterator = None;
                        }
                        progress = true;
                    } else {
                        pending = true;
                    }
                } else {
                    group.get_mut().iterator = None;
                    progress = true;
                }
            }
            if group.get().iterator.is_none() {
                let wakers = {
                    // Episode -> status -> Journal. Never acquire Episode while
                    // holding status, and release both before invoking a waker.
                    let state = lock(&episode.state);
                    let mut status = lock(&group.get().handle.status);
                    if status.belongs_to(&episode.state)
                        && !status.checked().observe().initialized()
                        && state
                            .cleanups
                            .protocol
                            .initialize_effect_status(group.id())
                            .is_some()
                    {
                        std::mem::take(&mut status.wakers)
                    } else {
                        BTreeMap::new()
                    }
                };
                wake_waiters(wakers);
            }
            if cancelled
                && group.get().iterator.is_none()
                && ((can_start && !unloading) || cleanup_allowed)
            {
                let group_id = group.id();
                let payload = group.get_mut();
                let (did, waiting) = self.poll_cleanup(
                    id,
                    group_id,
                    &mut payload.running,
                    Some(&payload.handle),
                    cx,
                );
                progress |= did;
                pending |= waiting;
                let episode = self
                    .kernel
                    .host(id)
                    .unwrap()
                    .episode
                    .as_ref()
                    .unwrap()
                    .clone();
                if group.get().running.is_none() {
                    let handle = group.get().handle.clone();
                    let retired = {
                        let mut state = lock(&episode.state);
                        let status = lock(&handle.status);
                        if status.belongs_to(&episode.state) {
                            state.cleanups.protocol.retire_observed_effect(group)
                        } else {
                            Err(group)
                        }
                    };
                    match retired {
                        Ok((payload, _observation)) => {
                            // Removal consumes the actual checkout under the same
                            // lock as registration. Drop user payloads after unlocking.
                            let mut status = lock(&payload.handle.status);
                            let wakers = std::mem::take(&mut status.wakers);
                            drop(status);
                            wake_waiters(wakers);
                            progress = true;
                            continue;
                        }
                        Err(retained) => group = retained,
                    }
                }
            }
            let returned = lock(&episode.state).cleanups.protocol.put_effect(group);
            assert!(
                returned.is_ok(),
                "return the checked-out effect to its live queue"
            );
        }
        (progress, pending)
    }
}
