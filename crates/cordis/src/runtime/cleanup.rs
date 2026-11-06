//! Ordinary Rust cleanup dispatch and effect polling.
//!
//! The verified queue owns admission and receipt validation. This adapter
//! polls user code and drops returned payloads outside bookkeeping locks.
//! Callback completion and scheduler progress remain host responsibilities.
pub(super) mod attempt;
use super::*;

impl Runtime {
    fn record_cleanup(
        &mut self,
        id: PluginId,
        group: Option<&EffectHandle>,
        message: CallbackError,
    ) {
        if let Some(handle) = group {
            handle.record_error(message.clone());
        }
        self.cleanup_errors.push(RuntimeError::Cleanup {
            plugin: id,
            error: message,
        });
    }
    // Both synchronous Child reports and paired callback completions arrive
    // after acknowledgement has left the Episode lock. Only Failed blocks;
    // Drained keeps the host's existing consumed-cleanup policy.
    fn record_cleanup_report(
        &mut self,
        id: PluginId,
        handle: Option<&EffectHandle>,
        report: CleanupReport<CallbackError, CleanupAction>,
    ) {
        drop(report.discarded);
        if let Err(message) = report.result {
            if report.outcome == RestoreOutcome::Failed {
                drop(
                    self.kernel
                        .host_mut(id)
                        .unwrap()
                        .control
                        .record_cleanup_failure(message.clone()),
                );
            }
            self.record_cleanup(id, handle, message);
        }
    }
    fn finish_child_result(
        &mut self,
        id: PluginId,
        group: usize,
        handle: Option<&EffectHandle>,
        ticket: RestoreTicket,
        result: CallbackResult,
    ) {
        let episode = self
            .kernel
            .host(id)
            .unwrap()
            .episode
            .as_ref()
            .unwrap()
            .clone();
        let completed = lock(&episode.state).execution.complete_result(
            group,
            ticket,
            result,
            None,
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
        self.record_cleanup_report(id, handle, report);
    }
    fn finish_reply(
        &mut self,
        id: PluginId,
        group: usize,
        handle: Option<&EffectHandle>,
        completion: CleanupCompletion,
    ) {
        let episode = self
            .kernel
            .host(id)
            .unwrap()
            .episode
            .as_ref()
            .unwrap()
            .clone();
        let completed = completion.acknowledge(
            &mut lock(&episode.state).execution,
            group,
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
        self.record_cleanup_report(id, handle, report);
    }
    fn finish_value(
        &mut self,
        id: PluginId,
        handle: Option<&EffectHandle>,
        completion: ValueCleanupReport<CleanupCallback, child::StaticChildControl>,
    ) {
        if let Err(error) = completion.report.result {
            let message = value_error(error);
            drop(
                self.kernel
                    .host_mut(id)
                    .unwrap()
                    .control
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
                    .control
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
            let action = lock(&episode.state)
                .execution
                .dispatch(group)
                .expect("live cleanup group and available attempt identity");
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
                        self.finish_child_result(id, group, handle, ticket, result);
                    }
                    CleanupAction::External(_) => self.finish_child_result(
                        id,
                        group,
                        handle,
                        ticket,
                        Err("ExternalChildInNativeRuntime".into()),
                    ),
                    CleanupAction::Callback(cleanup) => {
                        match RunningCleanup::start(ticket, cleanup) {
                            Ok(future) => *running = Some(future),
                            Err(failure) => self.finish_reply(id, group, handle, failure),
                        }
                    }
                }
            }
        }
        if let Some(attempt) = running.as_mut() {
            match attempt.poll(cx) {
                Poll::Pending => return (progress, true),
                Poll::Ready(result) => {
                    let attempt = running.take().unwrap();
                    self.finish_reply(id, group, handle, result);
                    progress = true;
                    // A user Future is dropped after acknowledgement and unlocking.
                    drop(attempt);
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
            .execution
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
            let mut group = lock(&episode.state).execution.take_effect(key).unwrap();
            let associated = group.get().handle.matches_episode(&episode.state);
            if !associated {
                // Reject before polling, cancellation, error forwarding or any
                // mutation of a handle belonging to another shared Episode.
                let returned = lock(&episode.state).execution.put_effect(group);
                assert!(returned.is_ok(), "retain the foreign-handle group");
                self.latch(id, "effect handle belongs to another episode".into());
                continue;
            }
            let cancelled = group.get().handle.poll_driver(cx, unloading || !can_start);
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
                state.execution.cancel(group.id());
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
                        .execution
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
                    let landed = lock(&setup.state).execution.land_effect(&mut group, reply);
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
                                group.get().handle.record_error(message.clone());
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
                group
                    .get()
                    .handle
                    .initialize_effect(&episode.state, group.id());
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
                    match EffectHandle::retire_effect(&episode.state, group) {
                        effect_handle::Retirement::Finished(payload) => {
                            // The checked removal returns the actual payload;
                            // user destructors run after all bookkeeping locks.
                            drop(payload);
                            progress = true;
                            continue;
                        }
                        effect_handle::Retirement::Retained(retained) => group = retained,
                    }
                }
            }
            let returned = lock(&episode.state).execution.put_effect(group);
            assert!(
                returned.is_ok(),
                "return the checked-out effect to its live queue"
            );
        }
        (progress, pending)
    }
}
