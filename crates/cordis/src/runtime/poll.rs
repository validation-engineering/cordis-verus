//! Ordinary Rust poll adapter; callback and scheduling behavior is a host boundary.
use super::*;

impl Runtime {
    pub(crate) fn poll_settle(
        &mut self,
        cx: &mut TaskContext<'_>,
    ) -> Poll<Result<(), RuntimeError>> {
        for _ in 0..1024 {
            if self.maintenance_changes >= 256 {
                self.compact();
            }
            let mut progress = false;
            let mut pending = false;
            // Dynamic service disposal is a normal verified provider retirement.
            for id in self.kernel.ids() {
                if let Some(service) = self.kernel.host(id).unwrap().service.clone() {
                    let cancelled = service.poll_driver(cx, false);
                    if cancelled && !self.retired(id) {
                        if let Err(error) = self.dispose(id) {
                            return Poll::Ready(Err(error));
                        }
                        progress = true;
                    }
                }
            }
            // Withdraw stale services before allowing any inverse to start.
            for id in self.kernel.ids() {
                if self.decision(id) == Some(Decision::Withdraw) {
                    if let Err(error) = self.leave(id) {
                        return Poll::Ready(Err(error));
                    }
                    progress = true;
                }
            }
            for id in self.kernel.ids() {
                if self.decision(id) == Some(Decision::Withdraw) {
                    if let Err(error) = self.leave(id) {
                        return Poll::Ready(Err(error));
                    }
                    progress = true;
                }
                let phase = self.phase(id).unwrap();
                if !matches!(phase, Phase::Loading | Phase::Active | Phase::Unloading) {
                    continue;
                }
                let Some(episode) = self.kernel.host(id).unwrap().episode.clone() else {
                    continue;
                };
                let driver = cx.waker().clone();
                let previous = lock(&episode.state).replace_driver(driver);
                drop(previous);
                let root_poll = self.kernel.host_mut(id).unwrap().root_setup.poll(
                    phase == Phase::Unloading,
                    &episode,
                    cx,
                );
                match root_poll {
                    Some(Poll::Pending) => pending = true,
                    Some(Poll::Ready(result)) => {
                        progress = true;
                        if let Err(message) = result {
                            if !(phase == Phase::Unloading && message.is_cancelled()) {
                                self.latch(id, message);
                            }
                        }
                    }
                    None => {}
                }
                match self.drain_requests(id) {
                    Ok(did) => progress |= did,
                    Err(error) => return Poll::Ready(Err(error)),
                }
                let unloading = phase == Phase::Unloading;
                if unloading
                    && self.kernel.host(id).unwrap().root_setup.is_done()
                    && !self.kernel.cleanup_started(id)
                {
                    // Do not restore any resource while any group has a setup
                    // poll outstanding: it may still rely on that resource.
                    let state = lock(&episode.state);
                    if state.execution.is_idle() && !state.execution.has_pending() {
                        if let Err(error) =
                            self.kernel.settle_managed_execution(id, &state.execution)
                        {
                            return Poll::Ready(Err(kernel_error(error)));
                        }
                        match self.kernel.begin_cleanup(id) {
                            Ok(()) => progress = true,
                            Err(KernelError::Relied) => {}
                            Err(error) => return Poll::Ready(Err(kernel_error(error))),
                        }
                    }
                }
                let cleanup_allowed = unloading
                    && self.kernel.cleanup_started(id)
                    && self.kernel.pending_action(id).is_some();
                let (did, waiting) = self.poll_groups(
                    id,
                    unloading || self.kernel.host(id).unwrap().control().failed().is_some(),
                    cleanup_allowed,
                    cx,
                );
                progress |= did;
                pending |= waiting;
                match self.drain_requests(id) {
                    Ok(did) => progress |= did,
                    Err(error) => return Poll::Ready(Err(error)),
                }
                if unloading
                    && cleanup_allowed
                    && self.kernel.host(id).unwrap().root_setup.is_done()
                {
                    let mut running = self.kernel.host_mut(id).unwrap().root_running.take();
                    let (did, waiting) = self.poll_cleanup(id, 0, &mut running, None, cx);
                    self.kernel.host_mut(id).unwrap().root_running = running;
                    progress |= did;
                    pending |= waiting;
                    let mut state = lock(&episode.state);
                    let retained_failure = state.execution.has_failed();
                    let callbacks_idle = self.kernel.host(id).unwrap().root_running.is_none()
                        && state.execution.effects().values().all(|group| {
                            group.get().running.is_none() && group.get().iterator.is_none()
                        });
                    if retained_failure && callbacks_idle {
                        if self.kernel.pending_action(id).is_some() {
                            if let Err(error) =
                                self.kernel.fail_managed_execution(id, &state.execution)
                            {
                                return Poll::Ready(Err(kernel_error(error)));
                            }
                            progress = true;
                        }
                    } else if self.kernel.host(id).unwrap().root_running.is_none()
                        && state.execution.effects().is_empty()
                        && state.execution.is_idle()
                        && state.execution.can_seal()
                    {
                        let episode_values = match self.release_controlled(id, &mut state.execution)
                        {
                            Ok((_, released)) => released,
                            Err(error) => return Poll::Ready(Err(kernel_error(error))),
                        };
                        self.maintenance_changes += 1;
                        // Services commonly retain their setup context. Empty the
                        // closed episode to break value -> context -> value cycles,
                        // but only after all consumer inverses have completed.
                        let previous_driver = state.take_driver();
                        drop(state);
                        let plugin = self.kernel.host_mut(id).unwrap();
                        plugin.episode = None;
                        plugin.root_setup = RootSetup::dormant();
                        // Escaped setup contexts must not retain a closed
                        // episode's driver. User waker destruction is unlocked.
                        drop(previous_driver);
                        drop(episode_values);
                        progress = true;
                    }
                } else if phase == Phase::Loading
                    && self.kernel.host(id).unwrap().root_setup.is_done()
                    && self.kernel.host(id).unwrap().initialized_effects()
                    && self.kernel.host(id).unwrap().control().failed().is_none()
                {
                    let mut state = lock(&episode.state);
                    // Serialize the Loading -> Active boundary with registration
                    // through escaped contexts. Requests admitted during Loading
                    // are initialized before the service becomes observable.
                    if state.execution.group_count() != 0 || state.execution.child_count() != 0 {
                        progress = true;
                        continue;
                    }
                    let target = self.kernel.target(id);
                    if !target
                        .as_ref()
                        .is_some_and(|target| state.can_finish(target))
                    {
                        // The protocol rejects publication while any admitted
                        // stage remains outstanding or its target has drifted.
                        drop(state);
                        if let Err(error) = self.leave(id) {
                            return Poll::Ready(Err(error));
                        }
                        progress = true;
                        continue;
                    }
                    let missing = state
                        .execution
                        .native()
                        .expect("native execution")
                        .missing();
                    if let Some(port) = missing {
                        drop(state);
                        self.latch(
                            id,
                            format!("declared service {} has no value", port.key).into(),
                        );
                        progress = true;
                    } else {
                        let finished = self
                            .kernel
                            .finish_recorded_execution(id, &mut state.execution);
                        drop(state);
                        match finished {
                            Ok(()) => {
                                if let Some(service) = &self.kernel.host(id).unwrap().service {
                                    service.initialize_service(false);
                                }
                            }
                            Err(KernelError::Changed) => {
                                if let Err(error) = self.leave(id) {
                                    return Poll::Ready(Err(error));
                                }
                            }
                            Err(error) => return Poll::Ready(Err(kernel_error(error))),
                        }
                        progress = true;
                    }
                }
            }
            for id in self.kernel.ids().into_iter().rev() {
                if self.retired(id)
                    && self.phase(id) == Some(Phase::Inactive)
                    && self.decision(id) == Some(Decision::Remove)
                {
                    let removed = match self.kernel.remove(id) {
                        Ok(removed) => removed,
                        Err(error) => return Poll::Ready(Err(kernel_error(error))),
                    };
                    self.maintenance_changes += 1;
                    let (registration, host) = removed.into_parts();
                    if let Some(service) = &host.service {
                        service.finish_service();
                    }
                    drop((registration, host));
                    progress = true;
                }
            }
            for id in self.kernel.ids() {
                if self.phase(id) != Some(Phase::Inactive)
                    || self.decision(id) != Some(Decision::Begin)
                {
                    continue;
                }
                let execution = match self.begin_controlled(id) {
                    Ok(owners) => owners,
                    Err(KernelError::MissingDependency) => continue,
                    Err(error) => return Poll::Ready(Err(kernel_error(error))),
                };
                self.start(id, cx, execution);
                progress = true;
            }
            if progress {
                continue;
            }
            if let Some(id) = self.kernel.ids().into_iter().find(|id| {
                self.kernel
                    .host(*id)
                    .unwrap()
                    .control()
                    .cleanup_failure()
                    .is_some()
            }) {
                return Poll::Ready(Err(RuntimeError::Cleanup {
                    plugin: id,
                    error: self
                        .kernel
                        .host(id)
                        .unwrap()
                        .control()
                        .cleanup_failure()
                        .cloned()
                        .unwrap(),
                }));
            }
            if pending {
                return Poll::Pending;
            }
            if self
                .kernel
                .ids()
                .iter()
                .any(|id| matches!(self.phase(*id), Some(Phase::Loading | Phase::Unloading)))
            {
                return Poll::Ready(Err(RuntimeError::Stalled));
            }
            if let Some(id) = self
                .kernel
                .ids()
                .into_iter()
                .find(|id| self.kernel.host(*id).unwrap().control().failed().is_some())
            {
                return Poll::Ready(Err(RuntimeError::Setup {
                    plugin: id,
                    error: self
                        .kernel
                        .host(id)
                        .unwrap()
                        .control()
                        .failed()
                        .cloned()
                        .unwrap(),
                }));
            }
            return Poll::Ready(Ok(()));
        }
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}
