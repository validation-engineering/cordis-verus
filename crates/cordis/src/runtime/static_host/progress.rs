//! External setup/cleanup handshake, separate from checked execution state.
//! Compound operations receive an already-locked Episode: the lock order is
//! Episode then progress. Displaced application errors return to the caller.
use super::*;

#[derive(Default)]
struct Progress {
    setup_landed: bool,
    abandoned: Option<String>,
    cleanup_running: bool,
    cleanup_error: Option<CallbackError>,
}

#[derive(Default)]
pub(super) struct StaticProgress(Mutex<Progress>);
impl StaticProgress {
    pub(super) fn can_retry_cleanup(&self, state: &Episode) -> bool {
        let progress = lock(&self.0);
        state.phase() != EpisodePhase::Closed
            && progress.abandoned.is_none()
            && progress.cleanup_error.is_some()
            && !progress.cleanup_running
            && state
                .execution
                .get(0)
                .is_some_and(|queue| queue.can_retry())
    }
    pub(super) fn start_cleanup(
        &self,
        state: &mut Episode,
        retry: bool,
    ) -> Result<Option<CallbackError>, String> {
        let mut progress = lock(&self.0);
        if state.phase() == EpisodePhase::Closed {
            return Err("StaticEpisodeClosed".into());
        }
        if let Some(error) = &progress.abandoned {
            return Err(error.clone());
        }
        if !retry {
            if let Some(error) = &progress.cleanup_error {
                return Err(error.to_string());
            }
        }
        if !progress.setup_landed {
            return Err("StaticSetupStillRunning".into());
        }
        if progress.cleanup_running {
            return Err("StaticCleanupStillRunning".into());
        }
        let mut previous_error = None;
        if retry {
            if progress.cleanup_error.is_none()
                || !state
                    .execution
                    .get(0)
                    .is_some_and(|queue| queue.can_retry())
            {
                return Err("StaticCleanupNotRetryable".into());
            }
            state
                .execution
                .retry(0)
                .map_err(|error| format!("StaticCleanupRetry: {error:?}"))?;
            previous_error = progress.cleanup_error.take();
        }
        state.withdraw();
        progress.cleanup_running = true;
        Ok(previous_error)
    }
    pub(super) fn setup_landed(&self) {
        lock(&self.0).setup_landed = true;
    }
    pub(super) fn abandon_setup(&self) {
        lock(&self.0).abandoned = Some("StaticSetupAbandoned: restoration is unconfirmed".into());
    }
    pub(super) fn cleanup_succeeded(&self) {
        lock(&self.0).cleanup_running = false;
    }
    pub(super) fn cleanup_failed(&self, error: CallbackError) -> Option<CallbackError> {
        let mut progress = lock(&self.0);
        progress.cleanup_running = false;
        progress.cleanup_error.replace(error)
    }
}
