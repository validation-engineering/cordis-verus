//! Ordinary Rust setup adapter; callback and scheduling behavior is a host boundary.
use super::*;

impl AsyncSetup {
    pub(super) fn require_dynamic(&self, feature: &str) -> CallbackResult {
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        if !state.static_only
            || (state.dynamic_host.is_some() && matches!(feature, "publish" | "mount"))
            || (state.service_updates.is_some()
                && matches!(feature, "provide_checked" | "set" | "refresh"))
        {
            return Ok(());
        }
        let message = format!("UnsupportedStaticFeature: {feature}");
        if state.unsupported.is_none() {
            state.unsupported = Some(message.clone());
        }
        Err(message.into())
    }
    /// Check whether this episode still accepts new effects (Loading or Active).
    /// In-flight setup may register its inverse after cancellation, but new
    /// timer, event or child resource acquisition should use this guard first.
    pub fn ensure_active(&self) -> CallbackResult {
        let state = lock(&self.state);
        if !self.scope.belongs(&state.cleanups.protocol)
            || !state
                .cleanups
                .protocol
                .accepts_acquisition(self.scope.group())
        {
            return Err(CANCELLED.into());
        }
        match state.phase() {
            EpisodePhase::Loading | EpisodePhase::Active => Ok(()),
            EpisodePhase::Restoring => Err(CANCELLED.into()),
            EpisodePhase::Closed => Err("owner episode has completed".into()),
        }
    }
    pub fn is_cancelled(&self) -> bool {
        let state = lock(&self.state);
        matches!(
            state.phase(),
            EpisodePhase::Restoring | EpisodePhase::Closed
        ) || !self.scope.belongs(&state.cleanups.protocol)
            || !state
                .cleanups
                .protocol
                .accepts_acquisition(self.scope.group())
    }
    pub fn owner(&self) -> PluginId {
        self.state.services.owner()
    }
    pub fn context(&self) -> &Context {
        &self.state.context
    }
    pub(super) fn check_live(&self, state: &Episode) -> CallbackResult {
        if state.phase() == EpisodePhase::Closed {
            Err("owner episode has completed".into())
        } else if !self.scope.belongs(&state.cleanups.protocol) {
            Err("effect group has completed".into())
        } else {
            Ok(())
        }
    }
    #[track_caller]
    pub fn get<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
    ) -> Result<Arc<T>, ServiceReadError> {
        self.require(key)
    }
    /// Read the episode-committed provider, with structured call-site errors.
    /// Reads remain valid during restoration and reject a completed episode.
    #[track_caller]
    pub fn require<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
    ) -> Result<Arc<T>, ServiceReadError> {
        let port = self.state.context.port(key);
        let location = std::panic::Location::caller();
        let error = |reason, provider| ServiceReadError {
            reason,
            provider,
            port,
            location,
            service: key.name,
            value_type: std::any::type_name::<T>(),
            plugin: self.state.services.owner(),
            generation: self.state.generation,
        };
        let state = lock(&self.state);
        if state.phase() == EpisodePhase::Closed {
            return Err(error(ServiceReadFailure::ClosedEpisode, None));
        }
        let (provider, value) = match state.cleanups.protocol.native() {
            Some(values) => {
                let (provider, slot) = values.read(port).map_err(|failure| {
                    let reason = match failure.reason {
                        NativeValueError::Closed => ServiceReadFailure::ClosedEpisode,
                        NativeValueError::Undeclared => ServiceReadFailure::Undeclared,
                        _ => ServiceReadFailure::MissingValue,
                    };
                    error(reason, failure.provider)
                })?;
                (provider, Some(slot.clone()))
            }
            None => {
                let (provider, slot) = state.values.read(port).map_err(|failure| {
                    error(
                        match failure.reason {
                            NativeValueError::Closed => ServiceReadFailure::ClosedEpisode,
                            NativeValueError::Undeclared => ServiceReadFailure::Undeclared,
                            _ => ServiceReadFailure::MissingValue,
                        },
                        failure.provider,
                    )
                })?;
                (provider, Some(slot.clone()))
            }
        };
        drop(state);
        let slot = value.ok_or_else(|| error(ServiceReadFailure::MissingValue, Some(provider)))?;
        slot.get::<T>()
            .ok_or_else(|| error(ServiceReadFailure::TypeMismatch, Some(provider)))
    }
    /// Capture the actual committed provider, slot version and shared object.
    /// This is a retained read, not a new lifecycle lease or write permission.
    #[track_caller]
    pub fn capture_reversible(
        &self,
        key: ServiceKey<ReversibleValue>,
    ) -> Result<ValueServiceBinding, ServiceReadError> {
        let port = self.state.context.port(key);
        let location = std::panic::Location::caller();
        let error = |reason, provider| ServiceReadError {
            reason,
            provider,
            port,
            location,
            service: key.name,
            value_type: std::any::type_name::<ReversibleValue>(),
            plugin: self.state.services.owner(),
            generation: self.state.generation,
        };
        let state = lock(&self.state);
        if state.phase() == EpisodePhase::Closed {
            return Err(error(ServiceReadFailure::ClosedEpisode, None));
        }
        if let Some(values) = state.cleanups.protocol.native() {
            return values
                .read_reversible(port)
                .map_err(|failure| self.reversible_read_error(key, location, failure));
        }
        // Static embeddings supply their own authoritative provider/lease
        // contract. They still use the exact same checked slot and capture.
        let (provider, slot) = state.values.read(port).map_err(|failure| {
            error(
                match failure.reason {
                    NativeValueError::Closed => ServiceReadFailure::ClosedEpisode,
                    NativeValueError::Undeclared => ServiceReadFailure::Undeclared,
                    _ => ServiceReadFailure::MissingValue,
                },
                failure.provider,
            )
        })?;
        slot.capture_binding(provider, port)
            .ok_or_else(|| error(ServiceReadFailure::TypeMismatch, Some(provider)))
    }
    /// Read a declared scalar service through the checked native binding path.
    /// The snapshot includes its actual object state and execution checkpoint.
    #[track_caller]
    pub fn observe_reversible(
        &self,
        key: ServiceKey<ReversibleValue>,
    ) -> Result<cordis_kernel::reversible_value::Snapshot, ServiceReadError> {
        let location = std::panic::Location::caller();
        let state = lock(&self.state);
        if let Some(values) = state.cleanups.protocol.native() {
            return values
                .observe_reversible(self.state.context.port(key))
                .map(|report| report.snapshot)
                .map_err(|error| self.reversible_read_error(key, location, error));
        }
        drop(state);
        Ok(self.capture_reversible(key)?.value().snapshot())
    }
    pub(super) fn reversible_read_error(
        &self,
        key: ServiceKey<ReversibleValue>,
        location: &'static std::panic::Location<'static>,
        failure: ValueReadError,
    ) -> ServiceReadError {
        let (reason, provider) = match failure {
            ValueReadError::Native(failure) => (
                match failure.reason {
                    NativeValueError::Closed => ServiceReadFailure::ClosedEpisode,
                    NativeValueError::Undeclared => ServiceReadFailure::Undeclared,
                    _ => ServiceReadFailure::MissingValue,
                },
                failure.provider,
            ),
            ValueReadError::NotReversible { provider } => {
                (ServiceReadFailure::TypeMismatch, Some(provider))
            }
        };
        ServiceReadError {
            reason,
            provider,
            port: self.state.context.port(key),
            location,
            service: key.name,
            value_type: std::any::type_name::<ReversibleValue>(),
            plugin: self.state.services.owner(),
            generation: self.state.generation,
        }
    }
    pub fn provide<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<Arc<T>, CallbackError> {
        self.provide_inner(key, value, None)
    }
    /// Publish a declared service with a pure per-consumer availability check.
    /// Panics make the dependency unavailable. Call `refresh` after external
    /// predicate state changes to wake a pending lifecycle driver.
    pub fn provide_checked<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<Arc<T>, CallbackError> {
        self.require_dynamic("provide_checked")?;
        self.provide_inner(key, value, Some(typed_check(check)))
    }
    pub(super) fn provide_inner<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: Option<ServiceCheck>,
    ) -> Result<Arc<T>, CallbackError> {
        let value = Arc::new(value);
        let slot = {
            let state = lock(&self.state);
            ServiceSlot::from_execution(&state.cleanups.protocol, value.clone(), check)
        };
        self.provide_slot(key, slot)?;
        Ok(value)
    }
    pub(super) fn provide_slot<T>(&self, key: ServiceKey<T>, value: SharedSlot) -> CallbackResult {
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        let port = self.state.context.port(key);
        let result = state.provide(
            self.state.services.owner(),
            self.state.services.provisions(),
            port,
            value,
        );
        let waker = if result.is_ok() {
            state.driver.take()
        } else {
            None
        };
        drop(state);
        result.map_err(|(reason, rejected)| {
            drop(rejected);
            match reason {
                NativeValueError::Closed => "owner episode has completed".to_owned(),
                NativeValueError::Undeclared => format!("undeclared provision: {}", key.name),
                NativeValueError::Duplicate => format!("duplicate value: {}", key.name),
                NativeValueError::Missing => format!("missing value: {}", key.name),
            }
        })?;
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(())
    }
    pub fn set<T: Any + Send + Sync>(&self, key: ServiceKey<T>, value: T) -> CallbackResult {
        self.require_dynamic("set")?;
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        let port = self.state.context.port(key);
        if !self.state.services.provisions().contains(&port) {
            return Err(format!("service is not owned here: {}", key.name).into());
        }
        let slot = state
            .own(self.state.services.owner(), port)
            .cloned()
            .ok_or_else(|| format!("service is not owned here: {}", key.name))?;
        if state.service_updates.is_some()
            && !matches!(state.phase(), EpisodePhase::Loading | EpisodePhase::Active)
        {
            return Err(CANCELLED.into());
        }
        let previous = match slot.replace(Arc::new(value)) {
            Ok(previous) => previous,
            Err(rejected) => {
                drop(state);
                drop(rejected.value);
                return Err(rejected.message.into());
            }
        };
        let notify = state.service_updates.clone();
        let waker = state.driver.take();
        drop(state);
        drop(previous);
        if let Some(notify) = notify {
            notify();
        }
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(())
    }
    /// Replace a declared native service payload and retain its checked inverse
    /// in this effect group's cleanup queue. Later writes block restoration;
    /// explicit cleanup retry resumes after the conflicting write is restored.
    /// Interior mutations of T are outside this replacement contract.
    #[track_caller]
    pub fn replace_service<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
    ) -> CallbackResult {
        let value: Value = Arc::new(value);
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        let result = state.cleanups.protocol.apply_native_payload(
            self.scope.group(),
            self.state.context.port(key),
            value,
        );
        let wake = if result.is_ok() {
            state.driver.take()
        } else {
            None
        };
        drop(state);
        if let Some(wake) = wake {
            wake.wake();
        }
        result.map(|_| ()).map_err(|(error, rejected)| {
            // Rejected values, including their destructors, leave the host lock.
            drop(rejected);
            use cordis_kernel::cleanup_groups::payload::AccessError;
            match error {
                AccessError::NoNative => "replace_service requires native service storage".into(),
                AccessError::Read(error) => {
                    format!("service replacement failed: {:?}", error.reason).into()
                }
                AccessError::Scalar => "use update_reversible for a ReversibleValue service".into(),
                AccessError::Value(cordis_kernel::versioned_value::ReplaceError::Capacity) => {
                    "service replacement revision capacity exhausted".into()
                }
                AccessError::Value(_) => CANCELLED.into(),
            }
        })
    }
    /// Apply a checked operation to a declared shared service. Its actual
    /// inverse enters this episode's cleanup queue before the call returns.
    /// Interference blocks restoration and keeps that inverse for retry.
    #[track_caller]
    pub fn update_reversible(
        &self,
        key: ServiceKey<ReversibleValue>,
        operation: ValueOperation,
    ) -> Result<ValueOutcome, CallbackError> {
        let location = std::panic::Location::caller();
        {
            let mut state = lock(&self.state);
            self.check_live(&state)?;
            if state.cleanups.protocol.native().is_some() {
                let result = state.cleanups.protocol.apply_native_value(
                    self.scope.group(),
                    self.state.context.port(key),
                    operation,
                    ValueBranch {
                        matched: None,
                        unmatched: None,
                    },
                );
                let wake = if result.is_ok() {
                    state.driver.take()
                } else {
                    None
                };
                drop(state);
                if let Some(wake) = wake {
                    wake.wake();
                }
                return result
                    .map(|report| report.admission.outcome)
                    .map_err(|error| {
                        use cordis_kernel::reversible_value::access::Error;
                        match error {
                            Error::NoNativeOwner => {
                                CallbackError::from("owner does not use native services")
                            }
                            Error::Read(error) => {
                                self.reversible_read_error(key, location, error).into()
                            }
                            Error::Value(error) => value_error(error),
                        }
                    });
            }
        }
        let binding = self.capture_reversible(key)?;
        let value = binding.value();
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        let result = state.cleanups.protocol.apply_value(
            self.scope.group(),
            value,
            operation,
            ValueBranch {
                matched: None,
                unmatched: None,
            },
        );
        let wake = if result.is_ok() {
            state.driver.take()
        } else {
            None
        };
        drop(state);
        if let Some(wake) = wake {
            wake.wake();
        }
        result.map(|admitted| admitted.outcome).map_err(value_error)
    }
    /// Compute an extensible scalar effect without holding host or value locks.
    /// Landing rechecks acquisition and the captured value/depth, then retains
    /// the actual inverse in this episode before returning the outcome.
    ///
    /// A change to the captured value/depth rejects the prepared result; retry
    /// explicitly to compute again. Exact restoration to the captured state is
    /// allowed. Verus-verified implementations also establish the
    /// effect's model law. Arbitrary Rust bodies and external side effects do not
    /// inherit that proof merely by implementing the trait.
    #[track_caller]
    pub fn update_reversible_with<E: ScalarEffect>(
        &self,
        key: ServiceKey<ReversibleValue>,
        effect: E,
    ) -> Result<ValueOutcome, CallbackError> {
        let capture = {
            let state = lock(&self.state);
            self.check_live(&state)?;
            if state.cleanups.protocol.native().is_some() {
                let location = std::panic::Location::caller();
                Some(
                    state
                        .cleanups
                        .protocol
                        .capture_native_effect(self.scope.group(), self.state.context.port(key))
                        .map_err(|error| match error {
                            cordis_kernel::reversible_value::cursor::StartError::Closed => {
                                CallbackError::from(CANCELLED)
                            }
                            cordis_kernel::reversible_value::cursor::StartError::NoNativeOwner => {
                                CallbackError::from("owner does not use native services")
                            }
                            cordis_kernel::reversible_value::cursor::StartError::Read(error) => {
                                self.reversible_read_error(key, location, error).into()
                            }
                        })?,
                )
            } else {
                None
            }
        };
        if let Some(capture) = capture {
            // Both host and value locks are released before invoking user code.
            let computation = catch_unwind(AssertUnwindSafe(|| capture.prepare(effect)))
                .map_err(|panic| CallbackError::panic(panic_message(panic)))?;
            let mut state = lock(&self.state);
            self.check_live(&state)?;
            let result = state.cleanups.protocol.apply_native_effect(
                self.scope.group(),
                computation,
                ValueBranch {
                    matched: None,
                    unmatched: None,
                },
            );
            let wake = if result.is_ok() {
                state.driver.take()
            } else {
                None
            };
            drop(state);
            if let Some(wake) = wake {
                wake.wake();
            }
            return result
                .map(|write| write.admission.outcome)
                .map_err(effect_error);
        }
        self.ensure_active()?;
        let binding = self.capture_reversible(key)?;
        let value = binding.value();
        let prepared = catch_unwind(AssertUnwindSafe(|| value.prepare_effect(effect)))
            .map_err(|panic| CallbackError::panic(panic_message(panic)))?;
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        let result = state.cleanups.protocol.apply_prepared_effect(
            self.scope.group(),
            prepared,
            ValueBranch {
                matched: None,
                unmatched: None,
            },
        );
        let wake = if result.is_ok() {
            state.driver.take()
        } else {
            None
        };
        drop(state);
        if let Some(wake) = wake {
            wake.wake();
        }
        result
            .map(|admitted| admitted.outcome)
            .map_err(effect_error)
    }
    /// Bind a resumable program to this episode, group and actual service.
    /// The cursor owns the continuation; each advance retains its inverse before
    /// returning. Other callers may change the value between advances.
    #[track_caller]
    pub fn start_value_program(
        &self,
        key: ServiceKey<ReversibleValue>,
        program: ValueProgram,
    ) -> Result<ValueProgramCursor, CallbackError> {
        let state = lock(&self.state);
        self.check_live(&state)?;
        if state.cleanups.protocol.native().is_some() {
            let location = std::panic::Location::caller();
            return state
                .cleanups
                .protocol
                .begin_native_value_program(
                    self.scope.group(),
                    self.state.context.port(key),
                    program,
                )
                .map_err(|error| match error {
                    cordis_kernel::reversible_value::cursor::StartError::Closed => {
                        CallbackError::from(CANCELLED)
                    }
                    cordis_kernel::reversible_value::cursor::StartError::Read(error) => {
                        self.reversible_read_error(key, location, error).into()
                    }
                    cordis_kernel::reversible_value::cursor::StartError::NoNativeOwner => {
                        CallbackError::from("owner does not use native services")
                    }
                });
        }
        drop(state);
        let binding = self.capture_reversible(key)?;
        let state = lock(&self.state);
        self.check_live(&state)?;
        state
            .cleanups
            .protocol
            .begin_bound_value_program(self.scope.group(), binding, program)
            .map_err(|_| CallbackError::from(CANCELLED))
    }
    /// Run the stored next instruction. `None` means the program is complete;
    /// overflow leaves the same instruction ready for an explicit retry.
    /// A foreign episode/group or closed owner is rejected before any write.
    pub fn advance_value_program(
        &self,
        cursor: &mut ValueProgramCursor,
    ) -> Result<Option<ValueOutcome>, CallbackError> {
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        let result = state
            .cleanups
            .protocol
            .advance_value_program(self.scope.group(), cursor);
        let wake = if matches!(result, Ok(Some(_))) {
            state.driver.take()
        } else {
            None
        };
        drop(state);
        if let Some(wake) = wake {
            wake.wake();
        }
        result.map_err(value_error)
    }
    /// Execute a finite native body across several declared services.
    /// All instructions, including unselected branches, must use declared keys.
    /// Each step resolves its current slot and retains its inverse before the
    /// next step. Concurrent callers may write or replace slots between steps;
    /// this is not a transaction. A failed prefix remains owned for cleanup.
    #[track_caller]
    pub fn run_service_program(
        &self,
        instructions: &[ServiceInstruction],
    ) -> Result<Vec<ValueOutcome>, CallbackError> {
        use cordis_kernel::reversible_value::services::{AdmissionError, Call, Program};
        let location = std::panic::Location::caller();
        let code = instructions
            .iter()
            .map(|instruction| Call {
                port: self.state.context.port(instruction.key),
                instruction: ValueInstruction {
                    operation: instruction.operation,
                    branch: instruction.branch,
                },
            })
            .collect();
        let program = Program::new(code).map_err(|_| {
            CallbackError::from("service program continuations must point forward within its body")
        })?;
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        let result = state
            .cleanups
            .protocol
            .run_service_program(self.scope.group(), &program);
        let wake = if result.is_ok() {
            state.driver.take()
        } else {
            None
        };
        drop(state);
        if let Some(wake) = wake {
            wake.wake();
        }
        let report = result.map_err(|error| match error {
            AdmissionError::Closed => CallbackError::from(CANCELLED),
            AdmissionError::NoNativeOwner => {
                CallbackError::from("service programs require native services")
            }
            AdmissionError::Undeclared { pc, .. } => self
                .reversible_read_error(
                    instructions[pc].key,
                    location,
                    ValueReadError::Native(
                        cordis_kernel::lifecycle_state::services::NativeReadError {
                            reason: NativeValueError::Undeclared,
                            provider: None,
                        },
                    ),
                )
                .into(),
        })?;
        if let Some(failure) = report.failure {
            use cordis_kernel::reversible_value::access::Error;
            return Err(match failure.error {
                Error::NoNativeOwner => {
                    CallbackError::from("service programs require native services")
                }
                Error::Read(error) => self
                    .reversible_read_error(instructions[failure.pc].key, location, error)
                    .into(),
                Error::Value(error) => value_error(error),
            });
        }
        Ok(report
            .steps
            .into_iter()
            .map(|step| step.write.admission.outcome)
            .collect())
    }
    /// Run a finite program without interleaved writes to this value. Every
    /// successful prefix remains registered even if a later operation fails.
    #[track_caller]
    pub fn run_value_program(
        &self,
        key: ServiceKey<ReversibleValue>,
        program: &ValueProgram,
    ) -> Result<Vec<ValueOutcome>, CallbackError> {
        let location = std::panic::Location::caller();
        {
            let mut state = lock(&self.state);
            self.check_live(&state)?;
            if state.cleanups.protocol.native().is_some() {
                let result = state.cleanups.protocol.run_native_value_program(
                    self.scope.group(),
                    self.state.context.port(key),
                    program,
                );
                let wake = if result.is_ok() {
                    state.driver.take()
                } else {
                    None
                };
                drop(state);
                if let Some(wake) = wake {
                    wake.wake();
                }
                let report = result.map_err(|error| {
                    use cordis_kernel::reversible_value::function::Error;
                    match error {
                        Error::Read(error) => {
                            self.reversible_read_error(key, location, error).into()
                        }
                        Error::Value(error) => value_error(error),
                        Error::NoNativeOwner => {
                            CallbackError::from("owner does not use native services")
                        }
                        Error::NotRunning => CallbackError::from(CANCELLED),
                        Error::WrongKey => CallbackError::from("program service key mismatch"),
                    }
                })?;
                return match report.program.error {
                    Some(error) => Err(value_error(error)),
                    None => Ok(report.program.outcomes),
                };
            }
        }
        let binding = self.capture_reversible(key)?;
        let value = binding.value();
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        let result = state
            .cleanups
            .protocol
            .run_value_program(self.scope.group(), value, program);
        let wake = if result.is_ok() {
            state.driver.take()
        } else {
            None
        };
        drop(state);
        if let Some(wake) = wake {
            wake.wake();
        }
        let report = result.map_err(value_error)?;
        match report.error {
            Some(error) => Err(value_error(error)),
            None => Ok(report.outcomes),
        }
    }
    /// Notify the driver after changing external service-check state.
    pub fn refresh(&self) -> CallbackResult {
        self.require_dynamic("refresh")?;
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        if state.service_updates.is_some()
            && !matches!(state.phase(), EpisodePhase::Loading | EpisodePhase::Active)
        {
            return Err(CANCELLED.into());
        }
        let notify = state.service_updates.clone();
        let waker = state.driver.take();
        drop(state);
        if let Some(notify) = notify {
            notify();
        }
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(())
    }
    /// Dynamically publish a service through an owned provider child. Its
    /// explicit owner-anchor dependency keeps owner resources alive until all
    /// consumers drain. It becomes available after owner initialization lands.
    pub fn publish<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<ServiceHandle<T>, CallbackError> {
        self.publish_inner(key, value, None)
    }
    pub fn publish_checked<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<ServiceHandle<T>, CallbackError> {
        self.publish_inner(key, value, Some(typed_check(check)))
    }
    pub(super) fn publish_inner<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: Option<ServiceCheck>,
    ) -> Result<ServiceHandle<T>, CallbackError> {
        self.require_dynamic("publish")?;
        self.ensure_active()?;
        let slot = {
            let state = lock(&self.state);
            ServiceSlot::from_execution(&state.cleanups.protocol, Arc::new(value), check)
        };
        let supplied = slot.clone();
        let mut plugin = Plugin::new(format!("service:{}", key.name), move |setup| {
            setup.inner.provide_slot(key, supplied.clone())
        })
        .provides(key);
        plugin.dependencies.push(self.state.anchor.key);
        let status = {
            let state = lock(&self.state);
            EffectHandle {
                status: Arc::new(Mutex::new(EffectStatus {
                    checked: Some(state.cleanups.protocol.service_status()),
                    episode: Arc::downgrade(&self.state),
                    notify: state.dynamic_host.clone(),
                    ..EffectStatus::default()
                })),
            }
        };
        let child = self.mount_request(&self.state.context, plugin, Some(status.clone()))?;
        Ok(ServiceHandle {
            child,
            slot,
            status,
            marker: PhantomData,
        })
    }
    pub fn on_cleanup(
        &self,
        cleanup: impl FnOnce() -> CallbackResult + Send + 'static,
    ) -> CallbackResult {
        self.on_cleanup_async(move || async move { cleanup() })
    }
    pub fn on_cleanup_async<F, Fut>(&self, cleanup: F) -> CallbackResult
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.register_inverse(Inverse::new_async(cleanup))
    }
    pub fn on_cleanup_retryable(
        &self,
        cleanup: impl FnMut() -> CallbackResult + Send + 'static,
    ) -> CallbackResult {
        self.register_inverse(Inverse::retryable(cleanup))
    }
    pub fn on_cleanup_retryable_async<F, Fut>(&self, cleanup: F) -> CallbackResult
    where
        F: FnMut() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.register_inverse(Inverse::retryable_async(cleanup))
    }
    pub(super) fn register_inverse(&self, inverse: Inverse) -> CallbackResult {
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        if !state.cleanups.contains(self.scope.group()) {
            return Err("effect group has completed".into());
        }
        state
            .cleanups
            .push(self.scope.group(), CleanupAction::Callback(inverse.0));
        let waker = state.driver.take();
        drop(state);
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(())
    }
    pub fn mount(&self, plugin: Plugin) -> Result<ChildHandle, CallbackError> {
        self.mount_in(&self.state.context, plugin)
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
        self.require_dynamic("mount")?;
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        if state.phase() == EpisodePhase::Restoring
            || !state
                .cleanups
                .protocol
                .accepts_acquisition(self.scope.group())
        {
            return Err(CANCELLED.into());
        }
        if !state.cleanups.contains(self.scope.group()) {
            return Err("effect group has completed".into());
        }
        let handle = if state.cleanups.protocol.lifecycle_ticket().is_some() {
            let error = Arc::new(Mutex::new(None));
            let request = NativeChildInput {
                context: context.clone(),
                plugin,
                service,
                error: error.clone(),
            };
            match state
                .cleanups
                .protocol
                .enqueue_native_child(self.scope.group(), request)
            {
                Ok((slot, _token)) => ChildHandle {
                    state: ChildState::Native { slot, error },
                    external: None,
                },
                Err(rejected) => {
                    drop(state);
                    drop(rejected);
                    return Err("child request admission is closed or exhausted".into());
                }
            }
        } else {
            let identity = ChildState::External(Arc::new(Mutex::new(Ok(None))));
            let external = state.dynamic_host.as_ref().map(|notify| {
                static_host::StaticChildControl::new(
                    self.state.services.owner(),
                    self.state.generation,
                    identity.clone(),
                    service.clone(),
                    notify.clone(),
                )
            });
            let handle = ChildHandle {
                state: identity,
                external,
            };
            let request = ChildDispatch::External(ExternalChildRequest {
                context: context.clone(),
                plugin,
                handle: handle.clone(),
            });
            if let Err(rejected) = state.cleanups.protocol.enqueue_owned_child(
                self.scope.group(),
                request,
                CleanupAction::External(handle.clone()),
            ) {
                drop(state);
                drop(rejected);
                return Err("child request admission is closed or exhausted".into());
            }
            handle
        };
        if let Some(control) = &handle.external {
            state.external_children.push(control.clone());
        }
        let notify = state.dynamic_host.clone();
        let waker = state.driver.take();
        drop(state);
        if let Some(notify) = notify {
            notify();
        }
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(handle)
    }
    pub fn effect(&self, effect: impl EffectIterator) -> Result<EffectHandle, CallbackError> {
        self.require_dynamic("effect")?;
        let mut state = lock(&self.state);
        self.check_live(&state)?;
        if state.phase() == EpisodePhase::Restoring
            || !state
                .cleanups
                .protocol
                .accepts_acquisition(self.scope.group())
        {
            return Err(CANCELLED.into());
        }
        if !state.cleanups.contains(self.scope.group()) {
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
        let admitted = match &self.state.services {
            SetupServices::Native(_) => {
                state
                    .cleanups
                    .protocol
                    .enqueue_native_effect(self.scope.group(), domain, payload)
            }
            SetupServices::External(context) => state
                .cleanups
                .protocol
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
                .cleanups
                .protocol
                .effect_status(group)
                .expect("native effect admission allocated its real cleanup group"),
        );
        let waker = state.driver.take();
        drop(state);
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(handle)
    }
}

impl Setup<'_> {
    /// Retain a checked inverse for a native service payload replacement.
    #[track_caller]
    pub fn replace_service<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
    ) -> CallbackResult {
        self.inner.replace_service(key, value)
    }

    pub fn owner(&self) -> PluginId {
        self.inner.owner()
    }
    pub fn context(&self) -> &Context {
        self.inner.context()
    }
    pub fn to_async(&self) -> AsyncSetup {
        self.inner.clone()
    }
    #[track_caller]
    pub fn get<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
    ) -> Result<Arc<T>, ServiceReadError> {
        self.inner.get(key)
    }
    /// Read the same committed binding as `get`, with an explicit required-read name.
    #[track_caller]
    pub fn require<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
    ) -> Result<Arc<T>, ServiceReadError> {
        self.inner.require(key)
    }
    #[track_caller]
    pub fn observe_reversible(
        &self,
        key: ServiceKey<ReversibleValue>,
    ) -> Result<cordis_kernel::reversible_value::Snapshot, ServiceReadError> {
        self.inner.observe_reversible(key)
    }
    pub fn provide<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<Arc<T>, CallbackError> {
        self.inner.provide(key, value)
    }
    pub fn provide_checked<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<Arc<T>, CallbackError> {
        self.inner.provide_checked(key, value, check)
    }
    pub fn publish<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<ServiceHandle<T>, CallbackError> {
        self.inner.publish(key, value)
    }
    pub fn publish_checked<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<ServiceHandle<T>, CallbackError> {
        self.inner.publish_checked(key, value, check)
    }
    pub fn refresh(&self) -> CallbackResult {
        self.inner.refresh()
    }
    #[track_caller]
    pub fn update_reversible(
        &mut self,
        key: ServiceKey<ReversibleValue>,
        operation: ValueOperation,
    ) -> Result<ValueOutcome, CallbackError> {
        self.inner.update_reversible(key, operation)
    }
    pub fn update_reversible_with<E: ScalarEffect>(
        &mut self,
        key: ServiceKey<ReversibleValue>,
        effect: E,
    ) -> Result<ValueOutcome, CallbackError> {
        self.inner.update_reversible_with(key, effect)
    }
    #[track_caller]
    pub fn start_value_program(
        &self,
        key: ServiceKey<ReversibleValue>,
        program: ValueProgram,
    ) -> Result<ValueProgramCursor, CallbackError> {
        self.inner.start_value_program(key, program)
    }
    #[track_caller]
    pub fn capture_reversible(
        &self,
        key: ServiceKey<ReversibleValue>,
    ) -> Result<ValueServiceBinding, ServiceReadError> {
        self.inner.capture_reversible(key)
    }
    pub fn advance_value_program(
        &self,
        cursor: &mut ValueProgramCursor,
    ) -> Result<Option<ValueOutcome>, CallbackError> {
        self.inner.advance_value_program(cursor)
    }
    #[track_caller]
    pub fn run_value_program(
        &mut self,
        key: ServiceKey<ReversibleValue>,
        program: &ValueProgram,
    ) -> Result<Vec<ValueOutcome>, CallbackError> {
        self.inner.run_value_program(key, program)
    }
    /// Run a checked multi-service body in this root, Child or effect group.
    #[track_caller]
    pub fn run_service_program(
        &mut self,
        instructions: &[ServiceInstruction],
    ) -> Result<Vec<ValueOutcome>, CallbackError> {
        self.inner.run_service_program(instructions)
    }
    pub fn set<T: Any + Send + Sync>(&mut self, key: ServiceKey<T>, value: T) -> CallbackResult {
        self.inner.set(key, value)
    }
    pub fn on_cleanup(&mut self, cleanup: impl FnOnce() -> CallbackResult + Send + 'static) {
        self.inner
            .on_cleanup(cleanup)
            .expect("live synchronous setup");
    }
    pub fn on_cleanup_async<F, Fut>(&mut self, cleanup: F)
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.inner
            .on_cleanup_async(cleanup)
            .expect("live synchronous setup");
    }
    pub fn on_cleanup_retryable(
        &mut self,
        cleanup: impl FnMut() -> CallbackResult + Send + 'static,
    ) {
        self.inner
            .on_cleanup_retryable(cleanup)
            .expect("live synchronous setup");
    }
    pub fn on_cleanup_retryable_async<F, Fut>(&mut self, cleanup: F)
    where
        F: FnMut() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.inner
            .on_cleanup_retryable_async(cleanup)
            .expect("live synchronous setup");
    }
    pub fn mount(&mut self, plugin: Plugin) -> Result<ChildHandle, CallbackError> {
        self.inner.mount(plugin)
    }
    pub fn mount_in(
        &mut self,
        context: &Context,
        plugin: Plugin,
    ) -> Result<ChildHandle, CallbackError> {
        self.inner.mount_in(context, plugin)
    }
    pub fn effect(&mut self, effect: impl EffectIterator) -> Result<EffectHandle, CallbackError> {
        self.inner.effect(effect)
    }
}
