//! NAPI-facing routing, separate from the graph borrow and Rust future polling.
use crate::{
    plugin::{Backend, FactoryRegistry, ResolvedImport},
    NativeDriver,
};
use cordis_driver::{ActionKind, ActionTicket};
use napi::{
    bindgen_prelude::Function,
    threadsafe_function::{ThreadsafeFunction, ThreadsafeFunctionCallMode},
    Env, Error, Result, Status,
};
use serde::Deserialize;
use serde_json::{json, Value};
use std::cell::RefCell;
use std::sync::{Arc, Mutex};

type WakeCallback = ThreadsafeFunction<(), (), (), Status, false, true>;
pub(crate) type WakeSlot = Arc<Mutex<Option<WakeCallback>>>;
pub(crate) fn backend(registry: FactoryRegistry) -> (RefCell<Backend>, WakeSlot) {
    let slot: WakeSlot = Arc::new(Mutex::new(None));
    let wake = slot.clone();
    let notify = Arc::new(move || {
        if let Some(callback) = wake.lock().unwrap().as_ref() {
            callback.call((), ThreadsafeFunctionCallMode::NonBlocking);
        }
    });
    (RefCell::new(Backend::new(registry, notify)), slot)
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Caller {
    id: String,
    generation: String,
    ticket: Option<ActionTicket>,
    authority: Option<Authority>,
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Authority {
    session: String,
    job: String,
    request: String,
}
#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
enum Request {
    Start {
        ticket: ActionTicket,
        factory: String,
        config: Value,
        #[serde(default)]
        ports: std::collections::BTreeMap<String, cordis_driver::ServicePort>,
    },
    Forget {
        id: String,
    },
    Cleanup {
        ticket: ActionTicket,
        session: String,
    },
    Call {
        session: String,
        service: String,
        method: String,
        args: Value,
        caller: Option<Caller>,
    },
    ObjectCall {
        session: String,
        object: String,
        method: String,
        args: Value,
        caller: Option<Caller>,
    },
    ObjectClose {
        session: String,
        object: String,
    },
    StreamNext {
        session: String,
        stream: String,
        caller: Option<Caller>,
    },
    StreamClose {
        session: String,
        stream: String,
    },
    Reply {
        request: String,
        success: bool,
        #[serde(default)]
        value: Value,
        error: Option<String>,
    },
    Cancel {
        session: String,
    },
    CancelJob {
        job: String,
    },
    Release {
        session: String,
    },
    Poll,
    Close,
}
fn identity<T: std::str::FromStr>(text: &str) -> std::result::Result<T, String> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
        return Err("InvalidIdentity".into());
    }
    text.parse().map_err(|_| "InvalidIdentity".into())
}
fn plugin_error(message: impl ToString) -> Error {
    Error::new(Status::InvalidArg, message.to_string())
}
impl NativeDriver {
    /// Embed an arbitrary set of statically linked Rust factories. Custom addons
    /// may export a createDriver function returning this object. No second graph
    /// or Rust Runtime is constructed by the plugin executor.
    pub fn with_factories(registry: FactoryRegistry) -> Result<Self> {
        let (backend, wake) = backend(registry);
        Ok(Self {
            driver: RefCell::new(cordis_driver::Driver::new().map_err(plugin_error)?),
            faulted: std::cell::Cell::new(false),
            backend,
            wake,
        })
    }
    fn valid_ticket(
        &self,
        ticket: &ActionTicket,
        kind: ActionKind,
    ) -> std::result::Result<(), String> {
        let driver = self.driver.try_borrow().map_err(|_| "ReentrantCommand")?;
        if ticket.domain != driver.domain() || ticket.kind != kind {
            return Err("StaleAction".into());
        }
        let expected = serde_json::to_value(ticket).map_err(|e| e.to_string())?;
        if driver.snapshot()["plugins"]
            .as_array()
            .unwrap()
            .iter()
            .any(|node| node["pendingAction"] == expected)
        {
            Ok(())
        } else {
            Err("StaleAction".into())
        }
    }
    fn call_access(
        &self,
        session: u64,
        service: &str,
        caller: &Option<Caller>,
        captured: Option<(usize, cordis_driver::ServicePort)>,
    ) -> std::result::Result<(bool, bool), String> {
        let (owner, generation, publication, port) = {
            let backend = self
                .backend
                .try_borrow()
                .map_err(|_| "ReentrantRustAction")?;
            let (owner, generation) = backend.owner(session)?;
            let (publication, port) = match captured {
                Some(binding) => binding,
                None => backend.binding(session, service)?,
            };
            (owner, generation, publication, port)
        };
        let (restoring, continuing) = {
            let driver = self.driver.try_borrow().map_err(|_| "ReentrantCommand")?;
            let mut restored = false;
            let mut continuation = false;
            let resolved = if let Some(caller) = caller.as_ref() {
                let id = identity(&caller.id)?;
                let caller_generation = identity(&caller.generation)?;
                if let Some(ticket) = &caller.ticket {
                    if ticket.id != id || ticket.generation != caller_generation {
                        return Err("StaleEpisode".into());
                    }
                    self.valid_ticket(ticket, ActionKind::Cleanup)?;
                    restored = true;
                }
                if let Some(authority) = &caller.authority {
                    let backend = self
                        .backend
                        .try_borrow()
                        .map_err(|_| "ReentrantRustAction")?;
                    let session = identity(&authority.session)?;
                    let job = identity(&authority.job)?;
                    let (source, source_generation, restoring_authority) =
                        backend.request_authority(session, job, identity(&authority.request)?)?;
                    drop(backend);
                    if !driver
                        .committed_reaches(source, source_generation, id)
                        .map_err(|e| e.to_string())?
                    {
                        return Err("InvalidAuthority".into());
                    }
                    restored |= restoring_authority;
                    continuation = true;
                }
                if !restored && !continuation {
                    driver
                        .validate(id, caller_generation)
                        .map_err(|e| e.to_string())?;
                }
                let bound = driver
                    .resolve(port, Some(id), Some(caller_generation))
                    .map_err(|e| e.to_string())?;
                if bound.is_some() {
                    bound
                } else {
                    driver
                        .validate(id, caller_generation)
                        .map_err(|e| e.to_string())?;
                    driver
                        .resolve(port, None, None)
                        .map_err(|e| e.to_string())?
                }
            } else {
                driver
                    .resolve(port, None, None)
                    .map_err(|e| e.to_string())?
            };
            let binding = resolved.ok_or("StalePublication")?;
            if binding["owner"]
                .as_str()
                .and_then(|s| s.parse::<usize>().ok())
                != Some(owner)
                || binding["publication"]
                    .as_str()
                    .and_then(|s| s.parse::<usize>().ok())
                    != Some(publication)
            {
                return Err("StalePublication".into());
            }
            // A committed consumer may call its old provider throughout
            // withdrawal. New unowned lookups above see active owners only.
            (
                restored,
                continuation || driver.validate(owner, generation).is_err(),
            )
        };
        Ok((restoring, continuing))
    }
    fn caller_identity(
        caller: &Option<Caller>,
    ) -> std::result::Result<Option<(usize, u64)>, String> {
        caller
            .as_ref()
            .map(|c| Ok((identity(&c.id)?, identity(&c.generation)?)))
            .transpose()
    }
    fn native_request(&self, request: Request) -> std::result::Result<Value, String> {
        match request {
            Request::Start {
                ticket,
                factory,
                config,
                ports,
            } => {
                self.valid_ticket(&ticket, ActionKind::Setup)?;
                let descriptor = self
                    .backend
                    .try_borrow()
                    .map_err(|_| "ReentrantRustAction")?
                    .typed_descriptor(&factory, &ports)?;
                if descriptor.is_none() {
                    return self
                        .backend
                        .try_borrow_mut()
                        .map_err(|_| "ReentrantRustAction")?
                        .start(ticket.id, ticket.generation, &factory, config);
                }
                let mut imports = Vec::new();
                if let Some(descriptor) = descriptor {
                    let driver = self.driver.try_borrow().map_err(|_| "ReentrantCommand")?;
                    for name in descriptor.inject {
                        let port = ports[&name];
                        let binding = driver
                            .resolve(port, Some(ticket.id), Some(ticket.generation))
                            .map_err(|e| e.to_string())?
                            .ok_or("TypedImportUnavailable")?;
                        imports.push(ResolvedImport {
                            name,
                            port,
                            owner: identity(
                                binding["owner"].as_str().ok_or("InvalidPublication")?,
                            )?,
                            publication: identity(
                                binding["publication"]
                                    .as_str()
                                    .ok_or("InvalidPublication")?,
                            )?,
                        });
                    }
                }
                self.backend
                    .try_borrow_mut()
                    .map_err(|_| "ReentrantRustAction")?
                    .start_resolved(
                        ticket.id,
                        ticket.generation,
                        &factory,
                        config,
                        ports,
                        imports,
                    )
            }
            Request::Forget { id } => {
                let id = identity(&id)?;
                let exists = self
                    .driver
                    .try_borrow()
                    .map_err(|_| "ReentrantCommand")?
                    .snapshot()["plugins"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|node| {
                        node["id"].as_str().and_then(|s| s.parse::<usize>().ok()) == Some(id)
                    });
                if exists {
                    return Err("TypedDefinitionStillMounted".into());
                }
                self.backend
                    .try_borrow_mut()
                    .map_err(|_| "ReentrantRustAction")?
                    .forget_typed(id)?;
                Ok(json!({}))
            }
            Request::Cleanup { ticket, session } => {
                self.valid_ticket(&ticket, ActionKind::Cleanup)?;
                let session = identity(&session)?;
                let mut backend = self
                    .backend
                    .try_borrow_mut()
                    .map_err(|_| "ReentrantRustAction")?;
                if backend.owner(session)? != (ticket.id, ticket.generation) {
                    return Err("StaleEpisode".into());
                }
                backend.cleanup(session)
            }
            Request::Call {
                session,
                service,
                method,
                args,
                caller,
            } => {
                if !args.is_array() {
                    return Err("ArgumentsMustBeJsonArray".into());
                }
                let session = identity(&session)?;
                let (restoring, continuing) = self.call_access(session, &service, &caller, None)?;
                if self
                    .backend
                    .try_borrow()
                    .map_err(|_| "ReentrantRustAction")?
                    .is_resource_method(session, &service, &method)?
                {
                    let (owner, generation) = self
                        .backend
                        .try_borrow()
                        .map_err(|_| "ReentrantRustAction")?
                        .owner(session)?;
                    let driver = self.driver.try_borrow().map_err(|_| "ReentrantCommand")?;
                    driver
                        .validate(owner, generation)
                        .map_err(|e| e.to_string())?;
                    if let Some((id, generation)) = Self::caller_identity(&caller)? {
                        driver.validate(id, generation).map_err(|e| e.to_string())?;
                    }
                    if restoring {
                        return Err("CleanupCannotAcquireResource".into());
                    }
                }
                let identity = Self::caller_identity(&caller)?;
                let mut backend = self
                    .backend
                    .try_borrow_mut()
                    .map_err(|_| "ReentrantRustAction")?;
                let reply =
                    backend.call(session, &service, &method, args, restoring, continuing)?;
                if let Some(stream) = reply.get("stream").and_then(Value::as_str) {
                    backend
                        .bind_stream(stream.parse().map_err(|_| "InvalidIdentity")?, identity)?;
                }
                if let Some(object) = reply.get("object").and_then(Value::as_str) {
                    backend
                        .bind_object(object.parse().map_err(|_| "InvalidIdentity")?, identity)?;
                }
                Ok(reply)
            }
            Request::ObjectCall {
                session,
                object,
                method,
                args,
                caller,
            } => {
                let session = identity(&session)?;
                let object = identity(&object)?;
                let (service, publication, port) = self
                    .backend
                    .try_borrow()
                    .map_err(|_| "ReentrantRustAction")?
                    .object_binding(session, object, Self::caller_identity(&caller)?)?;
                let (restoring, continuing) =
                    self.call_access(session, &service, &caller, Some((publication, port)))?;
                self.backend
                    .try_borrow_mut()
                    .map_err(|_| "ReentrantRustAction")?
                    .object_call(session, object, &method, args, restoring, continuing)
            }
            Request::ObjectClose { session, object } => self
                .backend
                .try_borrow_mut()
                .map_err(|_| "ReentrantRustAction")?
                .object_close(identity(&session)?, identity(&object)?),
            Request::StreamNext {
                session,
                stream,
                caller,
            } => {
                let session = identity(&session)?;
                let stream = identity(&stream)?;
                let caller_identity = Self::caller_identity(&caller)?;
                let (service, publication, port) = self
                    .backend
                    .try_borrow()
                    .map_err(|_| "ReentrantRustAction")?
                    .stream_binding(session, stream, caller_identity)?;
                let (restoring, continuing) =
                    self.call_access(session, &service, &caller, Some((publication, port)))?;
                self.backend
                    .try_borrow_mut()
                    .map_err(|_| "ReentrantRustAction")?
                    .stream_next(session, stream, restoring, continuing)
            }
            Request::StreamClose { session, stream } => self
                .backend
                .try_borrow_mut()
                .map_err(|_| "ReentrantRustAction")?
                .stream_close(identity(&session)?, identity(&stream)?),
            Request::Reply {
                request,
                success,
                value,
                error,
            } => {
                let result = if success {
                    Ok(value)
                } else {
                    Err(error.unwrap_or_else(|| "HostCallFailed".into()))
                };
                self.backend
                    .try_borrow_mut()
                    .map_err(|_| "ReentrantRustAction")?
                    .reply(identity(&request)?, result)?;
                Ok(json!({}))
            }
            Request::CancelJob { job } => {
                self.backend
                    .try_borrow_mut()
                    .map_err(|_| "ReentrantRustAction")?
                    .cancel_job(identity(&job)?)?;
                Ok(json!({}))
            }
            Request::Cancel { session } => {
                self.backend
                    .try_borrow_mut()
                    .map_err(|_| "ReentrantRustAction")?
                    .cancel(identity(&session)?)?;
                Ok(json!({}))
            }
            Request::Release { session } => {
                self.backend
                    .try_borrow_mut()
                    .map_err(|_| "ReentrantRustAction")?
                    .release(identity(&session)?)?;
                Ok(json!({}))
            }
            Request::Close => {
                if !self
                    .backend
                    .try_borrow()
                    .map_err(|_| "ReentrantRustAction")?
                    .can_close()
                {
                    return Err("SessionBusy".into());
                }
                *self.wake.lock().map_err(|_| "WakePoisoned")? = None;
                Ok(json!({}))
            }
            Request::Poll => Ok(self
                .backend
                .try_borrow_mut()
                .map_err(|_| "ReentrantRustAction")?
                .poll()),
        }
    }
    pub(crate) fn native_command(&self, env: Env, input: String) -> Result<String> {
        self.check_fault()?;
        let request: Request = serde_json::from_str(&input).map_err(plugin_error)?;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.native_request(request)
        }));
        let result = match result {
            Ok(result) => result.map_err(plugin_error),
            Err(payload) => {
                std::mem::forget(payload);
                self.faulted.set(true);
                if let Ok(mut wake) = self.wake.lock() {
                    *wake = None;
                }
                Err(Error::new(
                    Status::GenericFailure,
                    "DomainFaulted: Rust plugin panicked",
                ))
            }
        };
        self.update_wake_liveness(&env)?;
        result.and_then(|value| serde_json::to_string(&value).map_err(plugin_error))
    }
    pub(crate) fn install_wake(&self, env: Env, callback: Function<'_, (), ()>) -> Result<()> {
        self.check_fault()?;
        let callback = callback
            .build_threadsafe_function::<()>()
            .weak::<true>()
            .build()?;
        *self.wake.lock().map_err(plugin_error)? = Some(callback);
        self.update_wake_liveness(&env)
    }
    fn update_wake_liveness(&self, env: &Env) -> Result<()> {
        let busy = self.backend.try_borrow().map_err(plugin_error)?.busy();
        if let Some(callback) = self.wake.lock().map_err(plugin_error)?.as_mut() {
            // napi's deprecated wrappers remain its safe API for Node event-loop
            // liveness. Cloning a TSFN does not replace ref/unref semantics.
            #[allow(deprecated)]
            if busy {
                callback.refer(env)?;
            } else {
                callback.unref(env)?;
            }
        }
        Ok(())
    }
}
