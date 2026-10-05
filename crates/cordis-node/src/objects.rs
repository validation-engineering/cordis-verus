//! Explicit objects and callbacks. Identities never appear inside JSON DTOs.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum ObjectOwnership {
    Borrowed,
    Owned,
}
/// A validated interface. The defining language retains the actual object.
#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ObjectDescriptor {
    type_name: String,
    methods: Vec<String>,
    ownership: ObjectOwnership,
}
impl ObjectDescriptor {
    pub fn new(
        type_name: impl Into<String>,
        methods: impl IntoIterator<Item = impl Into<String>>,
        ownership: ObjectOwnership,
    ) -> PluginResult<Self> {
        let type_name = type_name.into();
        let methods = methods.into_iter().map(Into::into).collect::<Vec<_>>();
        let mut names = std::collections::BTreeSet::new();
        if type_name.is_empty()
            || methods.is_empty()
            || methods.iter().any(|m| m.is_empty() || !names.insert(m))
        {
            return Err("InvalidObjectDescriptor".into());
        }
        Ok(Self {
            type_name,
            methods,
            ownership,
        })
    }
    pub fn callback(
        type_name: impl Into<String>,
        ownership: ObjectOwnership,
    ) -> PluginResult<Self> {
        Self::new(type_name, ["call"], ownership)
    }
    pub fn type_name(&self) -> &str {
        &self.type_name
    }
    pub fn methods(&self) -> &[String] {
        &self.methods
    }
    pub fn ownership(&self) -> ObjectOwnership {
        self.ownership
    }
    pub(super) fn from_value(value: Value) -> PluginResult<Self> {
        #[derive(Deserialize)]
        #[serde(rename_all = "camelCase", deny_unknown_fields)]
        struct Raw {
            type_name: String,
            methods: Vec<String>,
            ownership: String,
        }
        let raw: Raw = serde_json::from_value(value).map_err(|_| "InvalidObjectDescriptor")?;
        let ownership = match raw.ownership.as_str() {
            "borrowed" => ObjectOwnership::Borrowed,
            "owned" => ObjectOwnership::Owned,
            _ => return Err("InvalidObjectDescriptor".into()),
        };
        Self::new(raw.type_name, raw.methods, ownership)
    }
}
/// Calls may overlap. Each call has its own cancellation token. An owned
/// object's close hook runs only after all admitted calls and their RPCs land.
/// Borrowed release drops the adapter reference without invoking this hook;
/// its referent must remain owned by the plugin or another explicit owner.
pub trait PluginObject: Send + Sync + 'static {
    fn descriptor(&self) -> ObjectDescriptor;
    fn call(&self, ctx: PluginContext, method: &str, args: Value) -> PluginFuture;
    fn close(&self, _ctx: PluginContext) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
}
/// A JS object capability scoped to one managed Rust action. Cloning this value
/// does not transfer ownership or extend that action's admission lifetime.
#[derive(Clone)]
pub struct JsObject {
    context: PluginContext,
    object: String,
    descriptor: ObjectDescriptor,
}
impl JsObject {
    pub fn descriptor(&self) -> &ObjectDescriptor {
        &self.descriptor
    }
    pub async fn call(&self, method: &str, args: Value) -> PluginResult<Value> {
        if !self.context.cleanup {
            self.context.cancellation.check()?;
        }
        if !args.is_array() {
            return Err("ArgumentsMustBeJsonArray".into());
        }
        let reply = {
            let mut transport = self.context.transport.lock().unwrap();
            if !self.context.alive.load(Ordering::Acquire) {
                return Err("ActionClosed".into());
            }
            let state = transport
                .foreign_objects
                .get(&self.object)
                .ok_or("UnknownObject")?;
            if state.session != self.context.session || state.job != self.context.job {
                return Err("WrongObjectOwner".into());
            }
            if state.closing {
                return Err("ObjectClosed".into());
            }
            if !state.descriptor.methods.iter().any(|m| m == method) {
                return Err("UndeclaredObjectMethod".into());
            }
            let service = state.service.clone();
            self.context.enqueue(
                &mut transport,
                "object_call",
                &service,
                Some(method.into()),
                Some(args),
                Some(ResourceReference::Object(self.object.clone())),
            )?
        };
        (self.context.notify)();
        reply.await
    }
    /// Await this object's calls before explicit close. A still pending call
    /// returns ObjectBusy without changing admission, preventing a cloned
    /// capability from waiting for its own reverse-call chain. The owning
    /// action's journal still joins such calls before automatic disposal.
    pub async fn close(&self) -> PluginResult<()> {
        self.context.close_js_object(&self.object, false).await
    }
}
/// A named callback adapter, rather than a function hidden in a JSON argument.
#[derive(Clone)]
pub struct JsCallback(JsObject);
impl JsCallback {
    pub fn descriptor(&self) -> &ObjectDescriptor {
        self.0.descriptor()
    }
    pub async fn invoke(&self, args: Value) -> PluginResult<Value> {
        self.0.call("call", args).await
    }
    pub async fn close(&self) -> PluginResult<()> {
        self.0.close().await
    }
}
#[derive(Clone)]
pub(super) struct ForeignObject {
    pub session: u64,
    pub job: u64,
    pub service: String,
    pub descriptor: ObjectDescriptor,
    pub order: u64,
    pub closing: bool,
    pub close_pending: bool,
    pub failed: Option<String>,
}
#[derive(Clone, Copy)]
pub(super) enum ObjectAction {
    Call(u64),
    Close(u64),
}
pub(super) struct RustObject {
    pub session: u64,
    pub service: String,
    pub publication: usize,
    pub port: cordis_driver::ServicePort,
    pub caller: Option<(usize, u64)>,
    pub descriptor: ObjectDescriptor,
    pub implementation: Arc<dyn PluginObject>,
    pub calls: std::collections::BTreeSet<u64>,
    pub close: Option<u64>,
    pub closing: bool,
}
impl PluginContext {
    pub async fn open_object(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<JsObject> {
        if !self.cleanup {
            self.cancellation.check()?;
        }
        if !self.descriptor.inject.iter().any(|s| s == service) {
            return Err("UndeclaredInjection".into());
        }
        if !args.is_array() {
            return Err("ArgumentsMustBeJsonArray".into());
        }
        let value = self
            .request("object_open", service, Some(method.into()), Some(args))?
            .await?;
        let object = value
            .get("object")
            .and_then(Value::as_str)
            .ok_or("InvalidObjectReply")?
            .to_owned();
        let descriptor = ObjectDescriptor::from_value(
            value
                .get("descriptor")
                .cloned()
                .ok_or("InvalidObjectReply")?,
        )?;
        Ok(JsObject {
            context: self.clone(),
            object,
            descriptor,
        })
    }
    pub async fn open_callback(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<JsCallback> {
        let object = self.open_object(service, method, args).await?;
        if object.descriptor.methods != ["call"] {
            return Err("InvalidCallbackDescriptor".into());
        }
        Ok(JsCallback(object))
    }
    async fn close_js_object(&self, object: &str, join_calls: bool) -> PluginResult<()> {
        // Close admission before joining calls. Unlike stream return, the
        // destructor is never used to wake a pending business operation.
        let reply = std::future::poll_fn(|cx| {
            let mut transport = self.transport.lock().unwrap();
            if !self.alive.load(Ordering::Acquire) {
                return Poll::Ready(Err("ActionClosed".into()));
            }
            let Some(state) = transport.foreign_objects.get(object) else {
                return Poll::Ready(Ok(None));
            };
            if state.session != self.session || (state.job != self.job && !self.cleanup) {
                return Poll::Ready(Err("WrongObjectOwner".into()));
            }
            let pending_calls = transport
                .pending
                .values()
                .any(|r| r.kind == "object_call" && r.object.as_deref() == Some(object));
            if state.close_pending || (pending_calls && !join_calls) {
                return Poll::Ready(Err("ObjectBusy".into()));
            }
            let service = state.service.clone();
            transport.foreign_objects.get_mut(object).unwrap().closing = true;
            if pending_calls {
                if !transport.waiters.iter().any(|w| w.will_wake(cx.waker())) {
                    transport.waiters.push(cx.waker().clone());
                }
                return Poll::Pending;
            }
            let mut control = self.clone();
            control.cleanup = true;
            match control.enqueue(
                &mut transport,
                "object_close",
                &service,
                None,
                None,
                Some(ResourceReference::Object(object.into())),
            ) {
                Ok(reply) => {
                    let state = transport.foreign_objects.get_mut(object).unwrap();
                    state.close_pending = true;
                    state.failed = None;
                    Poll::Ready(Ok(Some(reply)))
                }
                Err(error) => Poll::Ready(Err(error)),
            }
        })
        .await?;
        if let Some(reply) = reply {
            (self.notify)();
            reply.await?;
        }
        Ok(())
    }
    pub(super) async fn drain_js_objects(
        &self,
        job: Option<u64>,
        retry: bool,
    ) -> PluginResult<Value> {
        loop {
            let next = std::future::poll_fn(|cx| {
                let mut transport = self.transport.lock().unwrap();
                // Finish all admissions before choosing the most recently
                // acquired object; a late open must not reverse cleanup order.
                let opening = transport.pending.values().any(|r| {
                    r.session == self.session
                        && job.is_none_or(|j| r.job == j)
                        && r.kind == "object_open"
                });
                if !opening {
                    let next = transport
                        .foreign_objects
                        .iter()
                        .filter(|(_, o)| {
                            o.session == self.session && job.is_none_or(|j| o.job == j)
                        })
                        .max_by_key(|(_, o)| o.order);
                    if let Some((id, state)) = next {
                        if !state.close_pending {
                            return Poll::Ready(Some((id.clone(), state.failed.clone())));
                        }
                    } else {
                        return Poll::Ready(None);
                    }
                }
                if !transport.waiters.iter().any(|w| w.will_wake(cx.waker())) {
                    transport.waiters.push(cx.waker().clone());
                }
                Poll::Pending
            })
            .await;
            let Some((object, failed)) = next else {
                return Ok(Value::Null);
            };
            if !retry {
                if let Some(error) = failed {
                    return Err(error);
                }
            }
            self.close_js_object(&object, true).await?;
        }
    }
    pub(super) async fn drain_js_resources(
        &self,
        job: Option<u64>,
        retry: bool,
    ) -> PluginResult<Value> {
        self.drain_js_streams(job, retry).await?;
        self.drain_js_objects(job, retry).await
    }
}
impl Backend {
    pub(super) fn open_rust_object(
        &mut self,
        session: u64,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<Value> {
        let instance = self
            .sessions
            .get(&session)
            .ok_or("UnknownSession")?
            .instance
            .clone();
        let (publication, port) = self.binding(session, service)?;
        let next = self.next_object.checked_add(1).ok_or("ObjectCapacity")?;
        let implementation = instance.open_object(service, method, args)?;
        let descriptor = implementation.descriptor();
        self.owned_objects
            .retain(|object| object.strong_count() > 0);
        let identity = Arc::downgrade(&implementation);
        if self
            .owned_objects
            .iter()
            .any(|object| object.ptr_eq(&identity))
            || (descriptor.ownership == ObjectOwnership::Owned
                && self
                    .objects
                    .values()
                    .any(|object| Arc::ptr_eq(&object.implementation, &implementation)))
        {
            return Err("ObjectOwnershipConflict".into());
        }
        if descriptor.ownership == ObjectOwnership::Owned {
            self.owned_objects.push(identity);
        }
        self.next_object = next;
        self.objects.insert(
            next,
            RustObject {
                session,
                service: service.into(),
                publication,
                port,
                caller: None,
                descriptor: descriptor.clone(),
                implementation,
                calls: Default::default(),
                close: None,
                closing: false,
            },
        );
        Ok(serde_json::json!({"object": next.to_string(), "descriptor": descriptor}))
    }
    pub fn bind_object(&mut self, object: u64, caller: Option<(usize, u64)>) -> PluginResult<()> {
        self.objects.get_mut(&object).ok_or("UnknownObject")?.caller = caller;
        Ok(())
    }
    pub fn object_binding(
        &self,
        session: u64,
        object: u64,
        caller: Option<(usize, u64)>,
    ) -> PluginResult<(String, usize, cordis_driver::ServicePort)> {
        let resource = self.objects.get(&object).ok_or("UnknownObject")?;
        if resource.session != session || resource.caller != caller {
            return Err("WrongObjectOwner".into());
        }
        Ok((
            resource.service.clone(),
            resource.publication,
            resource.port,
        ))
    }
    pub fn object_call(
        &mut self,
        session: u64,
        object: u64,
        method: &str,
        args: Value,
        restoring: bool,
        continuing: bool,
    ) -> PluginResult<Value> {
        if !args.is_array() {
            return Err("ArgumentsMustBeJsonArray".into());
        }
        let resource = self.objects.get(&object).ok_or("UnknownObject")?;
        if resource.session != session {
            return Err("WrongObjectOwner".into());
        }
        if resource.closing {
            return Err("ObjectClosed".into());
        }
        if !resource.descriptor.methods.iter().any(|m| m == method) {
            return Err("UndeclaredObjectMethod".into());
        }
        let implementation = resource.implementation.clone();
        let s = self.sessions.get(&session).ok_or("UnknownSession")?;
        if !restoring && !continuing {
            s.cancellation.check()?;
        }
        let cancelled = s.cancellation.is_cancelled();
        let job = self.job_id()?;
        let ctx = self.context(session, job, restoring)?;
        if cancelled && !restoring {
            ctx.cancellation.cancel();
        }
        let future = implementation.call(ctx.clone(), method, args);
        self.add_job(ctx, JobKind::Call, future);
        self.jobs.get_mut(&job).unwrap().object = Some(ObjectAction::Call(object));
        self.objects.get_mut(&object).unwrap().calls.insert(job);
        Ok(serde_json::json!({"job":job.to_string()}))
    }
    pub fn object_close(&mut self, session: u64, object: u64) -> PluginResult<Value> {
        let Some(resource) = self.objects.get(&object) else {
            if object > 0 && object <= self.next_object {
                return Ok(serde_json::json!({"closed":true}));
            }
            return Err("UnknownObject".into());
        };
        if resource.session != session {
            return Err("WrongObjectOwner".into());
        }
        if let Some(job) = resource.close {
            return Ok(serde_json::json!({"job":job.to_string()}));
        }
        let implementation = resource.implementation.clone();
        let owned = resource.descriptor.ownership == ObjectOwnership::Owned;
        let calls = resource.calls.iter().copied().collect::<Vec<_>>();
        let landings = calls
            .iter()
            .filter_map(|id| self.jobs.get(id))
            .map(|j| j.landing.clone())
            .collect::<Vec<_>>();
        let job = self.job_id()?;
        let ctx = self.context(session, job, true)?;
        let close_ctx = ctx.clone();
        for call in calls {
            self.cancel_job(call)?;
        }
        self.add_job(
            ctx,
            JobKind::ResourceClose,
            Box::pin(async move {
                for landing in landings {
                    landing.wait().await;
                }
                if owned {
                    implementation.close(close_ctx).await
                } else {
                    Ok(Value::Null)
                }
            }),
        );
        self.jobs.get_mut(&job).unwrap().object = Some(ObjectAction::Close(object));
        let resource = self.objects.get_mut(&object).unwrap();
        resource.closing = true;
        resource.close = Some(job);
        Ok(serde_json::json!({"job":job.to_string()}))
    }
    pub(super) fn object_landed(&mut self, action: ObjectAction, job: u64, success: bool) {
        match action {
            ObjectAction::Call(object) => {
                if let Some(resource) = self.objects.get_mut(&object) {
                    resource.calls.remove(&job);
                }
            }
            ObjectAction::Close(object) => {
                if success {
                    self.objects.remove(&object);
                } else if let Some(resource) = self.objects.get_mut(&object) {
                    resource.close = None;
                }
            }
        }
    }
}
