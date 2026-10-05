//! Explicit pull streams. Stream objects stay in their defining language.
use super::*;

pub type StreamFuture = Pin<Box<dyn Future<Output = PluginResult<Option<Value>>> + Send + 'static>>;
/// One pull is admitted at a time. `close` is asynchronous and retryable; it is
/// not invoked until a cancelled, in-flight pull and its external calls land.
pub trait PluginStream: Send + Sync + 'static {
    fn next(&self, ctx: PluginContext) -> StreamFuture;
    /// Request cooperative cancellation only; do not destroy resources still
    /// used by a pending pull. The async close runs after that pull lands.
    fn cancel(&self) {}
    fn close(&self, _ctx: PluginContext) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
}
/// A JavaScript stream scoped to its opening Rust action. Explicit close is
/// available; a dropped or forgotten handle is drained by that action's journal.
#[derive(Clone)]
pub struct JsStream {
    context: PluginContext,
    stream: String,
}
impl JsStream {
    pub async fn next(&self) -> PluginResult<Option<Value>> {
        if !self.context.cleanup {
            self.context.cancellation.check()?;
        }
        let reply = self
            .context
            .stream_request("stream_next", &self.stream, true)?
            .await?;
        match reply.get("done").and_then(Value::as_bool) {
            Some(true) => Ok(None),
            Some(false) => Ok(Some(
                reply.get("value").cloned().ok_or("InvalidStreamReply")?,
            )),
            None => Err("InvalidStreamReply".into()),
        }
    }
    /// Finish the current next before explicitly closing. A pending next
    /// returns StreamBusy without changing admission, preventing a cloned
    /// capability from joining its own reverse-call chain. Framework cancel
    /// and the action journal can still return before joining an active next.
    pub async fn close(&self) -> PluginResult<()> {
        self.context.close_js_stream(&self.stream, false).await
    }
}
#[derive(Clone)]
pub(super) struct ForeignStream {
    pub session: u64,
    pub job: u64,
    pub service: String,
    pub pull: bool,
    pub closing: bool,
    pub close_pending: bool,
    pub failed: Option<String>,
}
#[derive(Default)]
pub(super) struct Landing {
    done: AtomicBool,
    waker: Mutex<Option<Waker>>,
}
impl Landing {
    pub async fn wait(&self) {
        std::future::poll_fn(|cx| {
            let mut waker = self.waker.lock().unwrap();
            if self.done.load(Ordering::Acquire) {
                Poll::Ready(())
            } else {
                *waker = Some(cx.waker().clone());
                Poll::Pending
            }
        })
        .await;
    }
    pub fn finish(&self) {
        self.done.store(true, Ordering::Release);
        let waker = self.waker.lock().unwrap().take();
        if let Some(waker) = waker {
            waker.wake();
        }
    }
}
#[derive(Clone, Copy)]
pub(super) enum StreamAction {
    Next(u64),
    Close(u64),
}
pub(super) struct RustStream {
    pub session: u64,
    pub service: String,
    pub publication: usize,
    pub port: cordis_driver::ServicePort,
    pub caller: Option<(usize, u64)>,
    pub implementation: Arc<dyn PluginStream>,
    pub pull: Option<u64>,
    pub close: Option<u64>,
    pub closing: bool,
}
impl PluginContext {
    pub async fn open_stream(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<JsStream> {
        if !self.cleanup {
            self.cancellation.check()?;
        }
        if !self.descriptor.inject.iter().any(|s| s == service) {
            return Err("UndeclaredInjection".into());
        }
        let value = self
            .request("stream_open", service, Some(method.into()), Some(args))?
            .await?;
        let stream = value
            .get("stream")
            .and_then(Value::as_str)
            .ok_or("InvalidStreamReply")?
            .to_owned();
        Ok(JsStream {
            context: self.clone(),
            stream,
        })
    }
    fn stream_request(
        &self,
        kind: &'static str,
        stream: &str,
        allow_pending_pull: bool,
    ) -> PluginResult<RequestFuture> {
        let mut transport = self.transport.lock().unwrap();
        if !self.alive.load(Ordering::Acquire) {
            return Err("ActionClosed".into());
        }
        let state = transport
            .foreign_streams
            .get(stream)
            .ok_or("UnknownStream")?;
        if state.session != self.session || (state.job != self.job && !self.cleanup) {
            return Err("WrongStreamOwner".into());
        }
        if kind == "stream_next" && (state.closing || state.pull) {
            return Err("StreamBusyOrClosed".into());
        }
        if kind == "stream_close" && (state.close_pending || (state.pull && !allow_pending_pull)) {
            return Err("StreamBusy".into());
        }
        let service = state.service.clone();
        let reply = self.enqueue(
            &mut transport,
            kind,
            &service,
            None,
            None,
            Some(ResourceReference::Stream(stream.into())),
        )?;
        let state = transport.foreign_streams.get_mut(stream).unwrap();
        if kind == "stream_next" {
            state.pull = true;
        } else {
            state.closing = true;
            state.close_pending = true;
            state.failed = None;
        }
        drop(transport);
        (self.notify)();
        Ok(reply)
    }
    async fn close_js_stream(&self, stream: &str, allow_pending_pull: bool) -> PluginResult<()> {
        // Only handles manufactured by open_stream can call this method. A
        // successfully closed identity cannot be reused by the JS resource table.
        if !self.alive.load(Ordering::Acquire) {
            return Err("ActionClosed".into());
        }
        if !self
            .transport
            .lock()
            .unwrap()
            .foreign_streams
            .contains_key(stream)
        {
            return Ok(());
        }
        self.stream_request("stream_close", stream, allow_pending_pull)?
            .await?;
        Ok(())
    }
    pub(super) async fn drain_js_streams(
        &self,
        job: Option<u64>,
        retry: bool,
    ) -> PluginResult<Value> {
        loop {
            let next = std::future::poll_fn(|cx| {
                let mut transport = self.transport.lock().unwrap();
                let next = transport
                    .foreign_streams
                    .iter()
                    .find(|(_, s)| s.session == self.session && job.is_none_or(|j| s.job == j));
                if let Some((id, state)) = next {
                    if !state.close_pending {
                        return Poll::Ready(Some((id.clone(), state.failed.clone())));
                    }
                } else if !transport.pending.values().any(|r| {
                    r.session == self.session
                        && job.is_none_or(|j| r.job == j)
                        && r.kind == "stream_open"
                }) {
                    return Poll::Ready(None);
                }
                if !transport.waiters.iter().any(|w| w.will_wake(cx.waker())) {
                    transport.waiters.push(cx.waker().clone());
                }
                Poll::Pending
            })
            .await;
            let Some((stream, failed)) = next else {
                return Ok(Value::Null);
            };
            if !retry {
                if let Some(error) = failed {
                    return Err(error);
                }
            }
            self.close_js_stream(&stream, true).await?;
        }
    }
}
impl Backend {
    pub(super) fn cancel_foreign_streams(&mut self, job: u64) -> PluginResult<()> {
        let Some(current) = self.jobs.get(&job) else {
            return Ok(());
        };
        let mut ctx = current.context.clone();
        ctx.cleanup = true;
        // The control context is independent of an escaped main-action clone.
        ctx.alive = Arc::new(AtomicBool::new(true));
        let streams = self
            .transport
            .lock()
            .unwrap()
            .foreign_streams
            .iter()
            .filter(|(_, s)| {
                s.session == current.session && s.job == job && !s.close_pending && !s.closing
            })
            .map(|(id, _)| id.clone())
            .collect::<Vec<_>>();
        for stream in streams {
            // The transport retains the real request; this control path does
            // not need a Rust waiter, and never fabricates its completion.
            drop(ctx.stream_request("stream_close", &stream, true)?);
        }
        ctx.alive.store(false, Ordering::Release);
        Ok(())
    }
    pub(super) fn open_rust_stream(
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
        let next = self.next_stream.checked_add(1).ok_or("StreamCapacity")?;
        let implementation = instance.open_stream(service, method, args)?;
        self.next_stream = next;
        self.streams.insert(
            next,
            RustStream {
                session,
                service: service.into(),
                publication,
                port,
                caller: None,
                implementation,
                pull: None,
                close: None,
                closing: false,
            },
        );
        Ok(serde_json::json!({"stream":next.to_string()}))
    }
    pub fn bind_stream(&mut self, stream: u64, caller: Option<(usize, u64)>) -> PluginResult<()> {
        self.streams.get_mut(&stream).ok_or("UnknownStream")?.caller = caller;
        Ok(())
    }
    pub fn stream_binding(
        &self,
        session: u64,
        stream: u64,
        caller: Option<(usize, u64)>,
    ) -> PluginResult<(String, usize, cordis_driver::ServicePort)> {
        let resource = self.streams.get(&stream).ok_or("UnknownStream")?;
        if resource.session != session || resource.caller != caller {
            return Err("WrongStreamOwner".into());
        }
        Ok((
            resource.service.clone(),
            resource.publication,
            resource.port,
        ))
    }
    pub fn stream_next(
        &mut self,
        session: u64,
        stream: u64,
        restoring: bool,
        continuing: bool,
    ) -> PluginResult<Value> {
        let resource = self.streams.get(&stream).ok_or("UnknownStream")?;
        if resource.session != session {
            return Err("WrongStreamOwner".into());
        }
        if resource.closing {
            return Err("StreamClosed".into());
        }
        if resource.pull.is_some() {
            return Err("StreamBusy".into());
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
        let future = implementation.next(ctx.clone());
        self.add_job(
            ctx,
            JobKind::Call,
            Box::pin(async move {
                match future.await? {
                    Some(value) => Ok(serde_json::json!({"done":false,"value":value})),
                    None => Ok(serde_json::json!({"done":true,"value":null})),
                }
            }),
        );
        self.jobs.get_mut(&job).unwrap().stream = Some(StreamAction::Next(stream));
        self.streams.get_mut(&stream).unwrap().pull = Some(job);
        Ok(serde_json::json!({"job":job.to_string()}))
    }
    pub fn stream_close(&mut self, session: u64, stream: u64) -> PluginResult<Value> {
        let Some(resource) = self.streams.get(&stream) else {
            if stream > 0 && stream <= self.next_stream {
                return Ok(serde_json::json!({"closed":true}));
            }
            return Err("UnknownStream".into());
        };
        if resource.session != session {
            return Err("WrongStreamOwner".into());
        }
        if let Some(job) = resource.close {
            return Ok(serde_json::json!({"job":job.to_string()}));
        }
        let implementation = resource.implementation.clone();
        let pull = resource.pull;
        let landing = pull
            .and_then(|id| self.jobs.get(&id))
            .map(|job| job.landing.clone());
        let job = self.job_id()?;
        let ctx = self.context(session, job, true)?;
        let close_ctx = ctx.clone();
        if let Some(pull) = pull {
            self.cancel_job(pull)?;
        }
        implementation.cancel();
        self.add_job(
            ctx,
            JobKind::ResourceClose,
            Box::pin(async move {
                if let Some(landing) = landing {
                    landing.wait().await;
                }
                implementation.close(close_ctx).await
            }),
        );
        self.jobs.get_mut(&job).unwrap().stream = Some(StreamAction::Close(stream));
        let resource = self.streams.get_mut(&stream).unwrap();
        resource.closing = true;
        resource.close = Some(job);
        Ok(serde_json::json!({"job":job.to_string()}))
    }
    pub(super) fn stream_landed(&mut self, action: StreamAction, success: bool) {
        match action {
            StreamAction::Next(stream) => {
                if let Some(stream) = self.streams.get_mut(&stream) {
                    stream.pull = None;
                }
            }
            StreamAction::Close(stream) => {
                if success {
                    self.streams.remove(&stream);
                } else if let Some(stream) = self.streams.get_mut(&stream) {
                    stream.close = None;
                }
            }
        }
    }
}
