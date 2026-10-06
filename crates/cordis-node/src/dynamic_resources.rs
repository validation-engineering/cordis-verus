//! Opaque resources retain their exact originating instance and library image.
//! The resident host owns the ordinary stream/object lifecycle and caller graph;
//! this module only adapts its admitted operations to the versioned C protocol.
use super::super::{ObjectDescriptor, ObjectOwnership, PluginObject, PluginStream, StreamFuture};
use super::*;

#[derive(Clone, Copy)]
enum Kind {
    Stream,
    Object,
}
impl Kind {
    fn key(self) -> &'static str {
        match self {
            Self::Stream => "stream",
            Self::Object => "object",
        }
    }
    fn destroy(self) -> &'static str {
        match self {
            Self::Stream => "destroy_stream",
            Self::Object => "destroy_object",
        }
    }
    fn close(self) -> &'static str {
        match self {
            Self::Stream => "stream_close",
            Self::Object => "object_close",
        }
    }
    fn count(self, module: &Module) -> &AtomicUsize {
        match self {
            Self::Stream => &module.streams,
            Self::Object => &module.objects,
        }
    }
    fn retained(self, module: &Module) -> &AtomicUsize {
        match self {
            Self::Stream => &module.retained_streams,
            Self::Object => &module.retained_objects,
        }
    }
}
struct Lease {
    instance: Arc<InstanceLease>,
    handle: u64,
    kind: Kind,
    closed: AtomicBool,
    destroyed: AtomicBool,
    finalization: Finalization,
    cancel_error: Mutex<Option<String>>,
}
impl Lease {
    fn new(instance: Arc<InstanceLease>, reply: &Value, kind: Kind) -> PluginResult<Arc<Self>> {
        let handle = match handle(reply, kind.key()) {
            Ok(handle) => handle,
            Err(error) => {
                // A malformed native response may have acquired something. It
                // is not a released resource merely because no ID was decoded.
                kind.retained(&instance.module)
                    .fetch_add(1, Ordering::AcqRel);
                return Err(error);
            }
        };
        kind.count(&instance.module).fetch_add(1, Ordering::AcqRel);
        Ok(Arc::new(Self {
            instance,
            handle,
            kind,
            closed: AtomicBool::new(false),
            destroyed: AtomicBool::new(false),
            finalization: Finalization::default(),
            cancel_error: Mutex::new(None),
        }))
    }
    fn request(&self, operation: &str) -> Value {
        let mut request = json!({"op":operation,"instance":self.instance.handle});
        request[self.kind.key()] = json!(self.handle);
        request
    }
    fn destroy(&self) -> PluginResult<()> {
        if self.finalization.pending() {
            return Err("NativeModuleFinalizationPending".into());
        }
        if !self.destroyed.load(Ordering::Acquire) {
            self.instance
                .module
                .request(self.request(self.kind.destroy()))?;
            self.destroyed.store(true, Ordering::Release);
        }
        Ok(())
    }
    fn cancel_stream(&self) {
        if self.closed.load(Ordering::Acquire) || self.destroyed.load(Ordering::Acquire) {
            return;
        }
        if let Err(error) = self.instance.module.request(self.request("stream_cancel")) {
            self.cancel_error
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .get_or_insert(error);
        }
    }
    fn close(self: &Arc<Self>, ctx: PluginContext) -> PluginFuture {
        let lease = self.clone();
        Box::pin(async move {
            if let Some(error) = lease
                .cancel_error
                .lock()
                .unwrap_or_else(|error| error.into_inner())
                .clone()
            {
                return Err(error);
            }
            lease.finalization.drain(&ctx, true).await?;
            if !lease.closed.load(Ordering::Acquire) {
                let job = lease
                    .instance
                    .job(lease.request(lease.kind.close()), ctx.clone())?;
                lease.finalization.begin(&ctx);
                let result = job.await;
                if result.is_ok() {
                    lease.closed.store(true, Ordering::Release);
                }
                lease.finalization.drain(&ctx, false).await?;
                result?;
            }
            // Destruction must succeed before the resident host can report a
            // successful close. Retrying never repeats a completed user hook.
            lease.destroy()?;
            Ok(Value::Null)
        })
    }
}
impl Drop for Lease {
    fn drop(&mut self) {
        if matches!(self.kind, Kind::Stream) && !self.closed.load(Ordering::Acquire) {
            // Best-effort cancellation on abandoned host teardown does not
            // count as close. Native jobs and images still remain retained.
            self.cancel_stream();
        }
        if self.destroy().is_err() {
            self.kind
                .retained(&self.instance.module)
                .fetch_add(1, Ordering::AcqRel);
        }
        self.kind
            .count(&self.instance.module)
            .fetch_sub(1, Ordering::AcqRel);
    }
}
struct Stream {
    lease: Arc<Lease>,
}
impl PluginStream for Stream {
    fn next(&self, ctx: PluginContext) -> StreamFuture {
        let lease = self.lease.clone();
        Box::pin(async move {
            if lease.closed.load(Ordering::Acquire) {
                return Err("NativeModuleStreamClosed".into());
            }
            let value = lease
                .instance
                .job(lease.request("stream_next"), ctx)?
                .await?;
            match value.get("done").and_then(Value::as_bool) {
                Some(true) => Ok(None),
                Some(false) => value
                    .get("value")
                    .cloned()
                    .map(Some)
                    .ok_or("NativeModuleInvalidStreamResult".into()),
                None => Err("NativeModuleInvalidStreamResult".into()),
            }
        })
    }
    fn cancel(&self) {
        self.lease.cancel_stream();
    }
    fn close(&self, ctx: PluginContext) -> PluginFuture {
        self.lease.close(ctx)
    }
}
struct Object {
    lease: Arc<Lease>,
    descriptor: ObjectDescriptor,
}
impl PluginObject for Object {
    fn descriptor(&self) -> ObjectDescriptor {
        self.descriptor.clone()
    }
    fn call(&self, ctx: PluginContext, method: &str, args: Value) -> PluginFuture {
        let lease = self.lease.clone();
        let mut request = lease.request("object_call");
        request["method"] = json!(method);
        request["args"] = args;
        Box::pin(async move {
            if lease.closed.load(Ordering::Acquire) {
                return Err("NativeModuleObjectClosed".into());
            }
            lease.instance.job(request, ctx)?.await
        })
    }
    fn close(&self, ctx: PluginContext) -> PluginFuture {
        self.lease.close(ctx)
    }
    fn release(&self, ctx: PluginContext, ownership: ObjectOwnership) -> PluginFuture {
        if ownership != self.descriptor.ownership() {
            return Box::pin(async { Err("NativeModuleObjectOwnershipChanged".into()) });
        }
        // Borrowed references still need a native release acknowledgement. The
        // SDK knows their original ownership and skips the user's close hook.
        self.lease.close(ctx)
    }
}
pub(super) fn open_stream(
    instance: Arc<InstanceLease>,
    service: &str,
    method: &str,
    args: Value,
) -> PluginResult<Arc<dyn PluginStream>> {
    let value = instance
        .module
        .request(json!({"op":"open_stream","instance":instance.handle,
        "service":service,"method":method,"args":args}))?;
    Ok(Arc::new(Stream {
        lease: Lease::new(instance, &value, Kind::Stream)?,
    }))
}
pub(super) fn open_object(
    instance: Arc<InstanceLease>,
    service: &str,
    method: &str,
    args: Value,
) -> PluginResult<Arc<dyn PluginObject>> {
    let value = instance
        .module
        .request(json!({"op":"open_object","instance":instance.handle,
        "service":service,"method":method,"args":args}))?;
    let lease = Lease::new(instance, &value, Kind::Object)?;
    let descriptor = ObjectDescriptor::from_value(
        value
            .get("descriptor")
            .cloned()
            .ok_or("NativeModuleInvalidObjectDescriptor")?,
    )?;
    Ok(Arc::new(Object { lease, descriptor }))
}
