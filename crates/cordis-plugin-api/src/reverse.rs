//! Action-scoped imports. Protocol handles never become ordinary JSON values
//! or public constructors; the resident action journal owns final disposal.
use super::*;

#[derive(Debug, Serialize, Deserialize)]
pub struct ReverseCall {
    pub request: u64,
    #[serde(flatten)]
    pub operation: ReverseOperation,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ReverseOperation {
    ChildMount {
        factory: String,
        config: Value,
    },
    ChildPublish {
        definition: u64,
        config: Value,
    },
    ChildStatus {
        child: u64,
    },
    ChildReady {
        child: u64,
    },
    ChildRetire {
        child: u64,
    },
    ChildJoin {
        child: u64,
    },
    ChildRetryCleanup {
        child: u64,
    },
    Call {
        service: String,
        method: String,
        args: Value,
    },
    StreamOpen {
        service: String,
        method: String,
        args: Value,
    },
    StreamNext {
        stream: u64,
    },
    StreamClose {
        stream: u64,
    },
    ObjectOpen {
        service: String,
        method: String,
        args: Value,
    },
    CallbackOpen {
        service: String,
        method: String,
        args: Value,
    },
    ObjectCall {
        object: u64,
        method: String,
        args: Value,
    },
    ObjectClose {
        object: u64,
    },
}
impl ReverseOperation {
    fn is_open(&self) -> bool {
        matches!(
            self,
            Self::StreamOpen { .. } | Self::ObjectOpen { .. } | Self::CallbackOpen { .. }
        )
    }
    fn resource(&self) -> Option<(u64, bool, bool)> {
        match *self {
            Self::StreamNext { stream } => Some((stream, false, false)),
            Self::StreamClose { stream } => Some((stream, false, true)),
            Self::ObjectCall { object, .. } => Some((object, true, false)),
            Self::ObjectClose { object } => Some((object, true, true)),
            _ => None,
        }
    }
}
/// Explicit resource replies are separate from user JSON results.
#[derive(Debug, Serialize, Deserialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum ReverseResult {
    Child { child: u64 },
    ChildState { child_state: ChildStatus },
    Ok { ok: Value },
    Error { error: String },
    Stream { stream: u64 },
    Object { object: u64, descriptor: Value },
    Item { item: ReverseItem },
}
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReverseItem {
    pub done: bool,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        deserialize_with = "present_value"
    )]
    pub value: Option<Value>,
}
fn present_value<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> Result<Option<Value>, D::Error> {
    Value::deserialize(deserializer).map(Some)
}
impl From<PluginResult<Value>> for ReverseResult {
    fn from(value: PluginResult<Value>) -> Self {
        match value {
            Ok(ok) => Self::Ok { ok },
            Err(error) => Self::Error { error },
        }
    }
}
#[derive(Debug)]
pub(super) enum CallValue {
    Child(u64),
    ChildState(ChildStatus),
    Json(Value),
    Stream(u64),
    Object(u64, ObjectDescriptor),
    Item(Option<Value>),
}
impl CallValue {
    pub(super) fn json(self) -> PluginResult<Value> {
        match self {
            Self::Json(value) => Ok(value),
            _ => Err("InvalidReverseReply".into()),
        }
    }
}
struct CallReply {
    result: Option<PluginResult<CallValue>>,
    waker: Option<Waker>,
    consumed: bool,
}
pub(super) struct CallFuture(Arc<Mutex<CallReply>>);
impl Future for CallFuture {
    type Output = PluginResult<CallValue>;
    fn poll(self: Pin<&mut Self>, context: &mut Context<'_>) -> Poll<Self::Output> {
        let next = context.waker().clone();
        let (poll, previous) = {
            let mut state = self.0.lock().unwrap();
            if state.consumed {
                return Poll::Ready(Err("ReverseCallResultConsumed".into()));
            }
            if let Some(result) = state.result.take() {
                state.consumed = true;
                (Poll::Ready(result), state.waker.take())
            } else {
                (Poll::Pending, state.waker.replace(next))
            }
        };
        drop(previous);
        poll
    }
}
struct CallRecord {
    queued: Option<ReverseCall>,
    operation: ReverseOperation,
    encoded_bytes: usize,
    reply: Arc<Mutex<CallReply>>,
}
struct ForeignResource {
    descriptor: Option<ObjectDescriptor>,
    pending: usize,
    closing: bool,
    closed: bool,
    ended: bool,
}
pub(super) struct CallQueue {
    open: bool,
    pub(super) next: u64,
    pending: BTreeMap<u64, CallRecord>,
    resources: BTreeMap<u64, ForeignResource>,
    admitted_resources: usize,
}
pub(super) struct CallAction {
    children: Option<Arc<ChildScope>>,
    inject: BTreeSet<String>,
    wake: Arc<HostWake>,
    pub(super) queue: Mutex<CallQueue>,
}
impl CallAction {
    pub(super) fn new(inject: &[String], wake: Arc<HostWake>) -> Self {
        Self {
            children: None,
            inject: inject.iter().cloned().collect(),
            wake,
            queue: Mutex::new(CallQueue {
                open: true,
                next: 1,
                pending: BTreeMap::new(),
                resources: BTreeMap::new(),
                admitted_resources: 0,
            }),
        }
    }
    pub(super) fn for_instance(
        inject: &[String],
        wake: Arc<HostWake>,
        children: Arc<ChildScope>,
    ) -> Self {
        let mut calls = Self::new(inject, wake);
        calls.children = Some(children);
        calls
    }
    pub(super) fn check_open(&self) -> PluginResult<()> {
        if self.queue.lock().unwrap().open {
            Ok(())
        } else {
            Err("ActionClosed".into())
        }
    }
    pub(super) fn enqueue_child(&self, operation: ReverseOperation) -> PluginResult<CallFuture> {
        if self.children.is_none() {
            return Err("ActionClosed".into());
        }
        self.enqueue_operation(operation)
    }
    pub(super) fn enqueue(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<CallFuture> {
        self.enqueue_operation(ReverseOperation::Call {
            service: service.into(),
            method: method.into(),
            args,
        })
    }
    fn enqueue_operation(&self, mut operation: ReverseOperation) -> PluginResult<CallFuture> {
        match &mut operation {
            ReverseOperation::Call {
                service,
                method,
                args,
            }
            | ReverseOperation::StreamOpen {
                service,
                method,
                args,
            }
            | ReverseOperation::ObjectOpen {
                service,
                method,
                args,
            }
            | ReverseOperation::CallbackOpen {
                service,
                method,
                args,
            } => {
                if !self.inject.contains(service) {
                    return Err("UndeclaredInjection".into());
                }
                check_arguments(method, args)?;
                if service.len() > MAX_CALL_BATCH_BYTES {
                    return Err("ReverseCallTooLarge".into());
                }
            }
            ReverseOperation::ObjectCall { method, args, .. } => check_arguments(method, args)?,
            ReverseOperation::ChildMount { config, .. }
            | ReverseOperation::ChildPublish { config, .. } => {
                *config = bounded_result(Ok(std::mem::take(config)))?;
            }
            _ => {}
        }
        let mut queue = self.queue.lock().unwrap();
        if !queue.open {
            return Err("ActionClosed".into());
        }
        if queue.pending.len() >= MAX_PENDING_CALLS {
            return Err("ReverseCallCapacity".into());
        }
        if operation.is_open() && queue.admitted_resources >= MAX_REVERSE_RESOURCES {
            return Err("ReverseResourceCapacity".into());
        }
        if let Some((id, object, close)) = operation.resource() {
            let state = queue.resources.get(&id).ok_or("UnknownReverseResource")?;
            if state.descriptor.is_some() != object {
                return Err("WrongReverseResourceKind".into());
            }
            if close {
                if state.pending != 0 {
                    return Err(if object { "ObjectBusy" } else { "StreamBusy" }.into());
                }
                if state.closed {
                    return Ok(completed(Ok(CallValue::Json(Value::Null))));
                }
            } else {
                if state.closing || state.closed || (!object && (state.pending != 0 || state.ended))
                {
                    return Err(if object {
                        "ObjectClosed"
                    } else {
                        "StreamBusyOrClosed"
                    }
                    .into());
                }
                if let ReverseOperation::ObjectCall { method, .. } = &operation {
                    if !state
                        .descriptor
                        .as_ref()
                        .unwrap()
                        .methods()
                        .contains(method)
                    {
                        return Err("UndeclaredObjectMethod".into());
                    }
                }
            }
        }
        let request = queue.next;
        let next = request
            .checked_add(1)
            .ok_or("ReverseCallHandleSpaceExhausted")?;
        let call = ReverseCall {
            request,
            operation: operation.clone(),
        };
        let encoded_bytes = serde_json::to_vec(&call)
            .map_err(|_| "ReverseCallEncoding")?
            .len();
        if encoded_bytes + 3 > MAX_CALL_BATCH_BYTES {
            return Err("ReverseCallTooLarge".into());
        }
        let reply = Arc::new(Mutex::new(CallReply {
            result: None,
            waker: None,
            consumed: false,
        }));
        if let Some((id, _, close)) = operation.resource() {
            let state = queue.resources.get_mut(&id).unwrap();
            state.pending += 1;
            state.closing |= close;
        }
        if operation.is_open() {
            queue.admitted_resources += 1;
        }
        queue.next = next;
        queue.pending.insert(
            request,
            CallRecord {
                queued: Some(call),
                operation,
                encoded_bytes,
                reply: reply.clone(),
            },
        );
        drop(queue);
        self.wake.notify();
        Ok(CallFuture(reply))
    }
    pub(super) fn has_queued(&self) -> bool {
        self.queue
            .lock()
            .unwrap()
            .pending
            .values()
            .any(|call| call.queued.is_some())
    }
    pub(super) fn close(&self) {
        self.queue.lock().unwrap().open = false;
    }
    pub(super) fn take_batch(&self) -> (Vec<ReverseCall>, usize) {
        let mut queue = self.queue.lock().unwrap();
        let mut calls = Vec::new();
        let mut bytes = 2;
        for record in queue.pending.values_mut() {
            if record.queued.is_some() {
                if bytes + record.encoded_bytes + 1 > MAX_CALL_BATCH_BYTES {
                    break;
                }
                bytes += record.encoded_bytes + 1;
                calls.push(record.queued.take().unwrap());
            }
        }
        let pending = queue.pending.len();
        let queued = queue.pending.values().any(|record| record.queued.is_some());
        drop(queue);
        if queued {
            self.wake.notify();
        }
        (calls, pending)
    }
    pub(super) fn resolve(
        &self,
        request: u64,
        result: impl Into<ReverseResult>,
    ) -> PluginResult<()> {
        let result = result.into();
        let (record, result) = {
            let mut queue = self.queue.lock().unwrap();
            let record = queue.pending.get(&request).ok_or("UnknownReverseCall")?;
            if record.queued.is_some() {
                return Err("ReverseCallNotDispatched".into());
            }
            let mut result = normalize_reply(&record.operation, result);
            let record = queue.pending.remove(&request).unwrap();
            if let Some((id, _, close)) = record.operation.resource() {
                let state = queue.resources.get_mut(&id).unwrap();
                state.pending -= 1;
                if close && result.is_ok() {
                    state.closed = true;
                }
                if matches!(result, Ok(CallValue::Item(None))) {
                    state.ended = true;
                }
            }
            let opened = match &result {
                Ok(CallValue::Stream(id)) => Some((*id, None)),
                Ok(CallValue::Object(id, descriptor)) => Some((*id, Some(descriptor.clone()))),
                _ => None,
            };
            if let Some((id, descriptor)) = opened {
                if id == 0 || queue.resources.contains_key(&id) {
                    result = Err("InvalidReverseResourceHandle".into());
                } else {
                    queue.resources.insert(
                        id,
                        ForeignResource {
                            descriptor,
                            pending: 0,
                            closing: false,
                            closed: false,
                            ended: false,
                        },
                    );
                }
            }
            if let Some(scope) = &self.children {
                if let Ok(CallValue::Child(child)) = &result {
                    let definition = match record.operation {
                        ReverseOperation::ChildPublish { definition, .. } => Some(definition),
                        _ => None,
                    };
                    if let Err(error) = scope.allocated(*child, definition) {
                        result = Err(error);
                    }
                }
                if let Err(error) = scope.completed(&record.operation, &mut result) {
                    result = Err(error);
                }
            }
            (record, result)
        };
        let waker = {
            let mut reply = record.reply.lock().unwrap();
            reply.result = Some(result);
            reply.waker.take()
        };
        if let Some(waker) = waker {
            waker.wake();
        }
        self.wake.notify();
        Ok(())
    }
}
fn completed(result: PluginResult<CallValue>) -> CallFuture {
    CallFuture(Arc::new(Mutex::new(CallReply {
        result: Some(result),
        waker: None,
        consumed: false,
    })))
}
fn check_arguments(method: &str, args: &mut Value) -> PluginResult<()> {
    if method.is_empty() {
        return Err("EmptyMethod".into());
    }
    if method.len() > MAX_CALL_BATCH_BYTES {
        return Err("ReverseCallTooLarge".into());
    }
    if !args.is_array() {
        return Err("ReverseCallArgumentsMustBeArray".into());
    }
    *args = bounded_result(Ok(std::mem::take(args)))?;
    Ok(())
}
fn normalize_reply(operation: &ReverseOperation, result: ReverseResult) -> PluginResult<CallValue> {
    use ReverseOperation as Op;
    match (operation, result) {
        (Op::ChildMount { .. } | Op::ChildPublish { .. }, ReverseResult::Child { child }) => {
            Ok(CallValue::Child(child))
        }
        (Op::ChildStatus { .. }, ReverseResult::ChildState { child_state }) => {
            bounded_result(Ok(json!(&child_state)))?;
            if child_state
                .id
                .as_ref()
                .is_some_and(|id| id.parse::<u64>().is_err())
            {
                return Err("InvalidChildStatus".into());
            }
            Ok(CallValue::ChildState(child_state))
        }
        (
            Op::ChildReady { .. }
            | Op::ChildRetire { .. }
            | Op::ChildJoin { .. }
            | Op::ChildRetryCleanup { .. },
            ReverseResult::Ok { ok: Value::Null },
        ) => Ok(CallValue::Json(Value::Null)),
        (_, ReverseResult::Error { error }) => bounded_result(Err(error)).map(CallValue::Json),
        (Op::Call { .. } | Op::ObjectCall { .. }, ReverseResult::Ok { ok }) => {
            bounded_result(Ok(ok)).map(CallValue::Json)
        }
        (
            Op::StreamClose { .. } | Op::ObjectClose { .. },
            ReverseResult::Ok { ok: Value::Null },
        ) => Ok(CallValue::Json(Value::Null)),
        (Op::StreamOpen { .. }, ReverseResult::Stream { stream }) => Ok(CallValue::Stream(stream)),
        (
            Op::ObjectOpen { .. } | Op::CallbackOpen { .. },
            ReverseResult::Object { object, descriptor },
        ) => {
            let descriptor = ObjectDescriptor::from_value(bounded_result(Ok(descriptor))?)?;
            if matches!(operation, Op::CallbackOpen { .. }) && descriptor.methods() != ["call"] {
                return Err("InvalidCallbackDescriptor".into());
            }
            Ok(CallValue::Object(object, descriptor))
        }
        (
            Op::StreamNext { .. },
            ReverseResult::Item {
                item:
                    ReverseItem {
                        done: true,
                        value: None,
                    },
            },
        ) => Ok(CallValue::Item(None)),
        (
            Op::StreamNext { .. },
            ReverseResult::Item {
                item:
                    ReverseItem {
                        done: false,
                        value: Some(value),
                    },
            },
        ) => bounded_result(Ok(value)).map(|value| CallValue::Item(Some(value))),
        (_, unexpected) => {
            // Even malformed in-process replies may contain deeply nested user
            // values; reject them without recursive serde_json destruction.
            match unexpected {
                ReverseResult::Ok { ok } => discard_deep_value(ok),
                ReverseResult::Object { descriptor, .. } => discard_deep_value(descriptor),
                ReverseResult::Item { item } => {
                    if let Some(value) = item.value {
                        discard_deep_value(value);
                    }
                }
                _ => {}
            }
            Err("InvalidReverseReply".into())
        }
    }
}

impl PluginContext {
    pub fn is_cancelled(&self) -> bool {
        self.cancellation.is_cancelled()
    }
    pub async fn cancelled(&self) {
        self.cancellation.cancelled().await;
    }
    fn business(&self) -> PluginResult<&Arc<CallAction>> {
        if !self.cleanup {
            self.cancellation.check()?;
        }
        self.calls.as_ref().ok_or_else(|| "ActionClosed".into())
    }
    /// Admit on first poll; dropping the awaiter never abandons accepted work.
    pub async fn call(&self, service: &str, method: &str, args: Value) -> PluginResult<Value> {
        self.business()?
            .enqueue(service, method, args)?
            .await?
            .json()
    }
    pub async fn open_stream(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<JsStream> {
        let result = self
            .business()?
            .enqueue_operation(ReverseOperation::StreamOpen {
                service: service.into(),
                method: method.into(),
                args,
            })?
            .await?;
        match result {
            CallValue::Stream(stream) => Ok(JsStream {
                context: self.clone(),
                stream,
            }),
            _ => Err("InvalidReverseReply".into()),
        }
    }
    pub async fn open_object(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<JsObject> {
        self.open_object_kind(service, method, args, false).await
    }
    pub async fn open_callback(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<JsCallback> {
        self.open_object_kind(service, method, args, true)
            .await
            .map(JsCallback)
    }
    async fn open_object_kind(
        &self,
        service: &str,
        method: &str,
        args: Value,
        callback: bool,
    ) -> PluginResult<JsObject> {
        let operation = if callback {
            ReverseOperation::CallbackOpen {
                service: service.into(),
                method: method.into(),
                args,
            }
        } else {
            ReverseOperation::ObjectOpen {
                service: service.into(),
                method: method.into(),
                args,
            }
        };
        match self.business()?.enqueue_operation(operation)?.await? {
            CallValue::Object(object, descriptor) => Ok(JsObject {
                context: self.clone(),
                object,
                descriptor,
            }),
            _ => Err("InvalidReverseReply".into()),
        }
    }
}
/// A private capability scoped to its creating action; clones do not extend it.
#[derive(Clone)]
pub struct JsStream {
    context: PluginContext,
    stream: u64,
}
impl JsStream {
    pub async fn next(&self) -> PluginResult<Option<Value>> {
        match self
            .context
            .business()?
            .enqueue_operation(ReverseOperation::StreamNext {
                stream: self.stream,
            })?
            .await?
        {
            CallValue::Item(value) => Ok(value),
            _ => Err("InvalidReverseReply".into()),
        }
    }
    /// Busy is an immediate error; await admitted pulls before explicit close.
    /// Cancellation does not prevent close, and failed close remains retryable.
    pub async fn close(&self) -> PluginResult<()> {
        self.context
            .calls
            .as_ref()
            .ok_or("ActionClosed")?
            .enqueue_operation(ReverseOperation::StreamClose {
                stream: self.stream,
            })?
            .await?
            .json()?;
        Ok(())
    }
}
#[derive(Clone)]
pub struct JsObject {
    context: PluginContext,
    object: u64,
    descriptor: ObjectDescriptor,
}
impl JsObject {
    pub fn descriptor(&self) -> &ObjectDescriptor {
        &self.descriptor
    }
    pub async fn call(&self, method: &str, args: Value) -> PluginResult<Value> {
        self.context
            .business()?
            .enqueue_operation(ReverseOperation::ObjectCall {
                object: self.object,
                method: method.into(),
                args,
            })?
            .await?
            .json()
    }
    pub async fn close(&self) -> PluginResult<()> {
        self.context
            .calls
            .as_ref()
            .ok_or("ActionClosed")?
            .enqueue_operation(ReverseOperation::ObjectClose {
                object: self.object,
            })?
            .await?
            .json()?;
        Ok(())
    }
}
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

#[cfg(test)]
#[path = "reverse_resource_tests.rs"]
mod tests;
