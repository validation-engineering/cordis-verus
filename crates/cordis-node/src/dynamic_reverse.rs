//! Action-local capabilities adapt the SDK wire to the existing resident
//! journal. Dropping these maps never claims that their JS resources closed.
use super::super::{JsObject, JsStream};
use super::*;
use cordis_plugin_api::{
    ReverseItem, ReverseOperation, ReverseResult, MAX_CALL_BATCH_BYTES, MAX_REVERSE_RESOURCES,
};

pub(super) type ReverseFuture = Pin<Box<dyn Future<Output = PluginResult<Completion>> + Send>>;
pub(super) enum Completion {
    Value(Value),
    Stream(u64, JsStream),
    Object(u64, JsObject),
    Item(Option<Value>),
    Child(u64),
    ChildState(cordis_plugin_api::ChildStatus),
}
#[derive(Default)]
pub(super) struct Resources {
    next: u64,
    streams: BTreeMap<u64, JsStream>,
    objects: BTreeMap<u64, JsObject>,
}
impl Resources {
    fn reserve(&mut self) -> PluginResult<u64> {
        if self.next >= MAX_REVERSE_RESOURCES as u64 {
            return Err("NativeModuleReverseResourceCapacity".into());
        }
        self.next += 1;
        Ok(self.next)
    }
    fn prepare(
        &mut self,
        parent: Arc<InstanceLease>,
        context: PluginContext,
        call: ReverseCall,
    ) -> PluginResult<ReverseFuture> {
        if serde_json::to_vec(&call).map_or(true, |bytes| bytes.len() + 3 > MAX_CALL_BATCH_BYTES) {
            return Err("ReverseCallTooLarge".into());
        }
        use ReverseOperation::*;
        match &call.operation {
            Call { args, .. }
            | StreamOpen { args, .. }
            | ObjectOpen { args, .. }
            | CallbackOpen { args, .. }
            | ObjectCall { args, .. } => {
                if !args.is_array() {
                    return Err("ReverseCallArgumentsMustBeArray".into());
                }
                bounded_reverse_result(Ok(args.clone()))?;
            }
            ChildMount { config, .. } | ChildPublish { config, .. } => {
                bounded_reverse_result(Ok(config.clone()))?;
            }
            _ => {}
        }
        let callback = matches!(&call.operation, CallbackOpen { .. });
        Ok(match call.operation {
            Call {
                service,
                method,
                args,
            } => Box::pin(async move {
                context
                    .call(&service, &method, args)
                    .await
                    .map(Completion::Value)
            }),
            StreamOpen {
                service,
                method,
                args,
            } => {
                let handle = self.reserve()?;
                Box::pin(async move {
                    context
                        .open_stream(&service, &method, args)
                        .await
                        .map(|stream| Completion::Stream(handle, stream))
                })
            }
            ObjectOpen {
                service,
                method,
                args,
            }
            | CallbackOpen {
                service,
                method,
                args,
            } => {
                let handle = self.reserve()?;
                Box::pin(async move {
                    let object = context.open_object(&service, &method, args).await?;
                    if callback && object.descriptor().methods() != ["call"] {
                        // Acquisition is already in the resident journal, so
                        // rejecting its interface does not erase cleanup.
                        return Err("InvalidCallbackDescriptor".into());
                    }
                    Ok(Completion::Object(handle, object))
                })
            }
            StreamNext { stream } => {
                let stream = self
                    .streams
                    .get(&stream)
                    .cloned()
                    .ok_or("NativeModuleUnknownJsStream")?;
                Box::pin(async move { stream.next().await.map(Completion::Item) })
            }
            StreamClose { stream } => {
                let stream = self
                    .streams
                    .get(&stream)
                    .cloned()
                    .ok_or("NativeModuleUnknownJsStream")?;
                Box::pin(async move {
                    stream
                        .close()
                        .await
                        .map(|()| Completion::Value(Value::Null))
                })
            }
            ObjectCall {
                object,
                method,
                args,
            } => {
                let object = self
                    .objects
                    .get(&object)
                    .cloned()
                    .ok_or("NativeModuleUnknownJsObject")?;
                Box::pin(async move { object.call(&method, args).await.map(Completion::Value) })
            }
            ChildMount { factory, config } => Box::pin(async move {
                parent
                    .children
                    .clone()
                    .mount(parent, context, Some(factory), None, config)
                    .await
                    .map(Completion::Child)
            }),
            ChildPublish { definition, config } => Box::pin(async move {
                parent
                    .children
                    .clone()
                    .mount(parent, context, None, Some(definition), config)
                    .await
                    .map(Completion::Child)
            }),
            ChildStatus { child } => Box::pin(async move {
                parent
                    .children
                    .clone()
                    .operation(parent, context, child, children::Operation::Status)
                    .await
                    .map(Completion::ChildState)
            }),
            ChildReady { child }
            | ChildRetire { child }
            | ChildJoin { child }
            | ChildRetryCleanup { child } => {
                let operation = match call.operation {
                    ChildReady { .. } => children::Operation::Ready,
                    ChildRetire { .. } => children::Operation::Retire,
                    ChildJoin { .. } => children::Operation::Join,
                    _ => children::Operation::Retry,
                };
                Box::pin(async move {
                    parent
                        .children
                        .clone()
                        .operation(parent, context, child, operation)
                        .await
                        .map(|_| Completion::Value(Value::Null))
                })
            }
            ObjectClose { object } => {
                let object = self
                    .objects
                    .get(&object)
                    .cloned()
                    .ok_or("NativeModuleUnknownJsObject")?;
                Box::pin(async move {
                    object
                        .close()
                        .await
                        .map(|()| Completion::Value(Value::Null))
                })
            }
        })
    }
    pub(super) fn dispatch(
        &mut self,
        parent: Arc<InstanceLease>,
        context: PluginContext,
        call: ReverseCall,
    ) -> ReverseFuture {
        // Even validation failures resolve the native request normally, so its
        // main future remains capable of handling the error and cleaning up.
        let definition = match &call.operation {
            ReverseOperation::ChildPublish { definition, .. } => Some(*definition),
            _ => None,
        };
        match self.prepare(parent.clone(), context, call) {
            Ok(future) => future,
            Err(error) => {
                Box::pin(
                    async move { Err(children::reject_definition(&parent, definition, error)) },
                )
            }
        }
    }
    pub(super) fn resolve(&mut self, result: PluginResult<Completion>) -> ReverseResult {
        let result = result.and_then(|result| {
            Ok(match result {
                Completion::Child(child) => ReverseResult::Child { child },
                Completion::ChildState(mut child_state) => {
                    child_state.error = child_state
                        .error
                        .map(|error| bounded_reverse_result(Err(error)).unwrap_err());
                    ReverseResult::ChildState { child_state }
                }
                Completion::Value(value) => ReverseResult::Ok {
                    ok: bounded_reverse_result(Ok(value))?,
                },
                Completion::Item(value) => ReverseResult::Item {
                    item: match value {
                        Some(value) => ReverseItem {
                            done: false,
                            value: Some(bounded_reverse_result(Ok(value))?),
                        },
                        None => ReverseItem {
                            done: true,
                            value: None,
                        },
                    },
                },
                Completion::Stream(handle, stream) => {
                    self.streams.insert(handle, stream);
                    ReverseResult::Stream { stream: handle }
                }
                Completion::Object(handle, object) => {
                    let descriptor = bounded_reverse_result(Ok(json!(object.descriptor())))?;
                    self.objects.insert(handle, object);
                    ReverseResult::Object {
                        object: handle,
                        descriptor,
                    }
                }
            })
        });
        match result {
            Ok(result) => result,
            Err(error) => ReverseResult::Error {
                error: bounded_reverse_result(Err(error)).unwrap_err(),
            },
        }
    }
}
