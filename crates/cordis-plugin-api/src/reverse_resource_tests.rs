use super::*;

fn context() -> (PluginContext, Arc<CallAction>) {
    let calls = Arc::new(CallAction::new(
        &["js".into()],
        Arc::new(HostWake(Mutex::new(None))),
    ));
    (
        PluginContext {
            calls: Some(calls.clone()),
            cancellation: CancellationToken::default(),
            cleanup: false,
            children: None,
        },
        calls,
    )
}
fn poll<F: Future + ?Sized>(future: Pin<&mut F>) -> Poll<F::Output> {
    future.poll(&mut Context::from_waker(Waker::noop()))
}
fn ready<T>(value: Poll<PluginResult<T>>) -> T {
    match value {
        Poll::Ready(Ok(value)) => value,
        _ => panic!("expected successful completion"),
    }
}
fn error<T>(value: Poll<PluginResult<T>>) -> String {
    match value {
        Poll::Ready(Err(error)) => error,
        _ => panic!("expected failed completion"),
    }
}
fn dispatched(calls: &CallAction) -> u64 {
    let (batch, pending) = calls.take_batch();
    assert_eq!(batch.len(), 1);
    assert!(pending > 0);
    batch[0].request
}
fn stream(ctx: &PluginContext, calls: &CallAction, id: u64) -> JsStream {
    let mut future = Box::pin(ctx.open_stream("js", "stream", json!([])));
    assert!(poll(future.as_mut()).is_pending());
    calls
        .resolve(dispatched(calls), ReverseResult::Stream { stream: id })
        .unwrap();
    ready(poll(future.as_mut()))
}
fn object(ctx: &PluginContext, calls: &CallAction, id: u64) -> JsObject {
    let mut future = Box::pin(ctx.open_object("js", "object", json!([])));
    assert!(poll(future.as_mut()).is_pending());
    calls.resolve(dispatched(calls), ReverseResult::Object { object: id, descriptor: json!({"typeName":"counter","methods":["read","add"],"ownership":"owned"}) }).unwrap();
    ready(poll(future.as_mut()))
}

#[test]
fn typed_resource_replies_preserve_null_items_and_reject_dto_handle_forgery() {
    let raw: ReverseResult =
        serde_json::from_value(json!({"item":{"done":false,"value":null}})).unwrap();
    assert!(matches!(
        raw,
        ReverseResult::Item {
            item: ReverseItem {
                done: false,
                value: Some(Value::Null)
            }
        }
    ));
    assert!(serde_json::from_value::<ReverseResult>(json!({"stream":1,"ok":null})).is_err());
    assert!(serde_json::from_value::<ReverseCall>(
        json!({"request":1,"kind":"stream_next","stream":1,"args":[]})
    )
    .is_err());
    let (ctx, calls) = context();
    let mut future = Box::pin(ctx.open_stream("js", "stream", json!([])));
    assert!(poll(future.as_mut()).is_pending());
    calls
        .resolve(dispatched(&calls), Ok(json!({"stream":1})))
        .unwrap();
    assert_eq!(error(poll(future.as_mut())), "InvalidReverseReply");
    assert!(calls.queue.lock().unwrap().pending.is_empty());
    assert!(calls.queue.lock().unwrap().resources.is_empty());
}

#[test]
fn dropped_pull_still_blocks_close_and_drains_after_action_admission_closes() {
    let (ctx, calls) = context();
    let stream = stream(&ctx, &calls, 1);
    let mut next = Box::pin(stream.next());
    assert!(poll(next.as_mut()).is_pending());
    drop(next);
    assert_eq!(
        error(poll(Box::pin(stream.next()).as_mut())),
        "StreamBusyOrClosed"
    );
    assert_eq!(error(poll(Box::pin(stream.close()).as_mut())), "StreamBusy");
    calls.close();
    assert_eq!(
        error(poll(Box::pin(stream.clone().close()).as_mut())),
        "ActionClosed"
    );
    let request = dispatched(&calls);
    assert_eq!(calls.queue.lock().unwrap().pending.len(), 1);
    calls
        .resolve(
            request,
            ReverseResult::Item {
                item: ReverseItem {
                    done: false,
                    value: Some(Value::Null),
                },
            },
        )
        .unwrap();
    assert!(calls.queue.lock().unwrap().pending.is_empty());
    assert_eq!(calls.queue.lock().unwrap().resources[&1].pending, 0);
}

#[test]
fn concurrent_object_calls_block_explicit_close_and_failed_close_can_retry_after_cancel() {
    let (ctx, calls) = context();
    let object = object(&ctx, &calls, 1);
    assert_eq!(object.descriptor().type_name(), "counter");
    assert_eq!(
        error(poll(Box::pin(object.call("hidden", json!([]))).as_mut())),
        "UndeclaredObjectMethod"
    );
    let mut one = Box::pin(object.call("read", json!([])));
    let mut two = Box::pin(object.call("add", json!([2])));
    assert!(poll(one.as_mut()).is_pending());
    assert!(poll(two.as_mut()).is_pending());
    let (batch, _) = calls.take_batch();
    assert_eq!(batch.len(), 2);
    assert_eq!(error(poll(Box::pin(object.close()).as_mut())), "ObjectBusy");
    calls.resolve(batch[0].request, Ok(json!(1))).unwrap();
    assert_eq!(ready(poll(one.as_mut())), json!(1));
    assert_eq!(error(poll(Box::pin(object.close()).as_mut())), "ObjectBusy");
    calls.resolve(batch[1].request, Ok(json!(3))).unwrap();
    assert_eq!(ready(poll(two.as_mut())), json!(3));
    drop((one, two));
    let mut close = Box::pin(object.close());
    assert!(poll(close.as_mut()).is_pending());
    calls
        .resolve(dispatched(&calls), Err("CloseFailed".to_string()))
        .unwrap();
    assert_eq!(error(poll(close.as_mut())), "CloseFailed");
    assert_eq!(
        error(poll(Box::pin(object.call("read", json!([]))).as_mut())),
        "ObjectClosed"
    );
    ctx.cancellation.cancel();
    let mut retry = Box::pin(object.close());
    assert!(poll(retry.as_mut()).is_pending());
    calls.resolve(dispatched(&calls), Ok(Value::Null)).unwrap();
    ready(poll(retry.as_mut()));
    ready(poll(Box::pin(object.close()).as_mut()));
    assert_eq!(calls.take_batch().1, 0);
    calls.close();
    assert_eq!(
        error(poll(Box::pin(object.close()).as_mut())),
        "ActionClosed"
    );
}

#[test]
fn invalid_descriptors_callbacks_and_duplicate_handles_land_as_errors() {
    let (ctx, calls) = context();
    for descriptor in [
        json!({"typeName":"bad","methods":["read","read"],"ownership":"owned"}),
        json!({"typeName":"bad","methods":["call"],"ownership":"wrong"}),
    ] {
        let mut future = Box::pin(ctx.open_object("js", "object", json!([])));
        assert!(poll(future.as_mut()).is_pending());
        calls
            .resolve(
                dispatched(&calls),
                ReverseResult::Object {
                    object: 1,
                    descriptor,
                },
            )
            .unwrap();
        assert_eq!(error(poll(future.as_mut())), "InvalidObjectDescriptor");
    }
    let mut callback = Box::pin(ctx.open_callback("js", "callback", json!([])));
    assert!(poll(callback.as_mut()).is_pending());
    calls.resolve(dispatched(&calls), ReverseResult::Object { object: 1, descriptor: json!({"typeName":"not.callback","methods":["read"],"ownership":"borrowed"}) }).unwrap();
    assert_eq!(error(poll(callback.as_mut())), "InvalidCallbackDescriptor");
    let _stream = stream(&ctx, &calls, 1);
    let mut another = Box::pin(ctx.open_object("js", "object", json!([])));
    assert!(poll(another.as_mut()).is_pending());
    calls
        .resolve(
            dispatched(&calls),
            ReverseResult::Object {
                object: 1,
                descriptor: json!({"typeName":"counter","methods":["read"],"ownership":"owned"}),
            },
        )
        .unwrap();
    assert_eq!(
        error(poll(another.as_mut())),
        "InvalidReverseResourceHandle"
    );
    assert_eq!(calls.take_batch().1, 0);
}

#[test]
fn stream_reply_payload_limit_is_independent_of_protocol_envelope() {
    let (ctx, calls) = context();
    let stream = stream(&ctx, &calls, 1);
    for (value, expected) in [
        (Value::String("x".repeat(MAX_MESSAGE_BYTES / 2 - 2)), None),
        (
            Value::String("x".repeat(MAX_MESSAGE_BYTES / 2)),
            Some("ResultTooLarge"),
        ),
    ] {
        let mut next = Box::pin(stream.next());
        assert!(poll(next.as_mut()).is_pending());
        calls
            .resolve(
                dispatched(&calls),
                ReverseResult::Item {
                    item: ReverseItem {
                        done: false,
                        value: Some(value),
                    },
                },
            )
            .unwrap();
        if let Some(error_text) = expected {
            assert_eq!(error(poll(next.as_mut())), error_text);
        } else {
            assert!(ready(poll(next.as_mut())).is_some());
        }
    }
    let mut value = Value::Null;
    for _ in 0..65 {
        value = json!([value]);
    }
    let mut next = Box::pin(stream.next());
    assert!(poll(next.as_mut()).is_pending());
    calls
        .resolve(
            dispatched(&calls),
            ReverseResult::Item {
                item: ReverseItem {
                    done: false,
                    value: Some(value),
                },
            },
        )
        .unwrap();
    assert_eq!(error(poll(next.as_mut())), "ValueTooDeep");
    let mut close = Box::pin(stream.close());
    assert!(poll(close.as_mut()).is_pending());
    calls.resolve(dispatched(&calls), Ok(Value::Null)).unwrap();
    ready(poll(close.as_mut()));
}

#[test]
fn dropped_acquisition_keeps_capability_accounted_and_capacity_is_bounded() {
    let (ctx, calls) = context();
    for id in 1..=MAX_REVERSE_RESOURCES as u64 {
        let mut future = Box::pin(ctx.open_stream("js", "stream", json!([])));
        assert!(poll(future.as_mut()).is_pending());
        drop(future);
        calls
            .resolve(dispatched(&calls), ReverseResult::Stream { stream: id })
            .unwrap();
    }
    assert_eq!(
        error(poll(
            Box::pin(ctx.open_stream("js", "stream", json!([]))).as_mut()
        )),
        "ReverseResourceCapacity"
    );
    assert_eq!(
        calls.queue.lock().unwrap().resources.len(),
        MAX_REVERSE_RESOURCES
    );
    assert_eq!(calls.take_batch().1, 0);
    calls.close();
    assert_eq!(
        error(poll(
            Box::pin(ctx.open_object("js", "object", json!([]))).as_mut()
        )),
        "ActionClosed"
    );
}

#[test]
fn callback_capability_preserves_borrowed_descriptor_and_invokes_declared_call() {
    let (ctx, calls) = context();
    let mut opening = Box::pin(ctx.open_callback("js", "callback", json!([])));
    assert!(poll(opening.as_mut()).is_pending());
    calls.resolve(dispatched(&calls), ReverseResult::Object { object: 1, descriptor: json!({"typeName":"callback","methods":["call"],"ownership":"borrowed"}) }).unwrap();
    let callback = ready(poll(opening.as_mut()));
    assert_eq!(callback.descriptor().ownership(), ObjectOwnership::Borrowed);
    let mut invoke = Box::pin(callback.invoke(json!([4])));
    assert!(poll(invoke.as_mut()).is_pending());
    let (batch, _) = calls.take_batch();
    assert!(
        matches!(&batch[0].operation, ReverseOperation::ObjectCall { object: 1, method, args } if method=="call" && args==&json!([4]))
    );
    calls.resolve(batch[0].request, Ok(json!(8))).unwrap();
    assert_eq!(ready(poll(invoke.as_mut())), json!(8));
}

#[test]
fn failed_acquisitions_do_not_reset_the_per_action_admission_budget() {
    let (ctx, calls) = context();
    for _ in 0..MAX_REVERSE_RESOURCES {
        let mut future = Box::pin(ctx.open_object("js", "object", json!([])));
        assert!(poll(future.as_mut()).is_pending());
        calls
            .resolve(dispatched(&calls), Err("OpenFailed".to_owned()))
            .unwrap();
        assert_eq!(error(poll(future.as_mut())), "OpenFailed");
    }
    assert!(calls.queue.lock().unwrap().resources.is_empty());
    assert_eq!(
        error(poll(
            Box::pin(ctx.open_stream("js", "stream", json!([]))).as_mut()
        )),
        "ReverseResourceCapacity"
    );
    assert_eq!(calls.take_batch().1, 0);
}
