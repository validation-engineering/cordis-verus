use super::tests::{
    call_result, cleanup_reverse, number, resource_call, reverse_backend, reverse_backend_config,
};
use super::*;

fn operations(backend: &mut super::super::Backend) -> Vec<Value> {
    for _ in 0..20 {
        let poll = backend.poll();
        assert_eq!(poll["jobs"], json!([]), "{poll}");
        if !poll["calls"].as_array().unwrap().is_empty() {
            return poll["calls"].as_array().unwrap().clone();
        }
    }
    panic!("missing reverse resource operation");
}
fn operation(backend: &mut super::super::Backend, kind: &str) -> Value {
    let calls = operations(backend);
    assert_eq!(calls.len(), 1, "{calls:?}");
    assert_eq!(calls[0]["kind"], kind);
    calls[0].clone()
}
fn reply(backend: &mut super::super::Backend, call: &Value, value: Value) {
    backend.reply(number(call, "request"), Ok(value)).unwrap();
}
fn open_object(backend: &mut super::super::Backend, call: &Value, methods: Value) {
    reply(
        backend,
        call,
        json!({"object":"js-object", "descriptor":{"typeName":"test.Callback","methods":methods,"ownership":"owned"}}),
    );
}
#[test]
fn reverse_stream_item_is_bounded_before_envelope_and_live_body_is_not_closed() {
    let (mut backend, module, session) = reverse_backend();
    for value in [Value::Null, json!("x".repeat(MAX_MESSAGE_BYTES / 2 - 2))] {
        backend
            .call(session, "native", "importStream", json!([]), false, false)
            .unwrap();
        let open = operation(&mut backend, "stream_open");
        reply(&mut backend, &open, json!({"stream":"js-stream"}));
        let next = operation(&mut backend, "stream_next");
        assert_eq!(backend.poll()["calls"], json!([]));
        assert_eq!(module.info()["resources"]["streams"], 0);
        reply(&mut backend, &next, json!({"done":false,"value":value}));
        let close = operation(&mut backend, "stream_close");
        assert_eq!(close["restoring"], true);
        reply(&mut backend, &close, json!({"done":true}));
        let result = call_result(&mut backend);
        assert_eq!(result["success"], true, "{result}");
        assert_eq!(result["value"], value);
    }
    cleanup_reverse(&mut backend, &module, session);
}
#[test]
fn dropped_native_next_returns_js_stream_before_waiting_for_actual_next_without_cancel() {
    let (mut backend, module, session) = reverse_backend();
    backend
        .call(
            session,
            "native",
            "droppedStreamNext",
            json!([]),
            false,
            false,
        )
        .unwrap();
    let open = operation(&mut backend, "stream_open");
    reply(&mut backend, &open, json!({"stream":"js-stream"}));
    let mut calls = operations(&mut backend);
    if calls.len() == 1 {
        calls.extend(operations(&mut backend));
    }
    assert_eq!(calls.len(), 2);
    let next = calls
        .iter()
        .find(|call| call["kind"] == "stream_next")
        .unwrap();
    let close = calls
        .iter()
        .find(|call| call["kind"] == "stream_close")
        .unwrap();
    // Model a JS next() which can only finish after return() actually lands.
    reply(&mut backend, close, json!({"done":true}));
    assert_eq!(backend.poll()["jobs"], json!([]));
    reply(&mut backend, next, json!({"done":true}));
    assert_eq!(call_result(&mut backend)["value"], "dropped next");
    cleanup_reverse(&mut backend, &module, session);
}
#[test]
fn dropped_late_native_open_is_journaled_even_after_cancellation() {
    let (mut backend, module, session) = reverse_backend();
    let start = backend
        .call(
            session,
            "native",
            "droppedStreamOpen",
            json!([]),
            false,
            false,
        )
        .unwrap();
    let open = operation(&mut backend, "stream_open");
    backend.cancel_job(number(&start, "job")).unwrap();
    assert_eq!(backend.poll()["jobs"], json!([]));
    reply(&mut backend, &open, json!({"stream":"late-stream"}));
    let close = operation(&mut backend, "stream_close");
    assert_eq!(backend.poll()["jobs"], json!([]));
    reply(&mut backend, &close, json!({"done":true}));
    assert_eq!(call_result(&mut backend)["value"], "dropped open");
    cleanup_reverse(&mut backend, &module, session);
}
#[test]
fn reverse_object_retry_and_callback_validation_preserve_the_resident_journal() {
    let (mut backend, module, session) = reverse_backend();
    backend
        .call(session, "native", "retryObject", json!([]), false, false)
        .unwrap();
    let open = operation(&mut backend, "object_open");
    open_object(&mut backend, &open, json!(["call"]));
    let call = operation(&mut backend, "object_call");
    assert_eq!(backend.poll()["calls"], json!([]));
    reply(&mut backend, &call, json!(42));
    let close = operation(&mut backend, "object_close");
    backend
        .reply(number(&close, "request"), Err("retry object close".into()))
        .unwrap();
    let close = operation(&mut backend, "object_close");
    reply(&mut backend, &close, json!({"closed":true}));
    assert_eq!(call_result(&mut backend)["value"], 42);
    backend
        .call(session, "native", "importCallback", json!([]), false, false)
        .unwrap();
    let open = operation(&mut backend, "object_open");
    open_object(&mut backend, &open, json!(["notCall"]));
    let close = operation(&mut backend, "object_close");
    reply(&mut backend, &close, json!({"closed":true}));
    let result = call_result(&mut backend);
    assert_eq!(result["success"], false);
    assert_eq!(result["error"], "InvalidCallbackDescriptor");
    cleanup_reverse(&mut backend, &module, session);
}
#[test]
fn escaped_reverse_object_keeps_original_action_authority() {
    let (mut backend, module, session) = reverse_backend();
    backend
        .call(session, "native", "escapeObject", json!([]), false, false)
        .unwrap();
    let open = operation(&mut backend, "object_open");
    open_object(&mut backend, &open, json!(["call"]));
    let close = operation(&mut backend, "object_close");
    reply(&mut backend, &close, json!({"closed":true}));
    assert_eq!(call_result(&mut backend)["success"], true);
    backend
        .call(session, "native", "useEscaped", json!([]), false, false)
        .unwrap();
    assert_eq!(call_result(&mut backend)["error"], "ActionClosed");
    cleanup_reverse(&mut backend, &module, session);
}
fn cleanup_import(backend: &mut super::super::Backend, session: u64) -> Value {
    backend.cleanup(session).unwrap();
    let orphan = operation(backend, "close_orphans");
    reply(backend, &orphan, Value::Null);
    let cleanup = resource_call(backend, "cleanup");
    reply(backend, &cleanup, Value::Null);
    let open = operation(backend, "stream_open");
    reply(backend, &open, json!({"stream":"cleanup-stream"}));
    operation(backend, "stream_close")
}
#[test]
fn native_cleanup_waits_for_js_finalization_and_explicit_retry_does_not_repeat_native_hook() {
    let (mut backend, module, session) = reverse_backend_config(json!({"cleanupImport":true}));
    let close = cleanup_import(&mut backend, session);
    backend
        .reply(
            number(&close, "request"),
            Err("retry cleanup stream".into()),
        )
        .unwrap();
    assert_eq!(call_result(&mut backend)["success"], false);
    assert_eq!(module.info()["resources"]["instances"], 1);
    backend.cleanup(session).unwrap();
    let orphan = operation(&mut backend, "close_orphans");
    reply(&mut backend, &orphan, Value::Null);
    let close = operation(&mut backend, "stream_close");
    reply(&mut backend, &close, json!({"done":true}));
    // No second native cleanup RPC. SDK is already in its Cleaned phase.
    assert_eq!(call_result(&mut backend)["success"], true);
    backend.release(session).unwrap();
    assert!(module.info()["resources"]
        .as_object()
        .unwrap()
        .values()
        .all(|value| value == 0));
}
#[test]
fn abandoned_native_cleanup_cannot_destroy_before_pending_js_finalization() {
    let (mut backend, module, session) = reverse_backend_config(json!({"cleanupImport":true}));
    let _close = cleanup_import(&mut backend, session);
    drop(backend);
    assert_eq!(module.info()["resources"]["retainedInstances"], 1);
}
#[test]
fn native_resource_close_drains_its_original_reverse_journal_before_destroy_and_retry() {
    let (mut backend, module, session) = reverse_backend();
    let stream = number(
        &backend
            .call(
                session,
                "native",
                "stream",
                json!(["close-import"]),
                false,
                false,
            )
            .unwrap(),
        "stream",
    );
    backend.stream_close(session, stream).unwrap();
    let hook = resource_call(&mut backend, "streamClose");
    reply(&mut backend, &hook, Value::Null);
    let open = operation(&mut backend, "stream_open");
    reply(&mut backend, &open, json!({"stream":"close-import"}));
    let close = operation(&mut backend, "stream_close");
    backend
        .reply(
            number(&close, "request"),
            Err("retry imported close".into()),
        )
        .unwrap();
    assert_eq!(call_result(&mut backend)["success"], false);
    assert_eq!(module.info()["resources"]["streams"], 1);
    backend.stream_close(session, stream).unwrap();
    let retry = operation(&mut backend, "stream_close");
    assert_eq!(retry["stream"], "close-import");
    reply(&mut backend, &retry, json!({"done":true}));
    assert_eq!(call_result(&mut backend)["success"], true);
    assert_eq!(module.info()["resources"]["streams"], 0);
    cleanup_reverse(&mut backend, &module, session);
}
