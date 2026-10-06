use super::super::Backend;
use super::tests::{call_result, cleanup_reverse, number, reverse_backend, reverse_backend_config};
use super::*;
fn arm(backend: &Backend, session: u64) -> String {
    backend.checkpoint_arm(session).unwrap()["token"]
        .as_str()
        .unwrap()
        .into()
}
fn cleanup(backend: &mut Backend, session: u64) -> (Value, Vec<Value>) {
    backend.cleanup(session).unwrap();
    let mut calls = Vec::new();
    for _ in 0..30 {
        let poll = backend.poll();
        for call in poll["calls"].as_array().unwrap() {
            calls.push(call.clone());
            backend
                .reply(number(call, "request"), Ok(Value::Null))
                .unwrap();
        }
        if let Some(result) = poll["jobs"].as_array().unwrap().first() {
            return (result.clone(), calls);
        }
    }
    panic!("checkpoint cleanup did not finish")
}
fn restore(
    backend: &mut Backend,
    module: &Module,
    token: &str,
    config: Value,
) -> (u64, Value, Vec<Value>) {
    let start = backend
        .native_start(
            100,
            1,
            &module.factory_ref("reverse"),
            config,
            BTreeMap::new(),
            Some(token),
        )
        .unwrap();
    let session = number(&start, "session");
    let mut calls = Vec::new();
    for _ in 0..30 {
        let poll = backend.poll();
        for call in poll["calls"].as_array().unwrap() {
            calls.push(call.clone());
            backend
                .reply(
                    number(call, "request"),
                    Ok(if call["kind"] == "provide" {
                        json!({"publication":"30","port":{"key":"4","realm":"0"}})
                    } else {
                        Value::Null
                    }),
                )
                .unwrap();
        }
        if let Some(result) = poll["jobs"].as_array().unwrap().first() {
            return (session, result.clone(), calls);
        }
    }
    panic!("checkpoint restore did not finish")
}
#[test]
fn checkpoint_captures_after_actual_calls_and_restores_before_setup_without_consuming_token() {
    let (mut backend, module, session) = reverse_backend();
    let token = arm(&backend, session);
    assert_eq!(
        module.info()["factories"][0]["checkpointSchema"]["schema"],
        "probe.counter"
    );
    backend
        .call(session, "native", "increment", json!([]), false, false)
        .unwrap();
    let poll = backend.poll();
    let call = &poll["calls"][0];
    assert_eq!(call["method"], "increment");
    assert_eq!(backend.cleanup(session).unwrap_err(), "SessionBusy");
    assert_eq!(backend.checkpoint_read(&token).unwrap()["state"], "armed");
    backend
        .reply(number(call, "request"), Ok(Value::Null))
        .unwrap();
    assert_eq!(call_result(&mut backend)["value"], 1);
    backend.cleanup(session).unwrap();
    let mut complete = false;
    for _ in 0..20 {
        let poll = backend.poll();
        for call in poll["calls"].as_array().unwrap() {
            if call["kind"] == "call" {
                let read = backend.checkpoint_read(&token).unwrap();
                assert_eq!(read["value"]["data"]["value"], 1);
                assert_eq!(read["retired"], false);
                assert_eq!(
                    backend
                        .native_start(
                            100,
                            1,
                            &module.factory_ref("reverse"),
                            Value::Null,
                            BTreeMap::new(),
                            Some(&token)
                        )
                        .unwrap_err(),
                    "NativeCheckpointSourceNotRetired"
                );
            }
            backend
                .reply(number(call, "request"), Ok(Value::Null))
                .unwrap();
        }
        if !poll["jobs"].as_array().unwrap().is_empty() {
            assert_eq!(poll["jobs"][0]["success"], true);
            complete = true;
            break;
        }
    }
    assert!(complete);
    backend.release(session).unwrap();
    let read = backend.checkpoint_read(&token).unwrap();
    assert_eq!(read["retired"], true);
    assert_eq!(read["source"]["session"], session.to_string());
    for _ in 0..2 {
        let (next, result, calls) = restore(&mut backend, &module, &token, Value::Null);
        assert_eq!(result["success"], true, "{result}");
        assert_eq!(calls[0]["method"], "setup");
        assert_eq!(calls[0]["args"], json!([1]));
        cleanup_reverse(&mut backend, &module, next);
    }
    backend.checkpoint_drop(&token).unwrap();
    assert_eq!(backend.module_info()["checkpoints"]["bytes"], 0);
    assert_eq!(backend.module_info()["checkpoints"]["tokens"], 0);
}
#[test]
fn checkpoint_capture_failure_blocks_native_cleanup_and_only_explicit_retry_captures_again() {
    let (mut backend, module, session) = reverse_backend_config(json!({"failCapture":true}));
    let token = arm(&backend, session);
    let (first, calls) = cleanup(&mut backend, session);
    assert_eq!(first["error"], "ProbeCheckpointFailed");
    assert!(!calls.iter().any(|call| call["method"] == "cleanup"));
    let read = backend.checkpoint_read(&token).unwrap();
    assert_eq!(read["state"], "failed");
    assert_eq!(read["failure"], "ProbeCheckpointFailed");
    assert!(read.get("error").is_none());
    assert_eq!(read["retired"], false);
    assert!(read.get("value").is_none());
    assert_eq!(backend.poll()["jobs"], json!([]));
    let (second, _) = cleanup(&mut backend, session);
    assert_eq!(second["success"], true);
    backend.release(session).unwrap();
    assert_eq!(
        backend.checkpoint_read(&token).unwrap()["value"]["data"]["attempt"],
        2
    );
    backend.checkpoint_drop(&token).unwrap();
    assert_eq!(module.info()["resources"]["instances"], 0);
}
#[test]
fn checkpoint_success_is_frozen_across_cleanup_retry_and_restore_failure_cleans_partial_instance() {
    let (mut backend, module, session) = reverse_backend_config(json!({"failCleanup":true}));
    let token = arm(&backend, session);
    let (first, _) = cleanup(&mut backend, session);
    assert_eq!(first["error"], "ProbeCleanupFailed");
    let value = backend.checkpoint_read(&token).unwrap()["value"].clone();
    assert_eq!(value["data"], json!({"value":0,"attempt":1}));
    let (second, _) = cleanup(&mut backend, session);
    assert_eq!(second["success"], true);
    backend.release(session).unwrap();
    assert_eq!(backend.checkpoint_read(&token).unwrap()["value"], value);
    let (candidate, result, calls) =
        restore(&mut backend, &module, &token, json!({"failRestore":true}));
    assert_eq!(result["error"], "ProbeRestoreFailed");
    assert!(calls.is_empty());
    cleanup_reverse(&mut backend, &module, candidate);
    let (rollback, result, calls) = restore(&mut backend, &module, &token, Value::Null);
    assert_eq!(result["success"], true);
    assert_eq!(calls[0]["args"], json!([0]));
    cleanup_reverse(&mut backend, &module, rollback);
    backend.checkpoint_drop(&token).unwrap();
}
#[test]
fn checkpoint_arming_can_be_cancelled_and_invalid_restore_never_creates_instance() {
    let (mut backend, module, session) = reverse_backend();
    let token = arm(&backend, session);
    assert_eq!(
        backend.checkpoint_arm(session).unwrap_err(),
        "NativeCheckpointAlreadyArmed"
    );
    assert_eq!(
        backend
            .native_start(
                100,
                1,
                &module.factory_ref("reverse"),
                Value::Null,
                BTreeMap::new(),
                Some(&token)
            )
            .unwrap_err(),
        "NativeCheckpointNotCaptured"
    );
    assert_eq!(module.info()["resources"]["instances"], 1);
    backend.checkpoint_drop(&token).unwrap();
    assert_eq!(
        backend.checkpoint_read(&token).unwrap_err(),
        "UnknownNativeCheckpoint"
    );
    cleanup_reverse(&mut backend, &module, session);
    assert_eq!(backend.module_info()["checkpoints"]["tokens"], 0);
}
#[test]
fn checkpoint_restoration_checks_factory_and_schema_before_allocating() {
    let (mut backend, module, session) = reverse_backend();
    let token = arm(&backend, session);
    assert_eq!(cleanup(&mut backend, session).0["success"], true);
    backend.release(session).unwrap();
    assert_eq!(
        backend
            .native_start(
                100,
                1,
                &module.factory_ref("probe-leaf"),
                Value::Null,
                BTreeMap::new(),
                Some(&token)
            )
            .unwrap_err(),
        "NativeCheckpointIdentityMismatch"
    );
    assert_eq!(
        backend
            .native_start(
                100,
                1,
                "unknown",
                Value::Null,
                BTreeMap::new(),
                Some(&token)
            )
            .unwrap_err(),
        "NativeCheckpointUnsupported"
    );
    assert_eq!(module.info()["resources"]["instances"], 0);
    backend.checkpoint_drop(&token).unwrap();
}

#[test]
fn checkpoints_are_backend_scoped_and_capacity_is_reclaimed_only_by_explicit_drop() {
    let (mut first, one, a) = reverse_backend();
    let (mut second, two, b) = reverse_backend();
    let token_a = arm(&first, a);
    let token_b = arm(&second, b);
    assert_ne!(token_a, token_b);
    assert_eq!(
        first.checkpoint_read(&token_b).unwrap_err(),
        "UnknownNativeCheckpoint"
    );
    assert_eq!(
        second.checkpoint_drop(&token_a).unwrap_err(),
        "UnknownNativeCheckpoint"
    );
    let mut sessions = vec![a];
    let mut tokens = vec![token_a];
    for id in 2..=65 {
        let started = first
            .native_start(
                id,
                1,
                &one.factory_ref("reverse"),
                Value::Null,
                BTreeMap::new(),
                None,
            )
            .unwrap();
        let session = number(&started, "session");
        let mut ready = false;
        for _ in 0..20 {
            let poll = first.poll();
            for call in poll["calls"].as_array().unwrap() {
                first.reply(number(call,"request"),Ok(if call["kind"]=="provide"{json!({"publication":(id+100).to_string(),"port":{"key":"4","realm":"0"}})}else{Value::Null})).unwrap();
            }
            if !poll["jobs"].as_array().unwrap().is_empty() {
                assert_eq!(poll["jobs"][0]["success"], true);
                ready = true;
                break;
            }
        }
        assert!(ready);
        sessions.push(session);
        if id < 65 {
            tokens.push(arm(&first, session));
        } else {
            assert_eq!(
                first.checkpoint_arm(session).unwrap_err(),
                "NativeCheckpointTokenCapacity"
            );
        }
    }
    assert_eq!(first.module_info()["checkpoints"]["tokens"], 64);
    first.checkpoint_drop(&tokens.remove(0)).unwrap();
    tokens.push(arm(&first, *sessions.last().unwrap()));
    for token in tokens {
        first.checkpoint_drop(&token).unwrap();
    }
    assert_eq!(first.module_info()["checkpoints"]["bytes"], 0);
    for session in sessions {
        assert_eq!(cleanup(&mut first, session).0["success"], true);
        first.release(session).unwrap();
    }
    second.checkpoint_drop(&token_b).unwrap();
    cleanup_reverse(&mut second, &two, b);
    assert!(one.info()["resources"]
        .as_object()
        .unwrap()
        .values()
        .all(|v| v == 0));
}
