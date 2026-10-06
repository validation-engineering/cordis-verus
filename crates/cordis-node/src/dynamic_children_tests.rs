use super::super::Backend;
use super::tests::{call_result, cleanup_reverse, number, reverse_backend};
use super::*;
use cordis_driver::ServicePort;
fn ports(anchor: &str) -> BTreeMap<String, ServicePort> {
    BTreeMap::from([
        ("js".into(), ServicePort { key: 1, realm: 0 }),
        ("leaf".into(), ServicePort { key: 2, realm: 0 }),
        (anchor.into(), ServicePort { key: 3, realm: 10 }),
    ])
}
fn parent() -> (Backend, Arc<Module>, u64) {
    let (mut backend, module, session) = reverse_backend();
    backend.sessions.get_mut(&session).unwrap().ports = BTreeMap::from([
        ("js".into(), ServicePort { key: 1, realm: 0 }),
        ("native".into(), ServicePort { key: 4, realm: 0 }),
        (
            "__cordis_native_anchor_parent".into(),
            ServicePort { key: 3, realm: 9 },
        ),
    ]);
    (backend, module, session)
}
fn create(backend: &mut Backend, session: u64, method: &str, config: Value) -> Value {
    backend
        .call(session, "native", method, config, false, false)
        .unwrap();
    for _ in 0..10 {
        let poll = backend.poll();
        assert_eq!(poll["jobs"], json!([]), "{poll}");
        if let Some(action) = poll["children"].as_array().unwrap().first() {
            return action.clone();
        }
    }
    panic!("child mount missing")
}
fn invoke(backend: &mut Backend, session: u64, method: &str) -> Value {
    backend
        .call(session, "native", method, Value::Null, false, false)
        .unwrap();
    call_result(backend)
}
fn start(backend: &mut Backend, action: &Value, generation: u64, config: Value) -> u64 {
    let start = backend
        .native_start(
            2,
            generation,
            action["factory"]["ref"].as_str().unwrap(),
            config,
            ports("__cordis_native_anchor_child"),
            None,
        )
        .unwrap();
    for _ in 0..10 {
        let poll = backend.poll();
        for call in poll["calls"].as_array().unwrap() {
            assert_eq!(call["kind"], "provide");
            backend
                .reply(
                    number(call, "request"),
                    Ok(json!({"publication":"9","port":{"key":"2","realm":"0"}})),
                )
                .unwrap();
        }
        if !poll["jobs"].as_array().unwrap().is_empty() {
            assert_eq!(poll["jobs"][0]["success"], true, "{poll}");
            return number(&start, "session");
        }
    }
    panic!("child setup incomplete")
}
fn cleanup_child(backend: &mut Backend, session: u64) -> Value {
    backend.cleanup(session).unwrap();
    for _ in 0..10 {
        let poll = backend.poll();
        for call in poll["calls"].as_array().unwrap() {
            assert_eq!(call["kind"], "close_orphans");
            backend
                .reply(number(call, "request"), Ok(Value::Null))
                .unwrap();
        }
        if let Some(result) = poll["jobs"].as_array().unwrap().first() {
            if result["success"] == true {
                backend.release(session).unwrap();
            }
            return result.clone();
        }
    }
    panic!("child cleanup did not finish")
}
#[test]
fn native_retained_child_reactivates_original_definition_until_real_removed() {
    let (mut backend, module, session) = parent();
    let action = create(&mut backend, session, "publishChild", json!({}));
    let key = action["child"].as_str().unwrap();
    assert_eq!(action["native"], true);
    assert_eq!(action["factory"]["nativeChildren"], true);
    assert_eq!(action["factory"]["inherited"].as_array().unwrap().len(), 2);
    backend
        .native_child_mounted(key, 2, ports("__cordis_native_anchor_child"))
        .unwrap();
    assert_eq!(call_result(&mut backend)["success"], true);
    let first = start(&mut backend, &action, 1, json!({}));
    backend
        .native_child_observed(key, true, None, false)
        .unwrap();
    assert_eq!(invoke(&mut backend, session, "childReady")["success"], true);
    assert_eq!(cleanup_child(&mut backend, first)["success"], true);
    backend
        .native_child_observed(key, false, None, false)
        .unwrap();
    assert_eq!(
        invoke(&mut backend, session, "childStatus")["value"]["initialized"],
        false
    );
    let second = start(&mut backend, &action, 2, json!({}));
    assert_ne!(first, second);
    assert_eq!(cleanup_child(&mut backend, second)["success"], true);
    backend.forget_typed(2).unwrap();
    backend.forget_typed(2).unwrap();
    assert_eq!(
        invoke(&mut backend, session, "childStatus")["value"]["removed"],
        true
    );
    assert_eq!(invoke(&mut backend, session, "childJoin")["success"], true);
    cleanup_reverse(&mut backend, &module, session);
    assert!(backend.native_children.is_empty());
}
#[test]
fn native_allocated_failure_join_waits_for_removed_and_cleanup_retry_uses_existing_node() {
    let (mut backend, module, session) = parent();
    let action = create(
        &mut backend,
        session,
        "publishChild",
        json!({"failCleanup":true}),
    );
    let key = action["child"].as_str().unwrap();
    backend
        .native_child_mounted(key, 2, ports("__cordis_native_anchor_child"))
        .unwrap();
    assert_eq!(call_result(&mut backend)["success"], true);
    let child = start(&mut backend, &action, 1, json!({"failCleanup":true}));
    backend
        .native_child_aborted(key, "observer failed".into())
        .unwrap();
    backend
        .call(session, "native", "childJoin", Value::Null, false, false)
        .unwrap();
    for _ in 0..3 {
        assert_eq!(backend.poll()["jobs"], json!([]));
    }
    assert_eq!(
        cleanup_child(&mut backend, child)["error"],
        "ProbeChildCleanupFailed"
    );
    backend
        .native_child_observed(key, false, Some("ProbeChildCleanupFailed".into()), true)
        .unwrap();
    assert_eq!(
        call_result(&mut backend)["error"],
        "ProbeChildCleanupFailed"
    );
    backend
        .call(session, "native", "childRetry", Value::Null, false, false)
        .unwrap();
    let poll = backend.poll();
    assert_eq!(poll["children"][0]["kind"], "retry");
    assert_eq!(poll["children"][0]["id"], "2");
    assert_eq!(poll["jobs"], json!([]));
    assert_eq!(cleanup_child(&mut backend, child)["success"], true);
    backend.forget_typed(2).unwrap();
    assert_eq!(call_result(&mut backend)["success"], true);
    cleanup_reverse(&mut backend, &module, session);
}
#[test]
fn native_preallocation_rejection_releases_definition_but_postallocation_does_not() {
    let (mut backend, module, session) = parent();
    let action = create(&mut backend, session, "publishChild", Value::Null);
    let key = action["child"].as_str().unwrap();
    backend
        .native_child_rejected(key, "admission denied".into())
        .unwrap();
    assert_eq!(call_result(&mut backend)["error"], "admission denied");
    let action = create(&mut backend, session, "mountChild", Value::Null);
    let key = action["child"].as_str().unwrap();
    assert!(backend
        .native_child_mounted(key, 2, BTreeMap::new())
        .unwrap_err()
        .contains("PortsInvalid"));
    assert!(backend
        .native_child_rejected(key, "bad".into())
        .unwrap_err()
        .contains("AlreadyMounted"));
    assert_eq!(call_result(&mut backend)["success"], true);
    backend.forget_typed(2).unwrap();
    cleanup_reverse(&mut backend, &module, session);
}
#[test]
fn native_child_self_join_and_sealed_ports_are_enforced() {
    let (mut backend, module, session) = parent();
    let action = create(&mut backend, session, "publishChild", Value::Null);
    let key = action["child"].as_str().unwrap();
    backend
        .native_child_mounted(key, 2, ports("__cordis_native_anchor_child"))
        .unwrap();
    call_result(&mut backend);
    let bad = ports("__cordis_native_anchor_altered");
    assert_eq!(
        backend
            .native_start(
                2,
                1,
                action["factory"]["ref"].as_str().unwrap(),
                Value::Null,
                bad,
                None,
            )
            .unwrap_err(),
        "NativeChildMountChanged"
    );
    let started = backend
        .call(session, "native", "childJoin", Value::Null, false, false)
        .unwrap();
    backend.typed_job_join_blocks(
        number(&started, "job"),
        std::collections::BTreeSet::from([2]),
    );
    assert_eq!(call_result(&mut backend)["error"], "ReentrantServiceJoin");
    let started = backend
        .call(session, "native", "childReady", Value::Null, false, false)
        .unwrap();
    backend
        .jobs
        .get_mut(&number(&started, "job"))
        .unwrap()
        .context
        .setup = true;
    // The future captures its own context clone, so the graph-derived set is the shared guard.
    backend.typed_job_join_blocks(
        number(&started, "job"),
        std::collections::BTreeSet::from([2]),
    );
    assert_eq!(call_result(&mut backend)["error"], "ReentrantServiceJoin");
    backend.forget_typed(2).unwrap();
    cleanup_reverse(&mut backend, &module, session);
}

#[test]
fn native_child_status_and_join_bound_external_failure_without_losing_removed_barrier() {
    let (mut backend, module, session) = parent();
    let action = create(&mut backend, session, "publishChild", Value::Null);
    let key = action["child"].as_str().unwrap();
    backend
        .native_child_mounted(key, 2, ports("__cordis_native_anchor_child"))
        .unwrap();
    call_result(&mut backend);
    backend
        .native_child_aborted(key, "x".repeat(MAX_MESSAGE_BYTES))
        .unwrap();
    assert_eq!(
        invoke(&mut backend, session, "childStatus")["value"]["error"],
        "PluginErrorTooLarge"
    );
    backend
        .call(session, "native", "childJoin", Value::Null, false, false)
        .unwrap();
    assert_eq!(backend.poll()["jobs"], json!([]));
    backend.forget_typed(2).unwrap();
    assert_eq!(call_result(&mut backend)["error"], "PluginErrorTooLarge");
    cleanup_reverse(&mut backend, &module, session);
}

#[test]
fn native_successful_reactivation_clears_current_error_but_join_keeps_history() {
    let (mut backend, module, session) = parent();
    let action = create(&mut backend, session, "publishChild", Value::Null);
    let key = action["child"].as_str().unwrap();
    backend
        .native_child_mounted(key, 2, ports("__cordis_native_anchor_child"))
        .unwrap();
    call_result(&mut backend);
    backend
        .native_child_observed(key, false, Some("temporary setup failure".into()), false)
        .unwrap();
    assert_eq!(
        invoke(&mut backend, session, "childReady")["error"],
        "temporary setup failure"
    );
    backend
        .native_child_observed(key, true, None, false)
        .unwrap();
    assert_eq!(
        invoke(&mut backend, session, "childStatus")["value"]["error"],
        Value::Null
    );
    assert_eq!(invoke(&mut backend, session, "childReady")["success"], true);
    backend.forget_typed(2).unwrap();
    assert_eq!(
        invoke(&mut backend, session, "childJoin")["error"],
        "temporary setup failure"
    );
    cleanup_reverse(&mut backend, &module, session);
}
