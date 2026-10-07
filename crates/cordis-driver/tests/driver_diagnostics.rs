//! Snapshot reads explain real protocol state without admitting or driving work.
use cordis_driver::{ActionTicket, Driver, HostAction, ServicePort};
use serde_json::{json, Value};

const PORT: ServicePort = ServicePort { key: 1, realm: 0 };
const SENTINEL: u64 = 18446744073709551234;
fn command(driver: &mut Driver, value: Value) -> Value {
    serde_json::from_str(&driver.command(&value.to_string()).unwrap()).unwrap()
}
fn action(driver: &mut Driver, id: usize, kind: &str) -> ActionTicket {
    let actions = driver.drive().unwrap();
    assert_eq!(actions.len(), 1, "unexpected batch: {actions:?}");
    match &actions[0] {
        HostAction::Setup { id: owner, ticket } if kind == "setup" && *owner == id => {
            ticket.clone()
        }
        HostAction::Cleanup { id: owner, ticket } if kind == "cleanup" && *owner == id => {
            ticket.clone()
        }
        _ => panic!("unexpected action: {actions:?}"),
    }
}
fn provider(
    driver: &mut Driver,
    port: ServicePort,
    checked: bool,
) -> (usize, ActionTicket, String) {
    let id = driver.mount(None, vec![], vec![]).unwrap();
    let ticket = action(driver, id, "setup");
    let publication = command(driver, json!({
        "op":"publish", "id": id.to_string(), "generation": ticket.generation.to_string(),
        "key": port.key.to_string(), "realm": port.realm.to_string(), "value": SENTINEL.to_string(), "check": checked,
    }))["publication"].as_str().unwrap().to_owned();
    driver.complete(ticket.clone(), true, None).unwrap();
    (id, ticket, publication)
}
fn plugin(driver: &Driver, id: usize) -> Value {
    let identity = id.to_string();
    driver.snapshot()["plugins"]
        .as_array()
        .unwrap()
        .iter()
        .find(|plugin| plugin["id"] == identity)
        .unwrap()
        .clone()
}
fn blockers(driver: &Driver, id: usize) -> Value {
    plugin(driver, id)["blockers"].clone()
}
fn state_projection(snapshot: &Value) -> Value {
    let plugins: Vec<_> = snapshot["plugins"]
        .as_array()
        .unwrap()
        .iter()
        .map(|plugin| {
            let mut state = serde_json::Map::new();
            for key in [
                "id",
                "generation",
                "parent",
                "state",
                "retired",
                "error",
                "cleanupFailed",
                "pendingAction",
            ] {
                state.insert(key.to_owned(), plugin[key].clone());
            }
            Value::Object(state)
        })
        .collect();
    json!({"abi": snapshot["abi"], "profile": snapshot["profile"], "domain": snapshot["domain"], "plugins": plugins})
}

fn stable(driver: &mut Driver) -> Value {
    let before = driver.snapshot();
    for _ in 0..5 {
        assert_eq!(driver.snapshot(), before);
        assert_eq!(command(driver, json!({"op":"snapshot"})), before);
        assert_eq!(driver.snapshot_state(), state_projection(&before));
        assert_eq!(
            command(driver, json!({"op":"snapshot_state"})),
            state_projection(&before)
        );
    }
    assert!(!before.to_string().contains(&SENTINEL.to_string()));
    before
}

#[test]
fn missing_realm_and_unavailable_provider_have_distinct_payload_free_reasons() {
    let mut driver = Driver::new().unwrap();
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    assert_eq!(
        blockers(&driver, consumer),
        json!([{ "code":"MissingProvider", "port":PORT }])
    );
    assert_eq!(plugin(&driver, consumer)["dependencies"], json!([PORT]));
    assert_eq!(plugin(&driver, consumer)["target"], Value::Null);
    stable(&mut driver);
    let (other, _, _) = provider(&mut driver, ServicePort { key: 1, realm: 7 }, false);
    assert_eq!(
        blockers(&driver, consumer),
        json!([{ "code":"RealmMismatch", "port":PORT, "observedRealms":["7"] }])
    );
    // A no-dependency plugin is not blocked by someone else's missing port.
    assert_eq!(blockers(&driver, other), json!([]));
    let declared = driver.mount(None, vec![], vec![PORT]).unwrap();
    assert_eq!(
        blockers(&driver, consumer),
        json!([{
            "code":"ProviderUnavailable", "port": PORT,
            "providers":[{"id":declared.to_string(),"generation":"0","state":"Pending","retired":false}]
        }])
    );
    stable(&mut driver);
    // Reading did not start the declared provider's setup.
    let ticket = action(&mut driver, declared, "setup");
    assert_eq!(plugin(&driver, declared)["pendingAction"], json!(ticket));
    assert_eq!(
        blockers(&driver, consumer)[0]["providers"][0]["state"],
        "Loading"
    );
}

#[test]
fn check_not_evaluated_pending_rejected_error_and_accepted_are_cached_observations() {
    let mut driver = Driver::new().unwrap();
    let (owner, _, publication) = provider(&mut driver, PORT, true);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    assert_eq!(
        blockers(&driver, consumer),
        json!([{
            "code":"CheckNotEvaluated", "port":PORT, "provider":owner.to_string(), "publication":publication,
        }])
    );
    stable(&mut driver);
    let checks = driver.check_actions().unwrap();
    assert_eq!(checks.len(), 1);
    assert_eq!(checks[0].ticket.action, 0, "reads must not allocate checks");
    assert_eq!(blockers(&driver, consumer)[0]["code"], "CheckPending");
    assert_eq!(
        blockers(&driver, consumer)[0]["ticket"],
        json!(checks[0].ticket)
    );
    stable(&mut driver);
    command(
        &mut driver,
        json!({"op":"complete_check", "ticket": checks[0].ticket, "available":false}),
    );
    assert_eq!(blockers(&driver, consumer)[0]["code"], "CheckRejected");
    stable(&mut driver);
    assert!(driver.check_actions().unwrap().is_empty());
    let checks = command(&mut driver, json!({"op":"notify","ports":[PORT]}));
    let ticket = checks["checks"][0]["ticket"].clone();
    command(
        &mut driver,
        json!({"op":"complete_check", "ticket":ticket,"available":false,"error":"predicate failed"}),
    );
    assert_eq!(blockers(&driver, consumer)[0]["code"], "CheckError");
    assert_eq!(blockers(&driver, consumer)[0]["error"], "predicate failed");
    stable(&mut driver);
    let checks = command(&mut driver, json!({"op":"notify","ports":[PORT]}));
    command(
        &mut driver,
        json!({"op":"complete_check", "ticket":checks["checks"][0]["ticket"],"available":true}),
    );
    assert_eq!(blockers(&driver, consumer), json!([]));
    stable(&mut driver);
    let setup = action(&mut driver, consumer, "setup");
    assert_eq!(setup.generation, 1);
}

#[test]
fn invalidated_check_is_not_reported_as_a_predicate_rejection() {
    let mut driver = Driver::new().unwrap();
    let (owner, setup, publication) = provider(&mut driver, PORT, true);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let ticket = driver.check_actions().unwrap()[0].ticket.clone();
    driver
        .set(
            owner,
            setup.generation,
            publication.parse().unwrap(),
            SENTINEL - 1,
        )
        .unwrap();
    assert_eq!(blockers(&driver, consumer)[0]["code"], "CheckInvalidated");
    stable(&mut driver);
    let response = command(
        &mut driver,
        json!({"op":"complete_check","ticket":ticket,"available":true}),
    );
    assert_eq!(response["accepted"], false);
    assert_eq!(blockers(&driver, consumer)[0]["code"], "CheckInvalidated");
    stable(&mut driver);
    assert!(driver.check_actions().unwrap().is_empty());
}

#[test]
fn successful_cached_check_is_not_blocked_by_a_new_check_in_flight() {
    let mut driver = Driver::new().unwrap();
    provider(&mut driver, PORT, true);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let ticket = driver.check_actions().unwrap()[0].ticket.clone();
    command(
        &mut driver,
        json!({"op":"complete_check","ticket":ticket,"available":true}),
    );
    let ticket = action(&mut driver, consumer, "setup");
    driver.complete(ticket, true, None).unwrap();
    let checks = command(&mut driver, json!({"op":"notify","ports":[PORT]}));
    assert_eq!(checks["checks"].as_array().unwrap().len(), 1);
    // Current lifecycle readiness still uses the successful cached observation.
    assert_eq!(blockers(&driver, consumer), json!([]));
    stable(&mut driver);
    assert!(driver.drive().unwrap().is_empty());
}

#[test]
fn committed_publication_is_separate_from_the_current_target_even_for_the_same_owner() {
    let mut driver = Driver::new().unwrap();
    let (owner, setup, original) = provider(&mut driver, PORT, false);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let ticket = action(&mut driver, consumer, "setup");
    driver.complete(ticket, true, None).unwrap();
    driver
        .revoke(owner, setup.generation, original.parse().unwrap())
        .unwrap();
    assert_eq!(blockers(&driver, consumer)[0]["code"], "PublicationMissing");
    stable(&mut driver);
    let replacement = driver
        .publish(owner, setup.generation, PORT, SENTINEL - 1)
        .unwrap();
    let snapshot = stable(&mut driver);
    let consumer_identity = consumer.to_string();
    let consumer_view = snapshot["plugins"]
        .as_array()
        .unwrap()
        .iter()
        .find(|node| node["id"] == consumer_identity)
        .unwrap();
    assert_eq!(consumer_view["state"], "Active");
    assert_eq!(consumer_view["committed"][0]["provider"], owner.to_string());
    assert_eq!(consumer_view["target"][0]["provider"], owner.to_string());
    assert_eq!(consumer_view["committed"][0]["publication"], original);
    assert_eq!(
        consumer_view["target"][0]["publication"],
        replacement.to_string()
    );
    assert_eq!(consumer_view["blockers"], json!([]));
    assert_eq!(snapshot["storage"]["liveLeases"], 1);
}

#[test]
fn cleanup_waits_identify_consumer_episode_and_retry_keeps_its_lease_until_success() {
    let mut driver = Driver::new().unwrap();
    let (owner, _, publication) = provider(&mut driver, PORT, false);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let setup = action(&mut driver, consumer, "setup");
    driver.complete(setup.clone(), true, None).unwrap();
    driver.retire(owner).unwrap();
    let cleanup = action(&mut driver, consumer, "cleanup");
    assert_eq!(
        blockers(&driver, owner),
        json!([{
            "code":"CommittedConsumers","consumers":[{"id":consumer.to_string(),"generation":setup.generation.to_string()}]
        }])
    );
    assert_eq!(
        blockers(&driver, consumer),
        json!([{"code":"PendingAction","ticket":cleanup}])
    );
    let before = stable(&mut driver);
    assert_eq!(before["storage"]["liveLeases"], 1);
    assert_eq!(
        plugin(&driver, consumer)["committed"][0]["publication"],
        publication
    );
    assert!(driver.drive().unwrap().is_empty());
    driver
        .complete(cleanup.clone(), false, Some("inverse rejected".into()))
        .unwrap();
    assert_eq!(
        blockers(&driver, consumer),
        json!([{"code":"CleanupFailed","error":"inverse rejected","retryable":true}])
    );
    stable(&mut driver);
    assert!(driver.drive().unwrap().is_empty());
    let HostAction::Cleanup { ticket, .. } = driver.retry_cleanup(consumer).unwrap() else {
        panic!()
    };
    assert_ne!(cleanup.action, ticket.action);
    stable(&mut driver);
    assert_eq!(
        blockers(&driver, consumer),
        json!([{"code":"PendingAction","ticket":ticket}])
    );
    driver.complete(ticket, true, None).unwrap();
    assert_eq!(plugin(&driver, consumer)["committed"], json!([]));
    assert_eq!(blockers(&driver, owner), json!([]));
    assert_eq!(stable(&mut driver)["storage"]["liveLeases"], 0);
    action(&mut driver, owner, "cleanup");
}

#[test]
fn retiring_child_only_blocks_next_episode_or_removal_not_parent_cleanup() {
    let mut driver = Driver::new().unwrap();
    let parent = driver.mount(None, vec![], vec![]).unwrap();
    let setup = action(&mut driver, parent, "setup");
    driver.complete(setup, true, None).unwrap();
    let child = driver.mount(Some(parent), vec![], vec![]).unwrap();
    let child_setup = action(&mut driver, child, "setup");
    driver.restart(parent).unwrap();
    let cleanup = action(&mut driver, parent, "cleanup");
    assert_eq!(
        blockers(&driver, parent),
        json!([{"code":"PendingAction","ticket":cleanup}])
    );
    driver.complete(cleanup, true, None).unwrap();
    assert_eq!(
        blockers(&driver, parent),
        json!([{
            "code":"RetiringChildren","children":[{"id":child.to_string(),"generation":child_setup.generation.to_string()}]
        }])
    );
    stable(&mut driver);
    assert!(driver.drive().unwrap().is_empty());
    driver.complete(child_setup, true, None).unwrap();
    let cleanup = action(&mut driver, child, "cleanup");
    driver.complete(cleanup, true, None).unwrap();
    let actions = driver.drive().unwrap();
    assert!(actions
        .iter()
        .any(|action| matches!(action, HostAction::Removed { id } if *id == child)));
    assert!(actions
        .iter()
        .any(|action| matches!(action, HostAction::Setup { id, .. } if *id == parent)));
    assert_eq!(blockers(&driver, parent).as_array().unwrap().len(), 1);
    assert_eq!(blockers(&driver, parent)[0]["code"], "PendingAction");
}

#[test]
fn reserved_unsealed_and_failed_setup_have_real_non_dependency_reasons() {
    let mut driver = Driver::new().unwrap();
    let id = command(&mut driver, json!({"op":"mount","sealed":false}))["id"]
        .as_str()
        .unwrap()
        .parse()
        .unwrap();
    assert_eq!(blockers(&driver, id), json!([{"code":"Unsealed"}]));
    stable(&mut driver);
    command(
        &mut driver,
        json!({"op":"seal","id":id.to_string(),"dependencies":[]}),
    );
    let setup = action(&mut driver, id, "setup");
    driver
        .complete(setup, false, Some("setup rejected".into()))
        .unwrap();
    let cleanup = action(&mut driver, id, "cleanup");
    driver.complete(cleanup, true, None).unwrap();
    assert_eq!(
        blockers(&driver, id),
        json!([{"code":"Failed","error":"setup rejected"}])
    );
    stable(&mut driver);
    assert!(driver.drive().unwrap().is_empty());
}

#[test]
fn target_preserves_kernel_identity_until_retained_dependency_can_be_reconciled() {
    let mut driver = Driver::new().unwrap();
    let (old, setup, original) = provider(&mut driver, PORT, false);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let ticket = action(&mut driver, consumer, "setup");
    driver.complete(ticket, true, None).unwrap();
    driver
        .revoke(old, setup.generation, original.parse().unwrap())
        .unwrap();
    let cleanup = action(&mut driver, consumer, "cleanup");
    let (new, _, replacement) = provider(&mut driver, PORT, false);
    stable(&mut driver);
    let view = plugin(&driver, consumer);
    assert_eq!(view["state"], "Unloading");
    assert_eq!(view["committed"][0]["provider"], old.to_string());
    assert_eq!(view["committed"][0]["publication"], original);
    // Dynamic publication visibility changes before the kernel may release
    // the old provider declaration; snapshot must not pretend these coincide.
    assert_eq!(view["target"][0]["provider"], old.to_string());
    assert_eq!(view["target"][0]["publication"], Value::Null);
    assert_eq!(
        driver.resolve(PORT, None, None).unwrap().unwrap()["publication"],
        replacement
    );
    assert_eq!(
        view["blockers"],
        json!([{"code":"PendingAction","ticket":cleanup}])
    );
    assert_eq!(
        driver.resolve(PORT, Some(consumer), None).unwrap().unwrap()["owner"],
        old.to_string()
    );
    assert!(driver.drive().unwrap().is_empty());
    driver.complete(cleanup, true, None).unwrap();
    let setup = action(&mut driver, consumer, "setup");
    assert_eq!(setup.generation, 2);
    assert_eq!(
        plugin(&driver, consumer)["committed"][0]["provider"],
        new.to_string()
    );
}

#[test]
fn active_target_mismatch_is_reported_without_withdrawing_or_advancing_actions() {
    let mut driver = Driver::new().unwrap();
    let (owner, setup, _) = provider(&mut driver, PORT, false);
    driver.retire(owner).unwrap();
    let view = plugin(&driver, owner);
    assert_eq!(view["state"], "Active");
    assert_eq!(view["committed"], json!([]));
    assert_eq!(view["target"], Value::Null);
    assert_eq!(view["blockers"], json!([{"code":"TargetChanged"}]));
    stable(&mut driver);
    let cleanup = action(&mut driver, owner, "cleanup");
    assert_eq!(
        cleanup.action,
        setup.action + 1,
        "reads must not allocate actions"
    );
}

#[test]
fn lightweight_state_reads_preserve_unrequested_and_pending_checks() {
    let mut driver = Driver::new().unwrap();
    provider(&mut driver, PORT, true);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let expected = state_projection(&driver.snapshot());
    for _ in 0..5 {
        assert_eq!(
            command(&mut driver, json!({"op":"snapshot_state"})),
            expected
        );
    }
    let ticket = driver.check_actions().unwrap()[0].ticket.clone();
    assert_eq!(ticket.action, 0, "state reads must not request checks");
    stable(&mut driver);
    assert_eq!(
        command(&mut driver, json!({"op":"validate_check", "ticket":ticket}))["current"],
        true
    );
    assert_eq!(
        command(
            &mut driver,
            json!({"op":"complete_check", "ticket":ticket, "available":true})
        )["accepted"],
        true
    );
    let setup = action(&mut driver, consumer, "setup");
    assert_eq!(setup.generation, 1);
    stable(&mut driver);
}

#[test]
fn lightweight_state_preserves_generation_zero_cleanup_failure_and_retry_identity() {
    let mut driver = Driver::new().unwrap();
    let id = command(&mut driver, json!({"op":"mount", "sealed":false}))["id"].clone();
    command(&mut driver, json!({"op":"prepare", "id":id}));
    command(&mut driver, json!({"op":"retire", "id":id}));
    stable(&mut driver);
    let id = id.as_str().unwrap().parse().unwrap();
    let cleanup = action(&mut driver, id, "cleanup");
    assert_eq!(cleanup.generation, 0);
    let before = stable(&mut driver);
    assert_eq!(before["plugins"][0]["state"], "Unloading");
    driver
        .complete(
            cleanup.clone(),
            false,
            Some("reserved inverse failed".into()),
        )
        .unwrap();
    let failed = stable(&mut driver);
    assert_eq!(failed["plugins"][0]["cleanupFailed"], true);
    let HostAction::Cleanup { ticket, .. } = driver.retry_cleanup(id).unwrap() else {
        panic!()
    };
    assert_eq!(ticket.action, cleanup.action + 1);
    stable(&mut driver);
    driver.complete(ticket, true, None).unwrap();
    assert_eq!(driver.drive().unwrap(), vec![HostAction::Removed { id }]);
    stable(&mut driver);
}
