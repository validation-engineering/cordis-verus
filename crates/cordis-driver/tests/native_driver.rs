use cordis_driver::{ActionKind, ActionTicket, Driver, HostAction, ServicePort};
use serde_json::{json, Value};

const PORT: ServicePort = ServicePort { key: 1, realm: 0 };
fn setup(driver: &mut Driver, id: usize) -> ActionTicket {
    driver
        .drive()
        .unwrap()
        .into_iter()
        .find_map(|action| match action {
            HostAction::Setup { id: owner, ticket } if owner == id => Some(ticket),
            _ => None,
        })
        .expect("setup action")
}
fn complete(driver: &mut Driver, ticket: ActionTicket) {
    driver.complete(ticket, true, None).unwrap();
}
fn active_provider(driver: &mut Driver, value: u64) -> (usize, u64, usize) {
    let id = driver.mount(None, vec![], vec![]).unwrap();
    let ticket = setup(driver, id);
    let generation = ticket.generation;
    let publication = driver.publish(id, generation, PORT, value).unwrap();
    complete(driver, ticket);
    (id, generation, publication)
}
fn only_cleanup(driver: &mut Driver, id: usize) -> ActionTicket {
    let actions = driver.drive().unwrap();
    assert_eq!(actions.len(), 1, "unexpected actions {actions:?}");
    match &actions[0] {
        HostAction::Cleanup { id: owner, ticket } => {
            assert_eq!(*owner, id);
            ticket.clone()
        }
        _ => panic!("expected cleanup"),
    }
}
fn command(driver: &mut Driver, value: Value) -> Value {
    serde_json::from_str(&driver.command(&value.to_string()).unwrap()).unwrap()
}

#[test]
fn outstanding_setup_survives_retirement_and_completes_once() {
    let mut driver = Driver::new().unwrap();
    let id = driver.mount(None, vec![], vec![]).unwrap();
    let ticket = setup(&mut driver, id);
    driver.retire(id).unwrap();
    assert!(driver.drive().unwrap().is_empty());
    assert_eq!(
        driver.validate(id, ticket.generation).unwrap_err().code,
        "AdmissionClosed"
    );
    complete(&mut driver, ticket.clone());
    assert_eq!(
        driver.complete(ticket, true, None).unwrap_err().code,
        "StaleAction"
    );
    let cleanup = only_cleanup(&mut driver, id);
    complete(&mut driver, cleanup);
    assert_eq!(driver.drive().unwrap(), vec![HostAction::Removed { id }]);
}

#[test]
fn cross_domain_and_forged_tickets_leave_real_action_outstanding() {
    let mut a = Driver::new().unwrap();
    let mut b = Driver::new().unwrap();
    let id = a.mount(None, vec![], vec![]).unwrap();
    let ticket = setup(&mut a, id);
    assert_eq!(
        b.complete(ticket.clone(), true, None).unwrap_err().code,
        "WrongDomain"
    );
    let mut forged = ticket.clone();
    forged.generation += 1;
    assert_eq!(
        a.complete(forged, true, None).unwrap_err().code,
        "StaleAction"
    );
    let mut forged = ticket.clone();
    forged.kind = ActionKind::Cleanup;
    assert_eq!(
        a.complete(forged, true, None).unwrap_err().code,
        "StaleAction"
    );
    complete(&mut a, ticket);
    assert_eq!(a.snapshot()["plugins"][0]["state"], "Active");
}

#[test]
fn provider_waits_for_consumer_cleanup_and_committed_lookup_survives_withdrawal() {
    let mut driver = Driver::new().unwrap();
    let (provider, _, publication) = active_provider(&mut driver, 42);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let ticket = setup(&mut driver, consumer);
    let generation = ticket.generation;
    complete(&mut driver, ticket);
    driver.retire(provider).unwrap();
    let cleanup = only_cleanup(&mut driver, consumer);
    assert!(driver.resolve(PORT, None, None).unwrap().is_none());
    let value = driver
        .resolve(PORT, Some(consumer), Some(generation))
        .unwrap()
        .unwrap();
    assert_eq!(value["publication"], publication.to_string());
    assert_eq!(value["value"], "42");
    complete(&mut driver, cleanup);
    let cleanup = only_cleanup(&mut driver, provider);
    complete(&mut driver, cleanup);
    assert_eq!(
        driver.drive().unwrap(),
        vec![HostAction::Removed { id: provider }]
    );
    assert_eq!(driver.snapshot()["plugins"][0]["state"], "Pending");
}

#[test]
fn set_preserves_publication_and_same_owner_republish_keeps_committed_old_slot() {
    let mut driver = Driver::new().unwrap();
    let (provider, generation, publication) = active_provider(&mut driver, 10);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let setup = setup(&mut driver, consumer);
    complete(&mut driver, setup);
    driver.set(provider, generation, publication, 11).unwrap();
    assert_eq!(
        driver.resolve(PORT, Some(consumer), None).unwrap().unwrap()["value"],
        "11"
    );
    assert!(driver.drive().unwrap().is_empty());
    driver.revoke(provider, generation, publication).unwrap();
    let replacement = driver.publish(provider, generation, PORT, 12).unwrap();
    assert_ne!(replacement, publication);
    assert!(driver.drive().unwrap().is_empty());
    assert_eq!(
        driver.resolve(PORT, None, None).unwrap().unwrap()["value"],
        "12"
    );
    assert_eq!(
        driver.resolve(PORT, Some(consumer), None).unwrap().unwrap()["value"],
        "11"
    );
    driver.revoke(provider, generation, publication).unwrap();
    assert_eq!(
        driver.resolve(PORT, None, None).unwrap().unwrap()["value"],
        "12"
    );
}

#[test]
fn cleanup_failure_retains_provider_dependency_until_explicit_retry_succeeds() {
    let mut driver = Driver::new().unwrap();
    let (provider, _, _) = active_provider(&mut driver, 9);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let setup = setup(&mut driver, consumer);
    complete(&mut driver, setup);
    driver.retire(provider).unwrap();
    let cleanup = only_cleanup(&mut driver, consumer);
    driver
        .complete(cleanup, false, Some("inverse failed".into()))
        .unwrap();
    assert!(driver.drive().unwrap().is_empty());
    assert_eq!(
        driver.resolve(PORT, Some(consumer), None).unwrap().unwrap()["value"],
        "9"
    );
    let HostAction::Cleanup { ticket, .. } = driver.retry_cleanup(consumer).unwrap() else {
        panic!()
    };
    complete(&mut driver, ticket);
    let cleanup = only_cleanup(&mut driver, provider);
    complete(&mut driver, cleanup);
}

#[test]
fn subtree_retirement_covers_pending_owned_children_without_inventing_dependencies() {
    let mut driver = Driver::new().unwrap();
    let parent = driver.mount(None, vec![], vec![]).unwrap();
    let setup = setup(&mut driver, parent);
    complete(&mut driver, setup);
    let child = driver.mount(Some(parent), vec![PORT], vec![]).unwrap();
    driver.retire(parent).unwrap();
    let actions = driver.drive().unwrap();
    assert!(actions.contains(&HostAction::Removed { id: child }));
    let cleanup = actions
        .into_iter()
        .find_map(|action| match action {
            HostAction::Cleanup { ticket, .. } => Some(ticket),
            _ => None,
        })
        .unwrap();
    complete(&mut driver, cleanup);
    assert_eq!(
        driver.drive().unwrap(),
        vec![HostAction::Removed { id: parent }]
    );
    assert!(driver.snapshot()["plugins"].as_array().unwrap().is_empty());
}

#[test]
fn generation_changes_and_stale_owned_mutations_are_rejected() {
    let mut driver = Driver::new().unwrap();
    let (provider, generation, publication) = active_provider(&mut driver, 7);
    driver.restart(provider).unwrap();
    let cleanup = only_cleanup(&mut driver, provider);
    complete(&mut driver, cleanup);
    let setup = setup(&mut driver, provider);
    assert!(setup.generation > generation);
    assert_eq!(
        driver
            .publish(provider, generation, PORT, 8)
            .unwrap_err()
            .code,
        "StaleEpisode"
    );
    assert_eq!(
        driver
            .revoke(provider, generation, publication)
            .unwrap_err()
            .code,
        "StalePublication"
    );
    driver.publish(provider, setup.generation, PORT, 9).unwrap();
    complete(&mut driver, setup);
}

#[test]
fn failed_setup_is_latched_and_partial_publications_are_cleaned() {
    let mut driver = Driver::new().unwrap();
    let id = driver.mount(None, vec![], vec![]).unwrap();
    let setup = setup(&mut driver, id);
    driver.publish(id, setup.generation, PORT, 99).unwrap();
    driver
        .complete(setup, false, Some("setup error".into()))
        .unwrap();
    assert!(driver.resolve(PORT, None, None).unwrap().is_none());
    let cleanup = only_cleanup(&mut driver, id);
    complete(&mut driver, cleanup);
    assert!(driver.drive().unwrap().is_empty());
    assert_eq!(driver.snapshot()["plugins"][0]["state"], "Failed");
}

#[test]
fn json_abi_roundtrip_keeps_large_identities_and_rejects_numbers() {
    let mut driver = Driver::new().unwrap();
    let mounted = command(&mut driver, json!({"op":"mount"}));
    let id = mounted["id"].clone();
    let actions = command(&mut driver, json!({"op":"drive"}));
    let ticket = actions["actions"][0]["ticket"].clone();
    let generation = ticket["generation"].clone();
    let publication = command(
        &mut driver,
        json!({"op":"publish","id":id,"generation":generation,"key":"18446744073709551615","realm":"9007199254740993","value":"18446744073709551615"}),
    );
    command(
        &mut driver,
        json!({"op":"complete","ticket":ticket,"success":true}),
    );
    let resolved = command(
        &mut driver,
        json!({"op":"resolve","key":"18446744073709551615","realm":"9007199254740993"}),
    );
    assert_eq!(resolved["value"], "18446744073709551615");
    assert_eq!(resolved["publication"], publication["publication"]);
    assert_eq!(
        driver
            .command(r#"{"op":"retire","id":0}"#)
            .unwrap_err()
            .code,
        "InvalidCommand"
    );
    assert_eq!(
        driver
            .command(r#"{"op":"mount","typo":true}"#)
            .unwrap_err()
            .code,
        "InvalidCommand"
    );
}

#[test]
fn missing_required_publication_prevents_activation() {
    let mut driver = Driver::new().unwrap();
    let provider = driver.mount(None, vec![], vec![PORT]).unwrap();
    let setup = setup(&mut driver, provider);
    complete(&mut driver, setup);
    assert_eq!(driver.snapshot()["plugins"][0]["state"], "Unloading");
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let cleanup = only_cleanup(&mut driver, provider);
    complete(&mut driver, cleanup);
    assert!(driver.drive().unwrap().is_empty());
    let consumer_id = consumer.to_string();
    assert!(driver.snapshot()["plugins"]
        .as_array()
        .unwrap()
        .iter()
        .any(|p| p["id"].as_str() == Some(consumer_id.as_str()) && p["state"] == "Pending"));
}

#[test]
fn in_flight_consumer_setup_blocks_provider_inverse_after_cancellation() {
    let mut driver = Driver::new().unwrap();
    let (provider, _, _) = active_provider(&mut driver, 123);
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    let pending = setup(&mut driver, consumer);
    driver.retire(provider).unwrap();
    assert!(driver.drive().unwrap().is_empty());
    assert_eq!(
        driver
            .resolve(PORT, Some(consumer), Some(pending.generation))
            .unwrap()
            .unwrap()["value"],
        "123"
    );
    complete(&mut driver, pending);
    let cleanup = only_cleanup(&mut driver, consumer);
    complete(&mut driver, cleanup);
    let cleanup = only_cleanup(&mut driver, provider);
    complete(&mut driver, cleanup);
}

#[test]
fn partially_initialized_publication_is_visible_only_to_its_owner() {
    let mut driver = Driver::new().unwrap();
    let provider = driver.mount(None, vec![], vec![]).unwrap();
    let pending = setup(&mut driver, provider);
    driver
        .publish(provider, pending.generation, PORT, 33)
        .unwrap();
    assert!(driver.resolve(PORT, None, None).unwrap().is_none());
    assert_eq!(
        driver
            .resolve(PORT, Some(provider), Some(pending.generation))
            .unwrap()
            .unwrap()["value"],
        "33"
    );
    let consumer = driver.mount(None, vec![PORT], vec![]).unwrap();
    assert!(driver.drive().unwrap().is_empty());
    complete(&mut driver, pending);
    let pending = setup(&mut driver, consumer);
    complete(&mut driver, pending);
}

#[test]
fn released_value_notifications_never_drop_handles_retained_by_other_slots() {
    let mut driver = Driver::new().unwrap();
    let (provider, generation, first) = active_provider(&mut driver, 42);
    let second = driver
        .publish(provider, generation, ServicePort { key: 2, realm: 0 }, 42)
        .unwrap();
    driver.set(provider, generation, first, 43).unwrap();
    assert_eq!(
        command(&mut driver, json!({"op": "drive"}))["released"],
        json!([])
    );
    driver.set(provider, generation, second, 43).unwrap();
    assert_eq!(
        command(&mut driver, json!({"op": "drive"}))["released"],
        json!(["42"])
    );
    driver.set(provider, generation, first, 44).unwrap();
    driver.set(provider, generation, first, 43).unwrap();
    assert_eq!(
        command(&mut driver, json!({"op": "drive"}))["released"],
        json!(["44"])
    );
}

#[test]
fn provider_cleanup_can_read_its_own_withdrawn_service_until_explicit_revoke() {
    let mut driver = Driver::new().unwrap();
    let (provider, generation, publication) = active_provider(&mut driver, 808);
    driver.retire(provider).unwrap();
    let cleanup = only_cleanup(&mut driver, provider);
    assert!(driver.resolve(PORT, None, None).unwrap().is_none());
    assert_eq!(
        driver
            .resolve(PORT, Some(provider), Some(generation))
            .unwrap()
            .unwrap()["value"],
        "808"
    );
    driver.revoke(provider, generation, publication).unwrap();
    assert!(driver
        .resolve(PORT, Some(provider), Some(generation))
        .unwrap()
        .is_none());
    complete(&mut driver, cleanup);
}
