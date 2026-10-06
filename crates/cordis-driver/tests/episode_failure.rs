use cordis_driver::{ActionTicket, Driver, HostAction, ServicePort};

fn setup(driver: &mut Driver, id: usize) -> ActionTicket {
    match driver.drive().unwrap().as_slice() {
        [HostAction::Setup { id: owner, ticket }] if *owner == id => ticket.clone(),
        actions => panic!("expected one setup: {actions:?}"),
    }
}
fn cleanup(driver: &mut Driver, id: usize) -> ActionTicket {
    match driver.drive().unwrap().as_slice() {
        [HostAction::Cleanup { id: owner, ticket }] if *owner == id => ticket.clone(),
        actions => panic!("expected one cleanup: {actions:?}"),
    }
}

#[test]
fn host_failure_withdraws_but_keeps_the_actual_setup_ticket_until_landing() {
    let mut driver = Driver::new().unwrap();
    let id = driver.mount(None, vec![], vec![]).unwrap();
    let pending = setup(&mut driver, id);
    driver
        .fail_episode(id, pending.generation, "child rejected".into())
        .unwrap();
    assert_eq!(
        driver.validate(id, pending.generation).unwrap_err().code,
        "AdmissionClosed"
    );
    assert!(driver.drive().unwrap().is_empty());
    assert_eq!(
        driver.snapshot()["plugins"][0]["pendingAction"]["kind"],
        "setup"
    );
    driver.complete(pending.clone(), true, None).unwrap();
    assert_eq!(
        driver.complete(pending, true, None).unwrap_err().code,
        "StaleAction"
    );
    let inverse = cleanup(&mut driver, id);
    driver.complete(inverse, true, None).unwrap();
    assert!(driver.drive().unwrap().is_empty());
    assert_eq!(driver.snapshot()["plugins"][0]["state"], "Failed");
    assert_eq!(driver.snapshot()["plugins"][0]["error"], "child rejected");
    assert_eq!(driver.snapshot()["plugins"][0]["retired"], false);
}

#[test]
fn a_host_failure_retains_committed_consumers_and_failed_cleanup_dependencies() {
    let mut driver = Driver::new().unwrap();
    let port = ServicePort { key: 3, realm: 8 };
    let provider = driver.mount(None, vec![], vec![]).unwrap();
    let pending = setup(&mut driver, provider);
    let generation = pending.generation;
    let publication = driver.publish(provider, generation, port, 73).unwrap();
    driver.complete(pending, true, None).unwrap();
    let consumer = driver.mount(None, vec![port], vec![]).unwrap();
    let pending = setup(&mut driver, consumer);
    let consumer_generation = pending.generation;
    driver.complete(pending, true, None).unwrap();
    driver
        .fail_episode(provider, generation, "child rejected".into())
        .unwrap();
    let inverse = cleanup(&mut driver, consumer);
    driver
        .complete(inverse, false, Some("consumer cleanup failed".into()))
        .unwrap();
    assert!(driver.drive().unwrap().is_empty());
    let retained = driver
        .resolve(port, Some(consumer), Some(consumer_generation))
        .unwrap()
        .unwrap();
    assert_eq!(retained["publication"], publication.to_string());
    assert_eq!(retained["value"], "73");
    let HostAction::Cleanup { ticket, .. } = driver.retry_cleanup(consumer).unwrap() else {
        panic!("cleanup")
    };
    driver.complete(ticket, true, None).unwrap();
    let inverse = cleanup(&mut driver, provider);
    driver.complete(inverse, true, None).unwrap();
    assert!(driver.drive().unwrap().is_empty());
    let nodes = driver.snapshot();
    assert_eq!(nodes["plugins"][0]["state"], "Failed");
    // A successful inverse retry releases leases but does not erase the
    // consumer's latched failure or implicitly restart it.
    assert_eq!(nodes["plugins"][1]["state"], "Failed");
    assert_eq!(nodes["plugins"][1]["cleanupFailed"], false);
    assert_eq!(nodes["storage"]["liveBindings"], 0);
}

#[test]
fn stale_reserved_and_completed_failure_reports_do_not_poison_a_new_generation() {
    let mut driver = Driver::new().unwrap();
    let id = driver.mount(None, vec![], vec![]).unwrap();
    driver.prepare(id).unwrap();
    assert_eq!(
        driver
            .fail_episode(id, 0, "reserved".into())
            .unwrap_err()
            .code,
        "AdmissionClosed"
    );
    let pending = setup(&mut driver, id);
    let generation = pending.generation;
    driver.complete(pending, true, None).unwrap();
    driver.fail_episode(id, generation, "first".into()).unwrap();
    assert_eq!(
        driver
            .fail_episode(id, generation, "late".into())
            .unwrap_err()
            .code,
        "AdmissionClosed"
    );
    let inverse = cleanup(&mut driver, id);
    driver.complete(inverse, true, None).unwrap();
    driver.restart(id).unwrap();
    let next = setup(&mut driver, id);
    assert!(next.generation > generation);
    let before = driver.snapshot();
    assert_eq!(
        driver
            .fail_episode(id, generation, "old generation".into())
            .unwrap_err()
            .code,
        "StaleEpisode"
    );
    assert_eq!(driver.snapshot(), before);
    driver.complete(next, true, None).unwrap();
    assert_eq!(driver.snapshot()["plugins"][0]["state"], "Active");
}
