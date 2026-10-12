use cordis_driver::{ActionTicket, Driver, HostAction, ServicePort};
use serde_json::json;
fn port(key: u64, realm: u64) -> ServicePort {
    ServicePort { key, realm }
}
fn setup(driver: &mut Driver, id: usize) -> ActionTicket {
    let actions = driver.drive().unwrap();
    assert_eq!(actions.len(), 1);
    match actions.into_iter().next().unwrap() {
        HostAction::Setup { id: actual, ticket } if actual == id => ticket,
        _ => panic!("expected setup"),
    }
}
fn provider(driver: &mut Driver, port: ServicePort, value: u64) -> (usize, usize) {
    let id = driver.mount(None, vec![], vec![]).unwrap();
    let ticket = setup(driver, id);
    let publication = driver.publish(id, ticket.generation, port, value).unwrap();
    driver.complete(ticket, true, None).unwrap();
    (id, publication)
}
#[test]
fn authority_follows_committed_edges_including_transitive_cleanup_not_new_targets() {
    let mut driver = Driver::new().unwrap();
    let (old, old_publication) = provider(&mut driver, port(1, 0), 10);
    let (isolated, _) = provider(&mut driver, port(1, 1), 11);
    let middle = driver.mount(None, vec![port(1, 0)], vec![]).unwrap();
    assert!(!driver.committed_reaches(middle, 0, old).unwrap());
    let ticket = setup(&mut driver, middle);
    driver
        .publish(middle, ticket.generation, port(2, 0), 20)
        .unwrap();
    driver.complete(ticket, true, None).unwrap();
    let leaf = driver.mount(None, vec![port(2, 0)], vec![]).unwrap();
    let ticket = setup(&mut driver, leaf);
    driver.complete(ticket, true, None).unwrap();
    assert!(driver.committed_reaches(leaf, 1, leaf).unwrap());
    assert!(driver.committed_reaches(leaf, 1, middle).unwrap());
    assert!(driver.committed_reaches(leaf, 1, old).unwrap());
    assert!(!driver.committed_reaches(leaf, 1, isolated).unwrap());
    driver.revoke(old, 1, old_publication).unwrap();
    let actions = driver.drive().unwrap();
    let cleanup = match &actions[0] {
        HostAction::Cleanup { id, ticket } if *id == leaf => ticket.clone(),
        _ => panic!("leaf must restore first"),
    };
    assert!(driver.committed_reaches(leaf, 1, old).unwrap());
    let (replacement, _) = provider(&mut driver, port(1, 0), 30);
    assert!(driver.committed_reaches(leaf, 1, old).unwrap());
    assert_eq!(driver.check_wait(leaf, 1, old, true).unwrap(), Some(old));
    assert_eq!(driver.check_wait(leaf, 1, replacement, true).unwrap(), None);
    assert!(!driver.committed_reaches(leaf, 1, replacement).unwrap());
    assert_eq!(
        driver.committed_reaches(leaf, 2, old).unwrap_err().code,
        "StaleEpisode"
    );
    let reply=driver.command(&json!({"op":"committed_reaches","from":leaf.to_string(),"generation":"1","target":old.to_string()}).to_string()).unwrap();
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&reply).unwrap(),
        json!({"reachable":true})
    );
    driver.complete(cleanup, true, None).unwrap();
    assert!(!driver.committed_reaches(leaf, 1, old).unwrap());
    assert!(driver.committed_reaches(middle, 1, old).unwrap());
    let actions = driver.drive().unwrap();
    let cleanup = match &actions[0] {
        HostAction::Cleanup { id, ticket } if *id == middle => ticket.clone(),
        _ => panic!("middle must restore next"),
    };
    driver.complete(cleanup, true, None).unwrap();
    let ticket = setup(&mut driver, middle);
    assert_eq!(ticket.generation, 2);
    assert!(driver.committed_reaches(middle, 2, replacement).unwrap());
    assert!(!driver.committed_reaches(middle, 2, old).unwrap());
    assert_eq!(
        driver.committed_reaches(middle, 1, old).unwrap_err().code,
        "StaleEpisode"
    );
}
#[test]
fn ownership_and_unknown_nodes_never_create_service_authority() {
    let mut driver = Driver::new().unwrap();
    let parent = driver.mount(None, vec![], vec![]).unwrap();
    let ticket = setup(&mut driver, parent);
    driver.complete(ticket, true, None).unwrap();
    let child = driver.mount(Some(parent), vec![], vec![]).unwrap();
    let ticket = setup(&mut driver, child);
    driver.complete(ticket, true, None).unwrap();
    assert!(!driver.committed_reaches(parent, 1, child).unwrap());
    assert!(!driver.committed_reaches(child, 1, parent).unwrap());
    assert!(!driver.committed_reaches(child, 1, usize::MAX).unwrap());
    assert_eq!(
        driver
            .committed_reaches(usize::MAX, 0, parent)
            .unwrap_err()
            .code,
        "StaleEpisode"
    );
    driver.retire(child).unwrap();
    let actions = driver.drive().unwrap();
    let ticket = match &actions[0] {
        HostAction::Cleanup { ticket, .. } => ticket.clone(),
        _ => panic!("cleanup"),
    };
    driver.complete(ticket, true, None).unwrap();
    driver.drive().unwrap();
    assert_eq!(
        driver.committed_reaches(child, 1, child).unwrap_err().code,
        "StaleEpisode"
    );
}

#[test]
fn wait_admission_checks_subtree_identity_live_scope_and_exact_episode() {
    let mut driver = Driver::new().unwrap();
    let owner = driver.mount(None, vec![], vec![]).unwrap();
    let ticket = setup(&mut driver, owner);
    driver.complete(ticket, true, None).unwrap();
    let provider = driver.mount(Some(owner), vec![], vec![]).unwrap();
    let ticket = setup(&mut driver, provider);
    driver
        .publish(provider, ticket.generation, port(7, 0), 70)
        .unwrap();
    driver.complete(ticket, true, None).unwrap();
    let middle = driver.mount(None, vec![port(7, 0)], vec![]).unwrap();
    let ticket = setup(&mut driver, middle);
    driver
        .publish(middle, ticket.generation, port(8, 0), 80)
        .unwrap();
    driver.complete(ticket, true, None).unwrap();
    let leaf = driver.mount(None, vec![port(8, 0)], vec![]).unwrap();
    let ticket = setup(&mut driver, leaf);
    driver.complete(ticket, true, None).unwrap();

    assert_eq!(driver.check_wait(leaf, 1, leaf, true).unwrap(), Some(leaf));
    assert_eq!(
        driver.check_wait(leaf, 1, owner, true).unwrap(),
        Some(provider)
    );
    assert_eq!(
        driver.check_wait(provider, 1, owner, true).unwrap(),
        Some(provider)
    );
    assert_eq!(driver.check_wait(owner, 1, provider, true).unwrap(), None);
    assert_eq!(driver.check_wait(leaf, 1, owner, false).unwrap(), None);
    assert_eq!(driver.check_wait(leaf, 1, usize::MAX, true).unwrap(), None);
    assert_eq!(
        driver.check_wait(leaf, 0, owner, false).unwrap_err().code,
        "StaleEpisode"
    );
    assert_eq!(
        driver
            .check_wait(usize::MAX, 0, owner, true)
            .unwrap_err()
            .code,
        "StaleEpisode"
    );
    let reply = driver
        .command(
            &json!({"op":"check_wait","from":leaf.to_string(),"generation":"1",
        "target":owner.to_string(),"holding":true})
            .to_string(),
        )
        .unwrap();
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&reply).unwrap(),
        json!({"blocked":true,"retained":provider.to_string()})
    );
    // Observation does not withdraw providers or consume the caller's episode.
    assert!(driver.committed_reaches(leaf, 1, provider).unwrap());
}

#[test]
fn pending_request_contract_uses_committed_providers_and_exact_receipts() {
    use cordis_driver::{request_ledger::RequestLedger, RequestTicket};
    let mut driver = Driver::new().unwrap();
    let (source, _) = provider(&mut driver, port(11, 0), 10);
    let leaf = driver.mount(None, vec![port(11, 0)], vec![]).unwrap();
    let setup = setup(&mut driver, leaf);
    driver.complete(setup, true, None).unwrap();
    let mut requests = RequestLedger::new(driver.domain());
    let a = requests.issue(leaf, 1, 100, 200, false).unwrap();
    let b = requests.issue(leaf, 1, 100, 200, true).unwrap();
    let c = requests.issue(leaf, 1, 101, 200, false).unwrap();
    assert!(!requests.job_drained(100, 200));
    assert!(!requests.job_drained(101, 200));
    assert!(requests.job_drained(100, 201));
    assert_eq!(
        driver
            .check_request_wait(&requests, a.into(), source)
            .unwrap(),
        Some(source)
    );
    let wrong = RequestTicket {
        generation: 2,
        ..a.into()
    };
    assert_eq!(
        driver
            .check_request_wait(&requests, wrong, source)
            .unwrap_err()
            .code,
        "InvalidAuthority"
    );
    assert!(requests.complete(wrong.into()).is_err());
    requests.complete(a).unwrap();
    assert!(!requests.job_drained(100, 200));
    assert_eq!(
        driver
            .check_request_wait(&requests, a.into(), source)
            .unwrap_err()
            .code,
        "StaleAuthority"
    );
    requests.complete(b).unwrap();
    assert!(requests.job_drained(100, 200));
    assert!(!requests.job_drained(101, 200));
    requests.complete(c).unwrap();
    // IDs are never reused, even when all payloads have been reclaimed.
    let d = requests.issue(leaf, 1, 100, 200, false).unwrap();
    assert!(d.request > c.request);
    assert!(requests.complete(a).is_err());
    assert!(requests.validate(d).is_ok());
    let stale = requests.issue(leaf, 0, 100, 201, false).unwrap();
    assert_eq!(
        driver
            .check_request_wait(&requests, stale.into(), source)
            .unwrap_err()
            .code,
        "StaleEpisode"
    );
}

#[test]
fn request_ticket_json_preserves_large_identities_and_rejects_lossy_numbers() {
    use cordis_driver::RequestTicket;
    let ticket = RequestTicket {
        domain: u64::MAX,
        id: usize::MAX,
        generation: u64::MAX,
        session: u64::MAX,
        job: u64::MAX,
        request: u64::MAX,
        restoring: true,
    };
    let value = serde_json::to_value(ticket).unwrap();
    assert_eq!(
        serde_json::from_value::<RequestTicket>(value.clone()).unwrap(),
        ticket
    );
    for field in ["domain", "id", "generation", "session", "job", "request"] {
        let mut bad = value.clone();
        bad[field] = json!(1);
        assert!(serde_json::from_value::<RequestTicket>(bad).is_err());
    }
}
