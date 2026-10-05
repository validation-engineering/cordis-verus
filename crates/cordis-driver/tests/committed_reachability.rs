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
