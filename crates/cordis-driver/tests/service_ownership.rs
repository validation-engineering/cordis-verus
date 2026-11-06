use cordis_driver::{ActionTicket, Command, Driver, HostAction, ServicePort};

const PORT: ServicePort = ServicePort { key: 42, realm: 3 };
fn begin(driver: &mut Driver, owner: usize) -> ActionTicket {
    driver
        .drive()
        .unwrap()
        .into_iter()
        .find_map(|action| match action {
            HostAction::Setup { id, ticket } if id == owner => Some(ticket),
            _ => None,
        })
        .expect("setup action")
}

#[test]
fn metadata_and_object_replacement_share_ownership_and_error_precedence() {
    let mut driver = Driver::new().unwrap();
    let mut bridge = driver.host_bridge();
    let owner = driver.mount(None, vec![], vec![]).unwrap();
    let setup = begin(&mut driver, owner);
    let original = bridge.issue("original object").unwrap();
    let next = bridge.issue("replacement object").unwrap();
    let publication = driver
        .publish_host_object(&bridge, owner, 1, PORT, original, false)
        .unwrap();
    driver.complete(setup, true, None).unwrap();
    let foreign = driver.mount(None, vec![], vec![]).unwrap();
    let setup = begin(&mut driver, foreign);
    driver.complete(setup, true, None).unwrap();
    let other_driver = Driver::new().unwrap();
    let mut other_bridge = other_driver.host_bridge();
    let wrong_domain = other_bridge.issue("wrong domain").unwrap();
    let before = driver.snapshot();
    assert_eq!(
        driver.set(foreign, 1, publication, 999).unwrap_err().code,
        "StalePublication"
    );
    assert_eq!(
        driver
            .set_host_object(&bridge, foreign, 1, publication, wrong_domain)
            .unwrap_err()
            .code,
        "StalePublication"
    );
    assert_eq!(
        driver.revoke(foreign, 1, publication).unwrap_err().code,
        "StalePublication"
    );
    assert_eq!(
        driver
            .execute(Command::Reclaim {
                id: foreign,
                generation: 1,
                publication
            })
            .unwrap_err()
            .code,
        "StalePublication"
    );
    assert_eq!(driver.snapshot(), before);
    assert_eq!(
        driver
            .set_host_object(&bridge, owner, 1, publication, wrong_domain)
            .unwrap_err()
            .code,
        "HostBridge"
    );
    assert_eq!(driver.snapshot(), before);
    driver
        .set_host_object(&bridge, owner, 1, publication, next)
        .unwrap();
    let (_, _, actual) = driver
        .resolve_host_object(&bridge, PORT, None, None)
        .unwrap()
        .unwrap();
    assert_eq!(*actual, "replacement object");
    driver.retire(owner).unwrap();
    let before = driver.snapshot();
    assert_eq!(
        driver
            .set_host_object(&bridge, owner, 1, publication, wrong_domain)
            .unwrap_err()
            .code,
        "AdmissionClosed"
    );
    assert_eq!(driver.snapshot(), before);
    driver.revoke(owner, 1, publication).unwrap();
}
