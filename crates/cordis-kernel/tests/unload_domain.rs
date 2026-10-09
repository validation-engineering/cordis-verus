use cordis_kernel::mixed_driver as mixed;
use cordis_kernel::mixed_driver::fresh;
use cordis_kernel::{Error, Phase, Port};

const SERVICE: Port = Port { key: 7, realm: 3 };
const OTHER_REALM: Port = Port { key: 7, realm: 4 };
const OWN: Port = Port { key: 8, realm: 3 };

#[derive(Debug, PartialEq, Eq)]
struct ActorSnapshot {
    phase: Option<Phase>,
    retired: bool,
    inverses: Option<usize>,
    values: Vec<Option<u64>>,
}

fn fresh_snapshot(driver: &fresh::FreshDriver) -> Vec<ActorSnapshot> {
    (0..6)
        .map(|actor| ActorSnapshot {
            phase: driver.phase(actor),
            retired: driver.retired(actor),
            inverses: driver.inverse_count(actor),
            values: [SERVICE, OTHER_REALM, OWN]
                .map(|key| driver.read(actor, key))
                .to_vec(),
        })
        .collect()
}

fn mixed_snapshot(driver: &mixed::MixedDriver) -> Vec<ActorSnapshot> {
    (0..6)
        .map(|actor| ActorSnapshot {
            phase: driver.phase(actor),
            retired: driver.retired(actor),
            inverses: driver.inverse_count(actor),
            values: [SERVICE, OTHER_REALM, OWN]
                .map(|key| driver.read(actor, key))
                .to_vec(),
        })
        .collect()
}

fn fresh_provider(port: Port, value: u64) -> fresh::Blueprint {
    fresh::Blueprint::new(
        vec![],
        vec![port],
        vec![fresh::Instruction::Provide {
            key: port,
            value,
            next: None,
        }],
    )
}

#[test]
fn fresh_unload_uses_captured_realm_and_restores_all_inverse_kinds_in_reverse() {
    use fresh::Instruction::*;
    let parent = fresh::Blueprint::new(
        vec![SERVICE],
        vec![OWN],
        vec![
            Provide {
                key: OWN,
                value: 13,
                next: Some(1),
            },
            Xor {
                key: OWN,
                mask: 6,
                next: Some(2),
            },
            Xor {
                key: SERVICE,
                mask: 5,
                next: Some(3),
            },
            Child {
                blueprint: 0,
                next: Some(4),
            },
        ],
    );
    let mut driver = fresh::FreshDriver::new(vec![
        fresh::Blueprint::new(vec![], vec![], vec![]),
        fresh_provider(SERVICE, 11),
        fresh_provider(OTHER_REALM, 97),
        parent,
    ]);
    let service = driver.insert(None, 1).unwrap();
    driver.begin(service).unwrap();
    assert_eq!(driver.step(service), Ok(fresh::Outcome::Finished));
    let other = driver.insert(None, 2).unwrap();
    driver.begin(other).unwrap();
    driver.step(other).unwrap();
    let actor = driver.insert(None, 3).unwrap();
    driver.begin(actor).unwrap();
    let run = driver.run_until_blocked(actor);
    assert_eq!(run.steps, 5);
    assert_eq!(run.error, None);
    assert_eq!(driver.read(actor, OWN), Some(13 ^ 6));
    assert_eq!(driver.read(service, SERVICE), Some(11 ^ 5));
    let child = 3;
    driver.begin(child).unwrap();
    driver.step(child).unwrap();
    driver.retire(child).unwrap();
    assert_eq!(driver.remove(child), Err(fresh::DriverError::Retained));

    driver.retire(service).unwrap();
    driver.depart(service).unwrap();
    let before = fresh_snapshot(&driver);
    assert_eq!(
        driver.unload(service),
        Err(fresh::DriverError::Kernel(Error::Relied))
    );
    assert_eq!(fresh_snapshot(&driver), before);
    driver.depart(actor).unwrap();
    driver.unload(actor).unwrap();
    assert_eq!(driver.phase(actor), Some(Phase::Inactive));
    assert_eq!(driver.inverse_count(actor), Some(0));
    assert_eq!(driver.read(actor, OWN), None);
    assert_eq!(driver.read(service, SERVICE), Some(11));
    assert_eq!(driver.read(other, OTHER_REALM), Some(97));
    assert_eq!(driver.inverse_count(other), Some(1));
    assert!(driver.retired(child));
    assert_eq!(driver.phase(child), Some(Phase::Active));
    assert_eq!(driver.inverse_count(child), Some(1));

    // The child inverse retires the captured child; its own Unit journal is
    // recovered separately, and the previously relied-on provider can retry.
    driver.depart(child).unwrap();
    driver.unload(child).unwrap();
    driver.remove(child).unwrap();
    driver.unload(service).unwrap();
    assert_eq!(driver.read(service, SERVICE), None);
    assert_eq!(driver.phase(other), Some(Phase::Active));
    assert_eq!(driver.read(other, OTHER_REALM), Some(97));
}

#[test]
fn mixed_unload_waits_for_its_own_consumer_and_then_restores_the_full_journal() {
    use mixed::Instruction::*;
    let provider = mixed::Blueprint::new(
        vec![],
        vec![SERVICE],
        vec![Provide {
            key: SERVICE,
            value: 7,
            next: None,
        }],
    );
    let parent = mixed::Blueprint::new(
        vec![SERVICE],
        vec![OWN],
        vec![
            Provide {
                key: OWN,
                value: 13,
                next: Some(1),
            },
            Xor {
                key: OWN,
                mask: 6,
                next: Some(2),
            },
            Xor {
                key: SERVICE,
                mask: 5,
                next: Some(3),
            },
            Child {
                expected: 2,
                blueprint: 0,
                next: Some(4),
            },
        ],
    );
    let consumer = mixed::Blueprint::new(
        vec![OWN],
        vec![],
        vec![Xor {
            key: OWN,
            mask: 3,
            next: None,
        }],
    );
    let mut driver = mixed::MixedDriver::new(vec![
        mixed::Blueprint::new(vec![], vec![], vec![]),
        provider,
        parent,
        consumer,
    ]);
    let service = driver.insert(None, 1).unwrap();
    driver.begin(service).unwrap();
    driver.step(service).unwrap();
    let actor = driver.insert(None, 2).unwrap();
    driver.begin(actor).unwrap();
    for _ in 0..5 {
        driver.step(actor).unwrap();
    }
    let consumer = driver.insert(None, 3).unwrap();
    assert_eq!(consumer, 3);
    driver.begin(consumer).unwrap();
    driver.step(consumer).unwrap();
    assert_eq!(driver.read(actor, OWN), Some(13 ^ 6 ^ 3));
    driver.retire(actor).unwrap();
    driver.depart(actor).unwrap();

    let before = mixed_snapshot(&driver);
    assert_eq!(
        driver.unload(actor),
        Err(mixed::DriverError::Kernel(Error::Relied))
    );
    assert_eq!(mixed_snapshot(&driver), before);
    assert!(!driver.retired(2));
    driver.depart(consumer).unwrap();
    driver.unload(consumer).unwrap();
    assert_eq!(driver.read(actor, OWN), Some(13 ^ 6));
    assert_eq!(driver.read(service, SERVICE), Some(7 ^ 5));
    driver.unload(actor).unwrap();
    assert_eq!(driver.read(actor, OWN), None);
    assert_eq!(driver.read(service, SERVICE), Some(7));
    assert_eq!(driver.phase(service), Some(Phase::Active));
    assert_eq!(driver.inverse_count(service), Some(1));
    assert_eq!(driver.phase(actor), Some(Phase::Inactive));
    assert_eq!(driver.inverse_count(actor), Some(0));
    assert!(driver.retired(2));
    assert_eq!(driver.phase(2), Some(Phase::Inactive));
    driver.remove(2).unwrap();
    assert_eq!(driver.inverse_count(consumer), Some(0));
}
