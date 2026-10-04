use cordis_kernel::driver::{Driver, DriverError};
use cordis_kernel::witnessed::EpisodeError;
use cordis_kernel::{Error, Phase, Port};

fn finish(driver: &mut Driver, id: usize) {
    assert!(driver.admit(id).unwrap());
    driver.end(id).unwrap();
    driver.finish(id).unwrap();
}

#[test]
fn owned_driver_applies_real_inverse_before_becoming_inactive() {
    let mut driver = Driver::default();
    let id = driver
        .insert_with_resources(None, vec![], vec![], vec![10, 20])
        .unwrap();
    driver.begin(id).unwrap();
    assert!(driver.admit(id).unwrap());
    driver.land_write(id, 1, 0, 30).unwrap();
    assert!(driver.admit(id).unwrap());
    driver.land_write(id, 1, 1, 40).unwrap();
    finish(&mut driver, id);
    assert_eq!(driver.read(id, 0), Some(30));
    assert_eq!(driver.read(id, 1), Some(40));
    driver.retire(id).unwrap();
    driver.depart(id).unwrap();
    assert_eq!(driver.phase(id), Some(Phase::Unloading));
    driver.unload(id).unwrap();
    assert_eq!(driver.phase(id), Some(Phase::Inactive));
    assert_eq!(driver.read(id, 0), Some(10));
    assert_eq!(driver.read(id, 1), Some(20));
    driver.remove(id).unwrap();
    assert_eq!(driver.phase(id), None);
    assert_eq!(driver.read(id, 0), None);
}

#[test]
fn retirement_does_not_discard_a_pending_resource_inverse() {
    let mut driver = Driver::new();
    let id = driver
        .insert_with_resources(None, vec![], vec![], vec![7])
        .unwrap();
    driver.begin(id).unwrap();
    assert!(driver.admit(id).unwrap());
    driver.retire(id).unwrap();
    assert_eq!(driver.depart(id), Err(DriverError::Pending));
    assert_eq!(driver.unload(id), Err(DriverError::Pending));
    assert_eq!(driver.phase(id), Some(Phase::Loading));
    driver.land_write(id, 8, 0, 11).unwrap();
    assert_eq!(driver.read(id, 0), Some(11));
    assert_eq!(driver.finish(id), Err(DriverError::Pending));
    driver.depart(id).unwrap();
    driver.unload(id).unwrap();
    assert_eq!(driver.read(id, 0), Some(7));
}

#[test]
fn provider_resources_remain_live_until_consumer_recovery() {
    let mut driver = Driver::new();
    let port = Port { key: 1, realm: 2 };
    let provider = driver
        .insert_with_resources(None, vec![], vec![port], vec![0])
        .unwrap();
    driver.begin(provider).unwrap();
    assert!(driver.admit(provider).unwrap());
    driver.land_write(provider, 0, 0, 99).unwrap();
    finish(&mut driver, provider);
    let consumer = driver
        .insert_with_resources(None, vec![port], vec![], vec![1])
        .unwrap();
    driver.begin(consumer).unwrap();
    assert!(driver.admit(consumer).unwrap());
    driver.land_write(consumer, 1, 0, 100).unwrap();
    finish(&mut driver, consumer);
    driver.retire(provider).unwrap();
    driver.depart(provider).unwrap();
    assert_eq!(
        driver.unload(provider),
        Err(DriverError::Kernel(Error::Relied))
    );
    assert_eq!(driver.read(provider, 0), Some(99));
    assert_eq!(driver.read(consumer, 0), Some(100));
    driver.depart(consumer).unwrap();
    driver.unload(consumer).unwrap();
    assert_eq!(driver.read(consumer, 0), Some(1));
    driver.unload(provider).unwrap();
    assert_eq!(driver.read(provider, 0), Some(0));
}

#[test]
fn invalid_calls_preserve_owned_effect_state_and_allow_retry() {
    let mut driver = Driver::new();
    let id = driver
        .insert_with_resources(None, vec![], vec![], vec![4])
        .unwrap();
    driver.begin(id).unwrap();
    assert_eq!(
        driver.land_write(id, 1, 0, 8),
        Err(DriverError::Effect(EpisodeError::NotAdmitted))
    );
    assert_eq!(driver.read(id, 0), Some(4));
    assert!(driver.admit(id).unwrap());
    driver.land_write(id, 1, 0, 8).unwrap();
    finish(&mut driver, id);
    assert_eq!(driver.depart(id), Err(DriverError::Kernel(Error::Changed)));
    assert_eq!(driver.read(id, 0), Some(8));
    assert_eq!(
        driver.unload(id),
        Err(DriverError::Kernel(Error::InvalidState))
    );
    assert_eq!(driver.read(id, 0), Some(8));
    assert_eq!(driver.phase(usize::MAX), None);
    assert_eq!(driver.read(usize::MAX, 0), None);
    assert_eq!(
        driver.begin(usize::MAX),
        Err(DriverError::Kernel(Error::Unknown))
    );
}

#[test]
fn repeated_activation_keeps_the_same_cells_and_commits_the_new_provider() {
    let mut driver = Driver::new();
    let port = Port { key: 70, realm: 1 };
    let provider = driver.insert(None, vec![], vec![port]).unwrap();
    driver.begin(provider).unwrap();
    finish(&mut driver, provider);
    let consumer = driver
        .insert_with_resources(None, vec![port], vec![], vec![12])
        .unwrap();
    driver.begin(consumer).unwrap();
    assert_eq!(driver.read(consumer, 0), Some(12));
    assert!(driver.admit(consumer).unwrap());
    driver.land_write(consumer, 3, 0, 99).unwrap();
    finish(&mut driver, consumer);
    driver.retire(provider).unwrap();
    driver.depart(provider).unwrap();
    driver.depart(consumer).unwrap();
    driver.unload(consumer).unwrap();
    assert_eq!(driver.read(consumer, 0), Some(12));
    driver.unload(provider).unwrap();
    driver.remove(provider).unwrap();

    let replacement = driver.insert(None, vec![], vec![port]).unwrap();
    assert_ne!(replacement, provider);
    driver.begin(replacement).unwrap();
    finish(&mut driver, replacement);
    driver.begin(consumer).unwrap();
    assert_eq!(driver.read(consumer, 0), Some(12));
    assert!(driver.admit(consumer).unwrap());
    driver.land_write(consumer, 4, 0, 33).unwrap();
    finish(&mut driver, consumer);
    driver.retire(replacement).unwrap();
    driver.depart(replacement).unwrap();
    driver.depart(consumer).unwrap();
    driver.unload(consumer).unwrap();
    assert_eq!(driver.read(consumer, 0), Some(12));
    driver.unload(replacement).unwrap();
}
