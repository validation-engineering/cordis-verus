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

#[test]
fn admission_requires_loading_and_never_reopens_an_ended_iterator() {
    let mut driver = Driver::new();
    let id = driver.insert(None, vec![], vec![]).unwrap();
    let invalid = Err(DriverError::Kernel(Error::InvalidState));
    assert_eq!(driver.admit(id), invalid);
    assert_eq!(driver.admit(usize::MAX), invalid);

    driver.begin(id).unwrap();
    assert_eq!(driver.admit(id), Ok(true));
    driver.end(id).unwrap();
    // Coherent target alone does not reopen an iterator that already ended.
    assert_eq!(driver.admit(id), Ok(false));
    assert_eq!(driver.admit(id), Ok(false));
    driver.finish(id).unwrap();
    assert_eq!(driver.admit(id), invalid);
    driver.retire(id).unwrap();
    driver.depart(id).unwrap();
    assert_eq!(driver.admit(id), invalid);
    driver.unload(id).unwrap();
    driver.remove(id).unwrap();
    assert_eq!(driver.admit(id), invalid);
}

#[test]
fn target_drift_rejects_new_stages_but_lands_and_recovers_an_admitted_stage() {
    let mut driver = Driver::new();
    let port = Port { key: 71, realm: 1 };
    let provider = driver.insert(None, vec![], vec![port]).unwrap();
    driver.begin(provider).unwrap();
    finish(&mut driver, provider);
    let idle = driver.insert(None, vec![port], vec![]).unwrap();
    let pending = driver
        .insert_with_resources(None, vec![port], vec![], vec![12])
        .unwrap();
    driver.begin(idle).unwrap();
    driver.begin(pending).unwrap();
    assert_eq!(driver.admit(pending), Ok(true));

    driver.retire(provider).unwrap();
    driver.depart(provider).unwrap();
    assert_eq!(driver.admit(idle), Ok(false));
    assert_eq!(driver.admit(pending), Ok(true));
    assert_eq!(driver.depart(pending), Err(DriverError::Pending));
    driver.land_write(pending, 4, 0, 33).unwrap();
    assert_eq!(driver.read(pending, 0), Some(33));
    assert_eq!(driver.admit(pending), Ok(false));
    assert_eq!(
        driver.unload(provider),
        Err(DriverError::Kernel(Error::Relied))
    );

    driver.depart(idle).unwrap();
    driver.unload(idle).unwrap();
    driver.depart(pending).unwrap();
    driver.unload(pending).unwrap();
    assert_eq!(driver.read(pending, 0), Some(12));
    driver.unload(provider).unwrap();
}

#[test]
fn begin_and_admit_uses_real_dependency_readiness_without_touching_resources_on_failure() {
    let mut driver = Driver::new();
    let port = Port { key: 75, realm: 1 };
    let consumer = driver
        .insert_with_resources(None, vec![port], vec![], vec![17])
        .unwrap();
    assert_eq!(
        driver.begin_and_admit(consumer),
        Err(DriverError::Kernel(Error::MissingDependency))
    );
    assert_eq!(driver.phase(consumer), Some(Phase::Inactive));
    assert_eq!(driver.read(consumer, 0), Some(17));

    let provider = driver.insert(None, vec![], vec![port]).unwrap();
    driver.begin_and_admit(provider).unwrap();
    driver.end(provider).unwrap();
    driver.finish(provider).unwrap();
    driver.begin_and_admit(consumer).unwrap();
    assert_eq!(driver.phase(consumer), Some(Phase::Loading));
    assert_eq!(driver.read(consumer, 0), Some(17));
    driver.land_write(consumer, 5, 0, 23).unwrap();
    assert_eq!(driver.read(consumer, 0), Some(23));
    assert_eq!(
        driver.begin_and_admit(consumer),
        Err(DriverError::Kernel(Error::InvalidState))
    );
    assert_eq!(driver.read(consumer, 0), Some(23));
}
