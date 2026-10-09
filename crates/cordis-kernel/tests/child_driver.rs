use cordis_kernel::child_driver::{ChildDriver, ChildDriverError};
use cordis_kernel::ownership::ChildError;
use cordis_kernel::{Error, Phase, Port};

fn finish(driver: &mut ChildDriver, id: usize) {
    assert!(driver.admit(id).unwrap());
    driver.end(id).unwrap();
    driver.finish(id).unwrap();
}

fn install(driver: &mut ChildDriver, id: usize) {
    driver.begin(id).unwrap();
    finish(driver, id);
}

#[test]
fn retired_inactive_child_is_retained_until_real_inverse_is_consumed() {
    let mut driver = ChildDriver::default();
    let parent = driver.insert(None, vec![], vec![]).unwrap();
    driver.begin(parent).unwrap();
    assert!(driver.admit(parent).unwrap());
    let child = driver.land_child(parent, vec![], vec![]).unwrap();
    driver.retire(child).unwrap();
    assert_eq!(driver.phase(child), Some(Phase::Inactive));
    assert_eq!(driver.remove(child), Err(ChildDriverError::Retained));
    assert_eq!(driver.inverse_count(parent), Some(1));
    finish(&mut driver, parent);
    driver.retire(parent).unwrap();
    driver.depart(parent).unwrap();
    driver.unload(parent).unwrap();
    assert_eq!(driver.inverse_count(parent), Some(0));
    driver.remove(child).unwrap();
    driver.remove(parent).unwrap();
    assert_eq!(driver.phase(child), None);
}

#[test]
fn parent_unload_retires_active_child_without_waiting_for_ownership_tree() {
    let mut driver = ChildDriver::new();
    let parent = driver.insert(None, vec![], vec![]).unwrap();
    driver.begin(parent).unwrap();
    assert!(driver.admit(parent).unwrap());
    let child = driver.land_child(parent, vec![], vec![]).unwrap();
    install(&mut driver, child);
    finish(&mut driver, parent);
    driver.retire(parent).unwrap();
    driver.depart(parent).unwrap();
    driver.unload(parent).unwrap();
    assert_eq!(driver.phase(parent), Some(Phase::Inactive));
    assert_eq!(driver.phase(child), Some(Phase::Active));
    assert!(driver.retired(child));
    assert_eq!(
        driver.remove(parent),
        Err(ChildDriverError::Kernel(Error::Children))
    );
    driver.depart(child).unwrap();
    driver.unload(child).unwrap();
    driver.remove(child).unwrap();
    driver.remove(parent).unwrap();
}

#[test]
fn all_actual_journals_retain_their_children_through_nested_recovery() {
    let mut driver = ChildDriver::new();
    let parent = driver.insert(None, vec![], vec![]).unwrap();
    driver.begin(parent).unwrap();
    assert!(driver.admit(parent).unwrap());
    let child = driver.land_child(parent, vec![], vec![]).unwrap();
    driver.begin(child).unwrap();
    assert!(driver.admit(child).unwrap());
    let grandchild = driver.land_child(child, vec![], vec![]).unwrap();
    finish(&mut driver, child);
    finish(&mut driver, parent);
    driver.retire(grandchild).unwrap();
    assert_eq!(driver.remove(grandchild), Err(ChildDriverError::Retained));
    driver.retire(parent).unwrap();
    driver.depart(parent).unwrap();
    driver.unload(parent).unwrap();
    assert_eq!(driver.inverse_count(parent), Some(0));
    assert_eq!(driver.inverse_count(child), Some(1));
    assert_eq!(driver.remove(grandchild), Err(ChildDriverError::Retained));
    driver.depart(child).unwrap();
    driver.unload(child).unwrap();
    driver.remove(grandchild).unwrap();
    driver.remove(child).unwrap();
    driver.remove(parent).unwrap();
}

#[test]
fn actual_service_dependency_blocks_parent_inverse_before_child_retirement() {
    let mut driver = ChildDriver::new();
    let port = Port { key: 10, realm: 3 };
    let parent = driver.insert(None, vec![], vec![port]).unwrap();
    driver.begin(parent).unwrap();
    assert!(driver.admit(parent).unwrap());
    let child = driver.land_child(parent, vec![port], vec![]).unwrap();
    finish(&mut driver, parent);
    install(&mut driver, child);
    driver.retire(parent).unwrap();
    driver.depart(parent).unwrap();
    assert_eq!(
        driver.unload(parent),
        Err(ChildDriverError::Episode(ChildError::Kernel(Error::Relied)))
    );
    assert!(!driver.retired(child));
    assert_eq!(driver.inverse_count(parent), Some(1));
    driver.depart(child).unwrap();
    driver.unload(child).unwrap();
    driver.unload(parent).unwrap();
    assert!(driver.retired(child));
    driver.remove(child).unwrap();
    driver.remove(parent).unwrap();
}

#[test]
fn reactivation_uses_a_new_private_journal_and_new_child_identity() {
    let mut driver = ChildDriver::new();
    let port = Port { key: 20, realm: 5 };
    let provider = driver.insert(None, vec![], vec![port]).unwrap();
    install(&mut driver, provider);
    let parent = driver.insert(None, vec![port], vec![]).unwrap();
    driver.begin(parent).unwrap();
    assert!(driver.admit(parent).unwrap());
    let first = driver.land_child(parent, vec![], vec![]).unwrap();
    let first_generation = driver.episode_generation(parent).unwrap();
    finish(&mut driver, parent);
    driver.retire(provider).unwrap();
    driver.depart(provider).unwrap();
    driver.depart(parent).unwrap();
    driver.unload(parent).unwrap();
    driver.unload(provider).unwrap();
    driver.remove(provider).unwrap();
    let replacement = driver.insert(None, vec![], vec![port]).unwrap();
    install(&mut driver, replacement);
    driver.begin(parent).unwrap();
    assert_eq!(driver.inverse_count(parent), Some(0));
    assert_eq!(
        driver.episode_generation(parent),
        Some(first_generation + 1)
    );
    assert!(driver.admit(parent).unwrap());
    let second = driver.land_child(parent, vec![], vec![]).unwrap();
    assert_ne!(first, second);
    driver.remove(first).unwrap();
    driver.retire(second).unwrap();
    assert_eq!(driver.remove(second), Err(ChildDriverError::Retained));
    assert_eq!(driver.inverse_count(parent), Some(1));
}

#[test]
fn pending_child_lands_atomically_in_unloading_after_target_loss() {
    let mut driver = ChildDriver::new();
    let port = Port { key: 33, realm: 1 };
    let provider = driver.insert(None, vec![], vec![port]).unwrap();
    install(&mut driver, provider);
    let parent = driver.insert(None, vec![port], vec![]).unwrap();
    driver.begin(parent).unwrap();
    assert!(driver.admit(parent).unwrap());
    driver.retire(provider).unwrap();
    driver.depart(provider).unwrap();
    assert_eq!(driver.depart(parent), Err(ChildDriverError::Pending));
    assert_eq!(driver.check_child(parent, &[], &[]), Ok(()));
    assert_eq!(driver.phase(parent), Some(Phase::Loading));
    assert_eq!(driver.inverse_count(parent), Some(0));
    let child = driver.land_child(parent, vec![], vec![]).unwrap();
    assert_eq!(driver.phase(parent), Some(Phase::Unloading));
    assert_eq!(driver.inverse_count(parent), Some(1));
    assert_eq!(driver.phase(child), Some(Phase::Inactive));
    assert!(!driver.retired(child));
    driver.unload(parent).unwrap();
    assert!(driver.retired(child));
    driver.unload(provider).unwrap();
}

#[test]
fn retired_parent_pending_child_is_captured_before_direct_diversion() {
    let mut driver = ChildDriver::new();
    let parent = driver.insert(None, vec![], vec![]).unwrap();
    driver.begin(parent).unwrap();
    assert!(driver.admit(parent).unwrap());
    driver.retire(parent).unwrap();
    let child = driver.land_child(parent, vec![], vec![]).unwrap();
    assert_eq!(driver.phase(parent), Some(Phase::Unloading));
    driver.unload(parent).unwrap();
    assert!(driver.retired(child));
    driver.remove(child).unwrap();
    driver.remove(parent).unwrap();
}

#[test]
fn external_parent_link_is_not_an_effect_inverse_or_a_service_dependency() {
    let mut driver = ChildDriver::new();
    let parent = driver.insert(None, vec![], vec![]).unwrap();
    let external_child = driver.insert(Some(parent), vec![], vec![]).unwrap();
    install(&mut driver, parent);
    install(&mut driver, external_child);
    driver.retire(parent).unwrap();
    driver.depart(parent).unwrap();
    driver.unload(parent).unwrap();
    assert_eq!(driver.phase(external_child), Some(Phase::Active));
    assert!(!driver.retired(external_child));
    assert_eq!(driver.inverse_count(parent), Some(0));
    assert_eq!(
        driver.remove(parent),
        Err(ChildDriverError::Kernel(Error::Children))
    );
    driver.retire(external_child).unwrap();
    driver.depart(external_child).unwrap();
    driver.unload(external_child).unwrap();
    driver.remove(external_child).unwrap();
    driver.remove(parent).unwrap();
}

#[test]
fn child_preflight_rechecks_live_reservations_and_retry_keeps_the_inverse_prefix() {
    let mut driver = ChildDriver::new();
    let port = Port { key: 81, realm: 2 };
    let parent = driver.insert(None, vec![], vec![]).unwrap();
    let other_parent = driver.insert(None, vec![], vec![]).unwrap();
    driver.begin(parent).unwrap();
    assert!(driver.admit(parent).unwrap());
    let prefix = driver.land_child(parent, vec![], vec![]).unwrap();
    assert!(driver.admit(parent).unwrap());
    assert_eq!(driver.check_child(parent, &[], &[port]), Ok(()));
    assert_eq!(driver.inverse_count(parent), Some(1));

    // Successful preflight does not reserve a provision for the pending stage.
    driver.begin(other_parent).unwrap();
    assert!(driver.admit(other_parent).unwrap());
    let blocker = driver.land_child(other_parent, vec![], vec![port]).unwrap();
    let conflict = ChildDriverError::Episode(ChildError::Kernel(Error::Conflict));
    assert_eq!(driver.check_child(parent, &[], &[port]), Err(conflict));
    assert_eq!(driver.check_child(parent, &[], &[port]), Err(conflict));
    assert_eq!(driver.land_child(parent, vec![], vec![port]), Err(conflict));
    assert_eq!(driver.inverse_count(parent), Some(1));
    assert_eq!(driver.depart(parent), Err(ChildDriverError::Pending));
    assert_eq!(driver.phase(parent), Some(Phase::Loading));
    assert!(!driver.retired(prefix));

    finish(&mut driver, other_parent);
    driver.retire(other_parent).unwrap();
    driver.depart(other_parent).unwrap();
    driver.unload(other_parent).unwrap();
    assert!(driver.retired(blocker));
    assert_eq!(driver.phase(blocker), Some(Phase::Inactive));
    assert_eq!(driver.check_child(parent, &[], &[port]), Err(conflict));
    assert_eq!(driver.land_child(parent, vec![], vec![port]), Err(conflict));
    assert_eq!(
        driver.check_and_land_child(parent, vec![], vec![port]),
        Err(conflict)
    );
    assert_eq!(driver.inverse_count(parent), Some(1));

    // Retirement and an empty inverse journal do not release the registry slot.
    driver.remove(blocker).unwrap();
    assert_eq!(driver.check_child(parent, &[], &[port]), Ok(()));
    let child = driver
        .check_and_land_child(parent, vec![], vec![port])
        .unwrap();
    assert_eq!(driver.inverse_count(parent), Some(2));
    finish(&mut driver, parent);
    driver.retire(parent).unwrap();
    driver.depart(parent).unwrap();
    driver.unload(parent).unwrap();
    assert!(driver.retired(prefix));
    assert!(driver.retired(child));
}
