use cordis_kernel::ownership::{ChildEpisode, ChildError};
use cordis_kernel::{Error, Kernel, Phase, Port};

fn install(kernel: &mut Kernel, id: usize) {
    kernel.begin(id).unwrap();
    kernel.finish(id).unwrap();
}

fn remove_retired(kernel: &mut Kernel, id: usize) {
    if kernel.phase(id) != Some(Phase::Inactive) {
        kernel.leave_if_changed(id).unwrap();
        kernel.begin_cleanup(id).unwrap();
        kernel.finish_cleanup(id).unwrap();
    }
    kernel.remove(id).unwrap();
}

#[test]
fn complete_parent_restore_retires_active_children_without_waiting() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let mut episode = ChildEpisode::new(parent, kernel.committed(parent));
    assert!(episode.admit(Some(&[])));
    let first = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    install(&mut kernel, first);
    assert!(episode.admit(Some(&[])));
    let second = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    install(&mut kernel, second);
    assert!(episode.admit(Some(&[])));
    assert!(episode.end());
    kernel.finish(parent).unwrap();
    kernel.retire(parent).unwrap();
    kernel.leave_if_changed(parent).unwrap();

    episode.finish_restore(&mut kernel).unwrap();
    assert!(episode.is_empty());
    assert_eq!(kernel.phase(parent), Some(Phase::Inactive));
    for child in [first, second] {
        assert!(kernel.retired(child));
        assert_eq!(kernel.phase(child), Some(Phase::Active));
    }
    assert_eq!(kernel.remove(parent), Err(Error::Children));
    remove_retired(&mut kernel, second);
    remove_retired(&mut kernel, first);
    kernel.remove(parent).unwrap();
}

#[test]
fn pending_instantiation_lands_after_parent_retirement_and_is_recovered() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let mut episode = ChildEpisode::attach(&kernel, parent).unwrap();
    assert_eq!(episode.admit_current(&kernel), Ok(true));
    kernel.retire(parent).unwrap();
    assert_eq!(episode.admit_current(&kernel), Ok(true));
    assert_eq!(episode.rollback_one(&mut kernel), Ok(None));
    assert_eq!(
        episode.finish_restore(&mut kernel),
        Err(ChildError::NotAdmitted)
    );

    // Definition 52 permits a registered retired parent: the outstanding stage
    // still yields its child and inverse before the L-Divert landing completes.
    let child = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    assert_eq!(kernel.phase(child), Some(Phase::Inactive));
    assert!(!kernel.retired(child));
    kernel.leave_if_changed(parent).unwrap();
    episode.finish_restore(&mut kernel).unwrap();
    assert!(kernel.retired(child));
    assert_eq!(kernel.phase(parent), Some(Phase::Inactive));
}

#[test]
fn child_inverses_retire_in_lifo_order_and_keep_lifecycle_unchanged() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let mut episode = ChildEpisode::new(parent, vec![]);
    assert!(episode.admit(Some(&[])));
    let first = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    assert!(episode.admit(Some(&[])));
    let second = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    install(&mut kernel, first);
    install(&mut kernel, second);
    episode.cancel();
    assert_eq!(episode.rollback_one(&mut kernel), Ok(Some(second)));
    assert!(kernel.retired(second));
    assert!(!kernel.retired(first));
    assert_eq!(kernel.phase(second), Some(Phase::Active));
    assert_eq!(episode.rollback_one(&mut kernel), Ok(Some(first)));
    assert_eq!(episode.rollback_one(&mut kernel), Ok(None));
    assert_eq!(kernel.phase(first), Some(Phase::Active));
}

#[test]
fn dependency_guard_blocks_child_accumulator_before_any_retirement() {
    let mut kernel = Kernel::new();
    let port = Port { key: 8, realm: 0 };
    let parent = kernel.insert(None, vec![], vec![port]).unwrap();
    kernel.begin(parent).unwrap();
    let mut episode = ChildEpisode::new(parent, vec![]);
    assert!(episode.admit(Some(&[])));
    let child = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    assert!(episode.admit(Some(&[])));
    assert!(episode.end());
    kernel.finish(parent).unwrap();
    let consumer = kernel.insert(None, vec![port], vec![]).unwrap();
    install(&mut kernel, consumer);
    kernel.retire(parent).unwrap();
    kernel.leave_if_changed(parent).unwrap();

    assert_eq!(
        episode.finish_restore(&mut kernel),
        Err(ChildError::Kernel(Error::Relied))
    );
    assert_eq!(episode.len(), 1);
    assert!(!kernel.retired(child));
    kernel.leave_if_changed(consumer).unwrap();
    kernel.begin_cleanup(consumer).unwrap();
    kernel.finish_cleanup(consumer).unwrap();
    episode.finish_restore(&mut kernel).unwrap();
    assert!(kernel.retired(child));
}

#[test]
fn failed_instantiation_keeps_the_admitted_stage_and_inverse_prefix() {
    let mut kernel = Kernel::new();
    let port = Port { key: 9, realm: 4 };
    let parent = kernel.insert(None, vec![], vec![port]).unwrap();
    kernel.begin(parent).unwrap();
    let mut episode = ChildEpisode::new(parent, vec![]);
    assert_eq!(
        episode.land_child(&mut kernel, vec![], vec![]),
        Err(ChildError::NotAdmitted)
    );
    assert!(episode.admit(Some(&[])));
    assert_eq!(
        episode.land_child(&mut kernel, vec![], vec![port]),
        Err(ChildError::Kernel(Error::Conflict))
    );
    assert!(episode.is_empty());
    let child = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    episode.cancel();
    kernel.retire(child).unwrap();
    assert!(episode.rollback(&mut kernel));
    assert!(episode.is_empty());
    assert!(kernel.retired(child));
}

#[test]
fn externally_removed_child_is_not_misreported_as_a_retirement_inverse() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let mut episode = ChildEpisode::new(parent, vec![]);
    assert!(episode.admit(Some(&[])));
    let child = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    episode.cancel();
    kernel.retire(child).unwrap();
    kernel.remove(child).unwrap();
    assert_eq!(
        episode.rollback_one(&mut kernel),
        Err(ChildError::Kernel(Error::Unknown))
    );
    // Full recovery also checks its complete inverse domain at runtime. It
    // must terminate and reject before consuming the witness or entering the
    // kernel's restoration phase, even though ordinary Rust erases preconditions.
    assert!(!episode.rollback(&mut kernel));
    assert_eq!(episode.len(), 1);
    kernel.retire(parent).unwrap();
    kernel.leave_if_changed(parent).unwrap();
    assert_eq!(
        episode.finish_restore(&mut kernel),
        Err(ChildError::Kernel(Error::Unknown))
    );
    assert!(!kernel.cleanup_started(parent));
    assert_eq!(kernel.phase(parent), Some(Phase::Unloading));
    // O-Retire requires a registered child. A host that treats an absent child
    // as already recovered needs a separate observational-extension theorem.
    assert_eq!(episode.len(), 1);
}

#[test]
fn checked_admission_observes_target_loss_and_preserves_an_admitted_landing() {
    let mut kernel = Kernel::new();
    let port = Port { key: 31, realm: 2 };
    let provider = kernel.insert(None, vec![], vec![port]).unwrap();
    install(&mut kernel, provider);
    let parent = kernel.insert(None, vec![port], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let mut pending = ChildEpisode::attach(&kernel, parent).unwrap();
    let mut idle = ChildEpisode::attach(&kernel, parent).unwrap();
    assert_eq!(pending.admit_current(&kernel), Ok(true));
    kernel.retire(provider).unwrap();
    kernel.leave_if_changed(provider).unwrap();
    // A new stage cannot start from the obsolete target. The already admitted
    // iteration still lands and captures its actual child retirement inverse.
    assert_eq!(idle.admit_current(&kernel), Ok(false));
    assert_eq!(
        idle.land_child(&mut kernel, vec![], vec![]),
        Err(ChildError::NotAdmitted)
    );
    assert_eq!(pending.admit_current(&kernel), Ok(true));
    assert!(pending.is_pending());
    let child = pending.land_child(&mut kernel, vec![], vec![]).unwrap();
    assert!(!pending.is_pending());
    kernel.leave_if_changed(parent).unwrap();
    pending.finish_restore(&mut kernel).unwrap();
    assert!(kernel.retired(child));
    kernel.begin_cleanup(provider).unwrap();
    kernel.finish_cleanup(provider).unwrap();
}

#[test]
fn checked_entry_points_reject_a_handle_from_an_old_committed_episode() {
    let mut kernel = Kernel::new();
    let port = Port { key: 41, realm: 3 };
    let provider = kernel.insert(None, vec![], vec![port]).unwrap();
    install(&mut kernel, provider);
    let parent = kernel.insert(None, vec![port], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let mut old_episode = ChildEpisode::attach(&kernel, parent).unwrap();
    assert_eq!(old_episode.admit_current(&kernel), Ok(true));
    let existing_child = old_episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    assert_eq!(old_episode.admit_current(&kernel), Ok(true));
    kernel.retire(provider).unwrap();
    kernel.leave_if_changed(provider).unwrap();
    // The low-level Kernel remains independently callable. Simulate a caller
    // replacing the live episode without reconciling its old effect handle.
    kernel.leave_if_changed(parent).unwrap();
    kernel.begin_cleanup(parent).unwrap();
    kernel.finish_cleanup(parent).unwrap();
    kernel.begin_cleanup(provider).unwrap();
    kernel.finish_cleanup(provider).unwrap();
    kernel.remove(provider).unwrap();
    let replacement = kernel.insert(None, vec![], vec![port]).unwrap();
    install(&mut kernel, replacement);
    kernel.begin(parent).unwrap();
    assert_eq!(
        old_episode.admit_current(&kernel),
        Err(ChildError::Kernel(Error::Changed))
    );
    assert_eq!(
        old_episode.land_child(&mut kernel, vec![], vec![]),
        Err(ChildError::Kernel(Error::Changed))
    );
    assert!(old_episode.is_pending());
    assert_eq!(old_episode.len(), 1);
    assert!(!kernel.retired(existing_child));
    let mut current_episode = ChildEpisode::attach(&kernel, parent).unwrap();
    assert_eq!(current_episode.admit_current(&kernel), Ok(true));
}

#[test]
fn complete_child_recovery_checks_missing_prefix_before_retiring_newest_child() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let mut episode = ChildEpisode::attach(&kernel, parent).unwrap();
    assert_eq!(episode.admit_current(&kernel), Ok(true));
    let first = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    assert_eq!(episode.admit_current(&kernel), Ok(true));
    let newest = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    episode.cancel();
    kernel.retire(first).unwrap();
    kernel.remove(first).unwrap();
    assert!(!episode.rollback(&mut kernel));
    assert_eq!(episode.len(), 2);
    assert!(!kernel.retired(newest));
    kernel.retire(parent).unwrap();
    kernel.leave_if_changed(parent).unwrap();
    assert_eq!(
        episode.finish_restore(&mut kernel),
        Err(ChildError::Kernel(Error::Unknown))
    );
    assert_eq!(episode.len(), 2);
    assert!(!kernel.retired(newest));
    assert!(!kernel.cleanup_started(parent));
}

#[test]
fn detached_child_snapshot_accepts_reordered_repeated_bindings_and_recovers_its_child() {
    let mut kernel = Kernel::new();
    let ports = vec![Port { key: 72, realm: 1 }, Port { key: 73, realm: 1 }];
    let provider = kernel.insert(None, vec![], ports.clone()).unwrap();
    install(&mut kernel, provider);
    let parent = kernel.insert(None, ports, vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let mut captured = kernel.committed(parent);
    captured.reverse();
    captured.push(captured[0]);
    let mut episode = ChildEpisode::new(parent, captured);

    // Definition 53's binding set is unchanged by vector order or repetition.
    assert_eq!(episode.admit_current(&kernel), Ok(true));
    let child = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    episode.cancel();
    kernel.retire(parent).unwrap();
    kernel.leave_if_changed(parent).unwrap();
    episode.finish_restore(&mut kernel).unwrap();
    assert!(kernel.retired(child));
    assert!(episode.is_empty());
}

#[test]
fn checked_child_admission_rejects_a_different_provider_without_settling_the_iterator() {
    let mut kernel = Kernel::new();
    let port = Port { key: 74, realm: 1 };
    let provider = kernel.insert(None, vec![], vec![port]).unwrap();
    install(&mut kernel, provider);
    let parent = kernel.insert(None, vec![port], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let mut captured = kernel.committed(parent);
    captured[0].provider = parent;
    let mut episode = ChildEpisode::new(parent, captured);

    assert_eq!(
        episode.admit_current(&kernel),
        Err(ChildError::Kernel(Error::Changed))
    );
    assert!(!episode.is_pending());
    assert!(!episode.is_settled());
    assert!(episode.is_empty());
    assert_eq!(kernel.phase(parent), Some(Phase::Loading));
}

#[test]
fn checked_child_landing_retries_after_reservation_release_with_the_same_pending_inverse() {
    let mut kernel = Kernel::new();
    let port = Port { key: 82, realm: 3 };
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let mut episode = ChildEpisode::attach(&kernel, parent).unwrap();
    assert_eq!(episode.admit_current(&kernel), Ok(true));
    let prefix = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    assert_eq!(episode.admit_current(&kernel), Ok(true));
    assert_eq!(episode.check_child(&kernel, &[], &[port]), Ok(()));
    let blocker = kernel.insert(Some(parent), vec![], vec![port]).unwrap();
    assert_eq!(
        episode.check_child(&kernel, &[], &[port]),
        Err(ChildError::Kernel(Error::Conflict))
    );
    assert_eq!(
        episode.land_child(&mut kernel, vec![], vec![port]),
        Err(ChildError::Kernel(Error::Conflict))
    );
    assert!(episode.is_pending());
    assert!(!episode.is_settled());
    assert_eq!(episode.child_at(0), Some(prefix));
    assert_eq!(episode.len(), 1);
    kernel.retire(blocker).unwrap();
    assert_eq!(
        episode.check_child(&kernel, &[], &[port]),
        Err(ChildError::Kernel(Error::Conflict))
    );
    kernel.remove(blocker).unwrap();
    assert_eq!(episode.check_child(&kernel, &[], &[port]), Ok(()));
    let child = episode.land_child(&mut kernel, vec![], vec![port]).unwrap();
    assert_eq!(episode.child_at(0), Some(prefix));
    assert_eq!(episode.child_at(1), Some(child));
    assert!(!episode.is_pending());
    episode.cancel();
    kernel.retire(parent).unwrap();
    kernel.leave_if_changed(parent).unwrap();
    episode.finish_restore(&mut kernel).unwrap();
    assert!(kernel.retired(prefix));
    assert!(kernel.retired(child));
}
