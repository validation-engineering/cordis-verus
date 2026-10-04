use cordis_kernel::ownership::{ChildEpisode, ChildError};
use cordis_kernel::{Error, Kernel, Phase, Port};

fn reset(kernel: &mut Kernel, actor: usize) {
    kernel.leave(actor).unwrap();
    kernel.begin_cleanup(actor).unwrap();
    kernel.finish_cleanup(actor).unwrap();
}

#[test]
fn checked_handle_rejects_a_new_episode_with_identical_empty_bindings() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    assert_eq!(kernel.episode_generation(parent), Some(0));
    kernel.begin(parent).unwrap();
    let mut old = ChildEpisode::attach(&kernel, parent).unwrap();
    assert_eq!(old.admit_current(&kernel), Ok(true));
    let child = old.land_child(&mut kernel, vec![], vec![]).unwrap();
    assert_eq!(old.admit_current(&kernel), Ok(true));
    let old_bindings = kernel.committed(parent);

    // The raw Kernel can be called independently. Its next activation has
    // exactly the same target/committed identities, but a different episode.
    reset(&mut kernel, parent);
    kernel.compact_bindings();
    kernel.compact_declarations();
    kernel.begin(parent).unwrap();
    assert_eq!(kernel.episode_generation(parent), Some(2));
    assert_eq!(kernel.committed(parent), old_bindings);
    assert_eq!(
        old.admit_current(&kernel),
        Err(ChildError::Kernel(Error::Changed))
    );
    let identities = kernel.identity_slots();
    assert_eq!(
        old.land_child(&mut kernel, vec![], vec![]),
        Err(ChildError::Kernel(Error::Changed))
    );
    assert_eq!(kernel.identity_slots(), identities);
    assert!(old.is_pending());
    assert_eq!(old.len(), 1);
    assert!(!kernel.retired(child));

    let mut current = ChildEpisode::attach(&kernel, parent).unwrap();
    assert_eq!(current.admit_current(&kernel), Ok(true));
    assert!(current.end());
    old.cancel();
    // The old pending stage is intentionally reconciled by this test before
    // asking the settled old accumulator to restore a later parent episode.
    assert!(old.end());
    kernel.leave(parent).unwrap();
    assert_eq!(
        old.finish_restore(&mut kernel),
        Err(ChildError::Kernel(Error::Changed))
    );
    assert_eq!(kernel.phase(parent), Some(Phase::Unloading));
    assert!(!kernel.cleanup_started(parent));
    assert!(!kernel.retired(child));
    assert_eq!(old.len(), 1);

    // The actual old child inverse remains usable as a standalone retirement;
    // it must not complete the new parent's lifecycle on its own.
    assert_eq!(old.rollback_one(&mut kernel), Ok(Some(child)));
    assert!(kernel.retired(child));
    assert_eq!(kernel.phase(parent), Some(Phase::Unloading));
    current.finish_restore(&mut kernel).unwrap();
    assert_eq!(kernel.phase(parent), Some(Phase::Inactive));
    assert_eq!(kernel.episode_generation(parent), Some(2));
}

#[test]
fn detached_accumulator_binds_on_first_checked_use() {
    let mut kernel = Kernel::new();
    let actor = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.begin(actor).unwrap();
    let mut episode = ChildEpisode::new(actor, vec![]);
    assert_eq!(episode.admit_current(&kernel), Ok(true));
    reset(&mut kernel, actor);
    kernel.begin(actor).unwrap();
    assert_eq!(
        episode.admit_current(&kernel),
        Err(ChildError::Kernel(Error::Changed))
    );
    assert!(episode.is_pending());
}

#[test]
fn generation_changes_only_on_successful_begin_and_survives_compaction() {
    let mut kernel = Kernel::new();
    let missing = Port { key: 44, realm: 1 };
    let actor = kernel.insert(None, vec![missing], vec![]).unwrap();
    assert_eq!(kernel.begin(actor), Err(Error::MissingDependency));
    assert_eq!(kernel.episode_generation(actor), Some(0));
    let provider = kernel.insert(None, vec![], vec![missing]).unwrap();
    kernel.begin(provider).unwrap();
    kernel.finish(provider).unwrap();
    kernel.begin(actor).unwrap();
    assert_eq!(kernel.episode_generation(actor), Some(1));
    assert_eq!(kernel.begin(actor), Err(Error::InvalidState));
    assert_eq!(kernel.episode_generation(actor), Some(1));
    reset(&mut kernel, actor);
    kernel.compact_bindings();
    kernel.compact_declarations();
    kernel.begin(actor).unwrap();
    assert_eq!(kernel.episode_generation(actor), Some(2));
    kernel.retire(actor).unwrap();
    reset(&mut kernel, actor);
    assert_eq!(kernel.begin(actor), Err(Error::Retired));
    assert_eq!(kernel.episode_generation(actor), Some(2));
    kernel.remove(actor).unwrap();
    assert_eq!(kernel.episode_generation(actor), None);
}
