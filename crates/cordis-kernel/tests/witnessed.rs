use cordis_kernel::resources::ResourceError;
use cordis_kernel::witnessed::{EpisodeError, ResourceEpisode};
use cordis_kernel::Binding;

#[test]
fn cancelled_stage_lands_real_inverse_before_exact_recovery() {
    let target = [Binding {
        key: 1,
        realm: 3,
        provider: 7,
    }];
    let mut episode = ResourceEpisode::new(vec![11, 22], target.to_vec());
    assert!(episode.admit(Some(&target)));
    episode.land_write(1, 0, 33).unwrap();
    assert!(episode.admit(Some(&target)));
    episode.cancel();
    assert!(!episode.rollback());
    assert!(!episode.rollback_one());
    assert_eq!(episode.read(0), Some(33));
    // Cancellation keeps the admitted stage alive and captures its real inverse.
    episode.land_write(1, 1, 44).unwrap();
    assert_eq!(episode.len(), 2);
    assert!(episode.rollback_one());
    assert_eq!(episode.read(1), Some(22));
    assert_eq!(episode.read(0), Some(33));
    assert!(episode.rollback());
    assert_eq!(episode.read(0), Some(11));
    assert!(episode.is_empty());
    assert!(!episode.admit(Some(&target)));
}

#[test]
fn failed_resource_stage_keeps_context_and_witness_prefix() {
    let mut episode = ResourceEpisode::new(vec![1], vec![]);
    assert_eq!(episode.land_write(5, 0, 2), Err(EpisodeError::NotAdmitted));
    assert!(episode.admit(Some(&[])));
    episode.land_write(5, 0, 2).unwrap();
    assert!(episode.admit(Some(&[])));
    assert_eq!(
        episode.land_write(6, 0, 3),
        Err(EpisodeError::Resource(ResourceError::Owned))
    );
    assert_eq!(episode.read(0), Some(2));
    assert_eq!(episode.len(), 1);
    assert!(!episode.rollback());
    // A failed write leaves the admitted stage available for a valid retry.
    episode.land_write(5, 0, 4).unwrap();
    assert!(episode.admit(Some(&[])));
    assert!(episode.end());
    assert!(episode.rollback());
    assert_eq!(episode.read(0), Some(1));
}

#[test]
fn changing_provider_cannot_start_a_new_resource_stage() {
    let committed = Binding {
        key: 1,
        realm: 0,
        provider: 1,
    };
    let changed = Binding {
        provider: 2,
        ..committed
    };
    let mut episode = ResourceEpisode::new(vec![9], vec![committed]);
    assert!(!episode.admit(Some(&[changed])));
    assert_eq!(episode.land_write(1, 0, 0), Err(EpisodeError::NotAdmitted));
    assert!(episode.rollback());
    assert_eq!(episode.read(0), Some(9));
}

#[test]
fn restart_changes_only_episode_metadata_after_recovery() {
    let mut episode = ResourceEpisode::new(vec![14], vec![]);
    assert!(episode.admit(Some(&[])));
    assert!(!episode.restart(vec![]));
    episode.land_write(1, 0, 29).unwrap();
    assert!(!episode.restart(vec![]));
    assert_eq!(episode.read(0), Some(29));
    episode.cancel();
    assert!(episode.rollback());
    assert_eq!(episode.read(0), Some(14));
    let binding = Binding {
        key: 1,
        realm: 0,
        provider: 6,
    };
    assert!(episode.restart(vec![binding]));
    assert_eq!(episode.read(0), Some(14));
    assert!(!episode.admit(Some(&[])));
    assert!(episode.restart(vec![binding]));
    assert!(episode.admit(Some(&[binding])));
    episode.land_write(2, 0, 51).unwrap();
    episode.cancel();
    assert!(episode.rollback());
    assert_eq!(episode.read(0), Some(14));
}
