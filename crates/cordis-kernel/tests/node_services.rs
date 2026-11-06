use cordis_kernel::lifecycle_state::cleanup::CleanupCommand as C;
use cordis_kernel::node_runtime::episode::{Command as E, EpisodeError};
use cordis_kernel::node_runtime::services::ServiceError as S;
use cordis_kernel::node_runtime::NodeRuntime;
use cordis_kernel::publication::{PublicationError as P, PublicationId};
use cordis_kernel::Port;

const PORT: Port = Port { key: 42, realm: 3 };

fn provider(core: &mut NodeRuntime, value: u64) -> (usize, PublicationId) {
    let owner = core.insert(None, vec![], vec![]).unwrap();
    let setup = core.begin(owner).unwrap();
    let publication = core
        .publish_service(owner, setup.generation, PORT, value)
        .unwrap();
    core.complete(setup, None).unwrap();
    core.finish(owner).unwrap();
    (owner, publication)
}

fn cleanup(core: &mut NodeRuntime, owner: usize) {
    core.cleanup(C::Withdraw { id: owner }).unwrap();
    let ticket = core
        .cleanup(C::Request {
            id: owner,
            reservation: false,
        })
        .unwrap()
        .unwrap();
    core.complete(ticket, None).unwrap();
    core.release_owned(owner).unwrap();
}

#[test]
fn foreign_and_old_episode_commands_preserve_the_actual_publication() {
    let mut core = NodeRuntime::new(940);
    let (owner, publication) = provider(&mut core, 10);
    let foreign = core.insert(None, vec![], vec![]).unwrap();
    let setup = core.begin(foreign).unwrap();
    core.complete(setup, None).unwrap();
    core.finish(foreign).unwrap();
    let original = core.store().registry().entry(publication).unwrap();
    assert_eq!(
        core.replace_service(foreign, 1, publication, 99),
        Err(S::StalePublication)
    );
    assert_eq!(
        core.revoke_service(foreign, 1, publication),
        Err(S::StalePublication)
    );
    assert_eq!(
        core.reclaim_service(foreign, 1, publication),
        Err(S::StalePublication)
    );
    assert_eq!(
        core.revoke_service(owner, 1, PublicationId(usize::MAX)),
        Err(S::Publication(P::Unknown))
    );
    assert_eq!(core.store().registry().entry(publication), Some(original));
    assert_eq!(core.store().observation(publication), Some((0, &10)));
    assert!(core.drain_released().is_empty());

    core.revoke_service(owner, 1, publication).unwrap();
    assert_eq!(
        core.replace_service(owner, 1, publication, 11),
        Err(S::Publication(P::Revoked))
    );
    cleanup(&mut core, owner);
    let setup = core.begin(owner).unwrap();
    assert_eq!(setup.generation, 2);
    // The old slot still records owner/generation 1. Matching those fields is
    // insufficient after the actual owner has entered its next episode.
    let tombstone = core.store().registry().entry(publication).unwrap();
    assert_eq!(
        core.revoke_service(owner, 1, publication),
        Err(S::StalePublication)
    );
    assert_eq!(
        core.reclaim_service(owner, 1, publication),
        Err(S::StalePublication)
    );
    assert_eq!(
        core.replace_service(owner, 1, publication, 12),
        Err(S::Access(EpisodeError::Stale))
    );
    assert_eq!(core.store().registry().entry(publication), Some(tombstone));
}

#[test]
fn reclaim_waits_for_real_lease_then_transfers_the_dynamic_declaration() {
    let mut core = NodeRuntime::new(941);
    let (owner, publication) = provider(&mut core, 10);
    let consumer = core.insert(None, vec![PORT], vec![]).unwrap();
    let setup = core.begin(consumer).unwrap();
    core.complete(setup, None).unwrap();
    core.finish(consumer).unwrap();
    let lease = core.admission(consumer).unwrap().resources()[0].lease;
    core.set_checked(publication.0, true);
    core.cleanup(C::Retire { id: owner }).unwrap();
    assert_eq!(
        core.replace_service(owner, 1, publication, 11),
        Err(S::Access(EpisodeError::Closed))
    );
    // Retirement closes writes but must not disable its own cleanup.
    core.revoke_service(owner, 1, publication).unwrap();
    core.revoke_service(owner, 1, publication).unwrap();
    let next = core.insert(None, vec![], vec![]).unwrap();
    core.episode_command(E::Prepare { id: next }).unwrap();
    let replacement = core.publish_service(next, 0, PORT, 20).unwrap();
    assert_eq!(core.reclaim_service(owner, 1, publication), Ok(false));
    assert!(core.checked().contains(&publication.0));
    assert_eq!(
        core.dynamic_declarations().get(&(PORT.key, PORT.realm)),
        Some(&owner)
    );
    assert_eq!(
        core.store().leased_observation(lease),
        Ok((publication, 0, &10))
    );

    cleanup(&mut core, consumer);
    assert_eq!(core.reclaim_service(owner, 1, publication), Ok(true));
    assert!(!core.checked().contains(&publication.0));
    assert_eq!(
        core.dynamic_declarations().get(&(PORT.key, PORT.realm)),
        Some(&next)
    );
    assert_eq!(core.store().value(publication), None);
    assert_eq!(core.store().value(replacement), Some(&20));
    assert_eq!(core.reclaim_service(owner, 1, publication), Ok(true));
    assert_eq!(core.drain_released(), vec![10]);
    assert!(core.drain_released().is_empty());
}
