use cordis_driver::shared::{CleanupOutcome, LifecycleDriver};
use cordis_driver::ActionTicket;
use cordis_kernel::publication::{LeaseId, PublicationId, PublicationRegistry};
use cordis_kernel::{Phase, Port};

const SOURCE: Port = Port { key: 41, realm: 2 };
const OWN: Port = Port { key: 42, realm: 2 };

struct Fixture {
    driver: LifecycleDriver,
    registry: PublicationRegistry,
    consumer: usize,
    publication: PublicationId,
    lease: LeaseId,
    other_lease: LeaseId,
    ticket: ActionTicket,
}

fn fixture() -> Fixture {
    let mut driver = LifecycleDriver::new().unwrap();
    let provider = driver.insert(None, vec![], vec![SOURCE]).unwrap();
    let consumer = driver.insert(None, vec![SOURCE], vec![OWN]).unwrap();
    let other = driver.insert(None, vec![SOURCE], vec![]).unwrap();
    for id in [provider, consumer, other] {
        driver.begin(id).unwrap();
        driver.settle_setup(id).unwrap();
        driver.finish(id).unwrap();
    }
    let mut registry = PublicationRegistry::for_domain(driver.domain());
    let source = registry.publish(provider, 1, SOURCE, 101).unwrap();
    let publication = registry.publish(consumer, 1, OWN, 202).unwrap();
    let lease = registry.acquire_for(source, consumer, 1).unwrap();
    let other_lease = registry.acquire_for(source, other, 1).unwrap();
    driver.retire(consumer).unwrap();
    driver.leave(consumer).unwrap();
    registry.revoke(publication).unwrap();
    driver.begin_cleanup(consumer).unwrap();
    let ticket = driver.pending_action(consumer).unwrap().clone();
    Fixture {
        driver,
        registry,
        consumer,
        publication,
        lease,
        other_lease,
        ticket,
    }
}

#[test]
fn failed_report_retains_resources_until_fresh_retry_releases_only_its_batch() {
    let mut f = fixture();
    let committed = f.driver.committed(f.consumer);
    f.driver
        .complete_cleanup(&f.ticket, CleanupOutcome::Failed)
        .unwrap();
    assert!(f
        .driver
        .finish_cleanup_resources(
            &mut f.registry,
            f.consumer,
            false,
            &[f.lease],
            &[f.publication]
        )
        .is_err());
    assert_eq!(f.driver.committed(f.consumer), committed);
    assert_eq!(f.registry.leased_slot(f.lease), Ok(101));
    assert!(f.registry.entry(f.publication).unwrap().retained);
    let retry = f.driver.retry_cleanup(f.consumer).unwrap();
    assert!(retry.action > f.ticket.action);
    assert!(f
        .driver
        .complete_cleanup(&f.ticket, CleanupOutcome::Succeeded)
        .is_err());
    f.driver
        .complete_cleanup(&retry, CleanupOutcome::Succeeded)
        .unwrap();
    let released = f
        .driver
        .finish_cleanup_resources(
            &mut f.registry,
            f.consumer,
            false,
            &[f.lease],
            &[f.publication],
        )
        .unwrap();
    assert_eq!(released.len(), 1);
    assert_eq!(released[0].publication, f.publication);
    assert_eq!(released[0].slot, 202);
    assert_eq!(f.driver.phase(f.consumer), Some(Phase::Inactive));
    assert!(f.driver.committed(f.consumer).is_empty());
    assert!(f.registry.lease(f.lease).is_none());
    assert_eq!(f.registry.leased_slot(f.other_lease), Ok(101));
    assert!(!f.registry.entry(f.publication).unwrap().retained);
    assert!(f
        .driver
        .finish_cleanup_resources(&mut f.registry, f.consumer, false, &[], &[])
        .is_err());
}

#[test]
fn late_invalid_manifest_items_cannot_partially_release_an_accepted_cleanup() {
    let mut f = fixture();
    f.driver
        .complete_cleanup(&f.ticket, CleanupOutcome::Succeeded)
        .unwrap();
    let committed = f.driver.committed(f.consumer);
    let publication = f.registry.entry(f.publication);
    let future = f
        .registry
        .acquire_for(PublicationId(0), f.consumer, 2)
        .unwrap();
    let unscoped = f.registry.acquire(PublicationId(0)).unwrap();
    for leases in [
        vec![f.lease, f.other_lease],
        vec![f.lease, f.lease],
        vec![f.lease, future],
        vec![f.lease, unscoped],
    ] {
        assert!(f
            .driver
            .finish_cleanup_resources(
                &mut f.registry,
                f.consumer,
                false,
                &leases,
                &[f.publication]
            )
            .is_err());
        assert_eq!(f.driver.committed(f.consumer), committed);
        assert_eq!(f.registry.entry(f.publication), publication);
        assert_eq!(f.registry.leased_slot(f.lease), Ok(101));
        assert_eq!(f.registry.lease_record_count(), 4);
    }
    for publications in [
        vec![f.publication, PublicationId(999)],
        vec![f.publication, f.publication],
        vec![f.publication, PublicationId(0)],
    ] {
        assert!(f
            .driver
            .finish_cleanup_resources(
                &mut f.registry,
                f.consumer,
                false,
                &[f.lease],
                &publications
            )
            .is_err());
        assert_eq!(f.registry.entry(f.publication), publication);
        assert_eq!(f.registry.leased_slot(f.lease), Ok(101));
        assert_eq!(f.driver.phase(f.consumer), Some(Phase::Unloading));
    }
    for (leases, publications) in [(vec![], vec![f.publication]), (vec![f.lease], vec![])] {
        assert!(f
            .driver
            .finish_cleanup_resources(&mut f.registry, f.consumer, false, &leases, &publications)
            .is_err());
        assert_eq!(f.registry.leased_slot(f.lease), Ok(101));
        assert_eq!(f.registry.entry(f.publication), publication);
        assert_eq!(f.driver.committed(f.consumer), committed);
    }
    // The successful callback report remains usable: correcting the manifest
    // does not require replaying callbacks or accepting a duplicate completion.
    f.driver
        .finish_cleanup_resources(
            &mut f.registry,
            f.consumer,
            false,
            &[f.lease],
            &[f.publication],
        )
        .unwrap();
    assert_eq!(f.registry.leased_slot(future), Ok(101));
    assert_eq!(f.registry.leased_slot(unscoped), Ok(101));
}

#[test]
fn a_foreign_registry_with_identical_local_ids_cannot_use_this_cleanup_receipt() {
    let mut f = fixture();
    f.driver
        .complete_cleanup(&f.ticket, CleanupOutcome::Succeeded)
        .unwrap();
    let other_driver = LifecycleDriver::new().unwrap();
    let mut foreign = PublicationRegistry::for_domain(other_driver.domain());
    let source = foreign.publish(0, 1, SOURCE, 101).unwrap();
    let publication = foreign.publish(f.consumer, 1, OWN, 202).unwrap();
    let lease = foreign.acquire_for(source, f.consumer, 1).unwrap();
    foreign.revoke(publication).unwrap();
    assert_eq!(lease, f.lease);
    assert_eq!(publication, f.publication);
    let committed = f.driver.committed(f.consumer);
    assert!(f
        .driver
        .finish_cleanup_resources(&mut foreign, f.consumer, false, &[lease], &[publication])
        .is_err());
    assert_eq!(foreign.leased_slot(lease), Ok(101));
    assert!(foreign.entry(publication).unwrap().retained);
    assert_eq!(f.driver.committed(f.consumer), committed);
    f.driver
        .finish_cleanup_resources(
            &mut f.registry,
            f.consumer,
            false,
            &[f.lease],
            &[f.publication],
        )
        .unwrap();
}

#[test]
fn a_remaining_consumer_lease_blocks_the_entire_publication_batch() {
    let mut f = fixture();
    // Simulate an outstanding managed holder outside the selected manifest.
    // The registry guard must protect it independently of Kernel declarations.
    // Acquisition must precede revocation, so use another publication of this episode.
    let later = f
        .registry
        .publish(f.consumer, 1, Port { key: 43, realm: 2 }, 303)
        .unwrap();
    let holder = f.registry.acquire_for(later, 99, 1).unwrap();
    f.registry.revoke(later).unwrap();
    f.driver
        .complete_cleanup(&f.ticket, CleanupOutcome::Succeeded)
        .unwrap();
    let committed = f.driver.committed(f.consumer);
    assert!(f
        .driver
        .finish_cleanup_resources(
            &mut f.registry,
            f.consumer,
            false,
            &[f.lease],
            &[f.publication, later]
        )
        .is_err());
    assert!(f.registry.entry(f.publication).unwrap().retained);
    assert_eq!(f.registry.leased_slot(f.lease), Ok(101));
    assert_eq!(f.registry.leased_slot(holder), Ok(303));
    assert_eq!(f.driver.committed(f.consumer), committed);
    f.registry.release(holder).unwrap();
    let released = f
        .driver
        .finish_cleanup_resources(
            &mut f.registry,
            f.consumer,
            false,
            &[f.lease],
            &[f.publication, later],
        )
        .unwrap();
    assert_eq!(
        released.iter().map(|item| item.slot).collect::<Vec<_>>(),
        vec![202, 303]
    );
}

#[test]
fn reservation_cleanup_releases_generation_zero_only_after_a_successful_retry() {
    let mut driver = LifecycleDriver::new().unwrap();
    let owner = driver.insert(None, vec![], vec![OWN]).unwrap();
    let mut registry = PublicationRegistry::for_domain(driver.domain());
    let publication = registry.publish(owner, 0, OWN, 202).unwrap();
    driver.retire(owner).unwrap();
    registry.revoke(publication).unwrap();
    driver.begin_reservation_cleanup(owner).unwrap();
    let ticket = driver.pending_action(owner).unwrap().clone();
    driver
        .complete_cleanup(&ticket, CleanupOutcome::Failed)
        .unwrap();
    assert!(driver
        .finish_cleanup_resources(&mut registry, owner, true, &[], &[publication])
        .is_err());
    assert!(registry.entry(publication).unwrap().retained);
    let retry = driver.retry_cleanup(owner).unwrap();
    driver
        .complete_cleanup(&retry, CleanupOutcome::Succeeded)
        .unwrap();
    assert!(driver
        .finish_cleanup_resources(&mut registry, owner, false, &[], &[publication])
        .is_err());
    let released = driver
        .finish_cleanup_resources(&mut registry, owner, true, &[], &[publication])
        .unwrap();
    assert_eq!(released[0].slot, 202);
    assert_eq!(driver.episode_generation(owner), Some(0));
    assert_eq!(driver.phase(owner), Some(Phase::Inactive));
    driver.remove(owner).unwrap();
}
