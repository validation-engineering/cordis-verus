use cordis_driver::shared::{CleanupOutcome, LifecycleDriver};
use cordis_driver::{ActionKind, ActionTicket};
use cordis_kernel::{Binding, Error, Phase, Port};

#[derive(Debug, PartialEq, Eq)]
struct Snapshot {
    phase: Option<Phase>,
    generation: Option<u64>,
    retired: bool,
    restoring: bool,
    committed: Vec<Binding>,
    target: Option<Vec<Binding>>,
    pending: Option<ActionTicket>,
}

fn snapshot(driver: &LifecycleDriver, ids: &[usize]) -> Vec<Snapshot> {
    ids.iter()
        .map(|&id| Snapshot {
            phase: driver.phase(id),
            generation: driver.episode_generation(id),
            retired: driver.retired(id),
            restoring: driver.cleanup_started(id),
            committed: driver.committed(id),
            target: driver.target(id),
            pending: driver.pending_action(id).cloned(),
        })
        .collect()
}

fn unloading_pair() -> (LifecycleDriver, usize, usize) {
    let mut driver = LifecycleDriver::new().unwrap();
    let port = Port { key: 7, realm: 3 };
    let provider = driver.insert(None, vec![], vec![port]).unwrap();
    let consumer = driver.insert(None, vec![port], vec![]).unwrap();
    for id in [provider, consumer] {
        driver.begin(id).unwrap();
        driver.settle_setup(id).unwrap();
        driver.finish(id).unwrap();
    }
    for id in [provider, consumer] {
        driver.retire(id).unwrap();
        driver.leave(id).unwrap();
    }
    (driver, provider, consumer)
}

#[test]
fn failed_cleanup_retains_provider_until_an_exact_fresh_retry_succeeds() {
    let (mut driver, provider, consumer) = unloading_pair();
    let ids = [provider, consumer];
    let committed = driver.committed(consumer);
    assert_eq!(committed.len(), 1);
    assert_eq!(committed[0].provider, provider);
    driver.begin_cleanup(consumer).unwrap();
    let failed = driver.pending_action(consumer).unwrap().clone();
    assert_eq!(driver.retry_cleanup(consumer), Err(Error::InvalidState));
    driver
        .complete_cleanup(&failed, CleanupOutcome::Failed)
        .unwrap();
    assert_eq!(driver.pending_action(consumer), None);
    assert_eq!(driver.phase(consumer), Some(Phase::Unloading));
    assert!(driver.cleanup_started(consumer));
    assert_eq!(driver.committed(consumer), committed);
    let after_failure = snapshot(&driver, &ids);
    assert_eq!(driver.finish_cleanup(consumer), Err(Error::InvalidState));
    assert_eq!(driver.remove(consumer), Err(Error::InvalidState));
    assert_eq!(driver.begin_cleanup(provider), Err(Error::Relied));
    assert!(driver
        .complete_cleanup(&failed, CleanupOutcome::Succeeded)
        .is_err());
    assert_eq!(snapshot(&driver, &ids), after_failure);

    let retry = driver.retry_cleanup(consumer).unwrap();
    assert_eq!(retry.domain, failed.domain);
    assert_eq!(retry.id, failed.id);
    assert_eq!(retry.generation, failed.generation);
    assert_eq!(retry.kind, ActionKind::Cleanup);
    assert!(retry.action > failed.action);
    let pending_retry = snapshot(&driver, &ids);
    assert_eq!(driver.retry_cleanup(consumer), Err(Error::InvalidState));
    assert!(driver
        .complete_cleanup(&failed, CleanupOutcome::Succeeded)
        .is_err());
    assert_eq!(snapshot(&driver, &ids), pending_retry);
    let mut forged = Vec::new();
    let mut wrong_domain = retry.clone();
    wrong_domain.domain = LifecycleDriver::new().unwrap().domain();
    forged.push(wrong_domain);
    let mut wrong_generation = retry.clone();
    wrong_generation.generation += 1;
    forged.push(wrong_generation);
    let mut wrong_action = retry.clone();
    wrong_action.action += 1;
    forged.push(wrong_action);
    let mut wrong_owner = retry.clone();
    wrong_owner.id = provider;
    forged.push(wrong_owner);
    let mut wrong_kind = retry.clone();
    wrong_kind.kind = ActionKind::Setup;
    forged.push(wrong_kind);
    for ticket in forged {
        assert!(driver
            .complete_cleanup(&ticket, CleanupOutcome::Succeeded)
            .is_err());
        assert_eq!(snapshot(&driver, &ids), pending_retry);
    }

    driver
        .complete_cleanup(&retry, CleanupOutcome::Succeeded)
        .unwrap();
    assert_eq!(driver.pending_action(consumer), None);
    assert_eq!(driver.committed(consumer), committed);
    let after_success = snapshot(&driver, &ids);
    assert_eq!(driver.retry_cleanup(consumer), Err(Error::InvalidState));
    assert!(driver
        .complete_cleanup(&retry, CleanupOutcome::Failed)
        .is_err());
    assert_eq!(snapshot(&driver, &ids), after_success);
    driver.finish_cleanup(consumer).unwrap();
    assert!(driver.committed(consumer).is_empty());
    assert_eq!(driver.phase(consumer), Some(Phase::Inactive));
    driver.remove(consumer).unwrap();
    driver.begin_cleanup(provider).unwrap();
    let cleanup = driver.pending_action(provider).unwrap().clone();
    driver
        .complete_cleanup(&cleanup, CleanupOutcome::Succeeded)
        .unwrap();
    driver.finish_cleanup(provider).unwrap();
    driver.remove(provider).unwrap();
}

#[test]
fn setup_completion_and_direct_finish_cannot_bypass_cleanup_results() {
    let mut driver = LifecycleDriver::new().unwrap();
    let id = driver.insert(None, vec![], vec![]).unwrap();
    driver.begin(id).unwrap();
    let setup = driver.pending_action(id).unwrap().clone();
    let before = snapshot(&driver, &[id]);
    assert!(driver
        .complete_cleanup(&setup, CleanupOutcome::Succeeded)
        .is_err());
    assert_eq!(snapshot(&driver, &[id]), before);
    driver.complete_action(&setup).unwrap();
    driver.retire(id).unwrap();
    driver.leave(id).unwrap();
    let unfinished = snapshot(&driver, &[id]);
    assert_eq!(driver.finish_cleanup(id), Err(Error::InvalidState));
    assert_eq!(driver.retry_cleanup(id), Err(Error::InvalidState));
    assert_eq!(snapshot(&driver, &[id]), unfinished);

    driver.begin_cleanup(id).unwrap();
    let cleanup = driver.pending_action(id).unwrap().clone();
    let pending = snapshot(&driver, &[id]);
    assert!(driver.complete_action(&cleanup).is_err());
    let mut forged_setup = cleanup.clone();
    forged_setup.kind = ActionKind::Setup;
    assert!(driver.complete_action(&forged_setup).is_err());
    assert!(driver.settle_setup(id).is_err());
    assert_eq!(driver.finish_cleanup(id), Err(Error::InvalidState));
    assert_eq!(driver.remove(id), Err(Error::InvalidState));
    assert_eq!(snapshot(&driver, &[id]), pending);
    driver
        .complete_cleanup(&cleanup, CleanupOutcome::Succeeded)
        .unwrap();
    driver.finish_cleanup(id).unwrap();
    assert_eq!(driver.finish_cleanup(id), Err(Error::InvalidState));
    driver.remove(id).unwrap();
}

#[test]
fn reservation_failure_requires_retry_and_explicit_finish_before_removal() {
    let mut driver = LifecycleDriver::new().unwrap();
    let id = driver.insert(None, vec![], vec![]).unwrap();
    driver.retire(id).unwrap();
    assert_eq!(driver.episode_generation(id), Some(0));
    assert_eq!(driver.retry_cleanup(id), Err(Error::InvalidState));
    assert_eq!(
        driver.finish_reservation_cleanup(id),
        Err(Error::InvalidState)
    );
    driver.begin_reservation_cleanup(id).unwrap();
    let failed = driver.pending_action(id).unwrap().clone();
    assert_eq!(failed.kind, ActionKind::Cleanup);
    assert_eq!(failed.generation, 0);
    let pending = snapshot(&driver, &[id]);
    assert!(driver.complete_action(&failed).is_err());
    assert_eq!(
        driver.finish_reservation_cleanup(id),
        Err(Error::InvalidState)
    );
    assert_eq!(driver.remove(id), Err(Error::InvalidState));
    assert_eq!(snapshot(&driver, &[id]), pending);
    driver
        .complete_cleanup(&failed, CleanupOutcome::Failed)
        .unwrap();
    assert_eq!(driver.pending_action(id), None);
    let after_failure = snapshot(&driver, &[id]);
    assert_eq!(
        driver.finish_reservation_cleanup(id),
        Err(Error::InvalidState)
    );
    assert_eq!(driver.finish_cleanup(id), Err(Error::InvalidState));
    assert_eq!(driver.remove(id), Err(Error::InvalidState));
    assert!(driver.begin_reservation_cleanup(id).is_err());
    assert_eq!(snapshot(&driver, &[id]), after_failure);

    let retry = driver.retry_cleanup(id).unwrap();
    assert_eq!(retry.generation, 0);
    assert!(retry.action > failed.action);
    let pending_retry = snapshot(&driver, &[id]);
    assert!(driver
        .complete_cleanup(&failed, CleanupOutcome::Succeeded)
        .is_err());
    assert_eq!(driver.retry_cleanup(id), Err(Error::InvalidState));
    assert_eq!(snapshot(&driver, &[id]), pending_retry);
    driver
        .complete_cleanup(&retry, CleanupOutcome::Succeeded)
        .unwrap();
    assert_eq!(driver.remove(id), Err(Error::InvalidState));
    assert_eq!(driver.finish_cleanup(id), Err(Error::InvalidState));
    driver.finish_reservation_cleanup(id).unwrap();
    assert_eq!(
        driver.finish_reservation_cleanup(id),
        Err(Error::InvalidState)
    );
    assert_eq!(driver.retry_cleanup(id), Err(Error::InvalidState));
    driver.remove(id).unwrap();
    assert_eq!(driver.phase(id), None);
}

#[test]
fn explicitly_drained_cleanup_can_finish_and_release_the_committed_provider() {
    let (mut driver, provider, consumer) = unloading_pair();
    let committed = driver.committed(consumer);
    driver.begin_cleanup(consumer).unwrap();
    let cleanup = driver.pending_action(consumer).unwrap().clone();
    driver
        .complete_cleanup(&cleanup, CleanupOutcome::Drained)
        .unwrap();
    assert_eq!(driver.committed(consumer), committed);
    assert_eq!(driver.begin_cleanup(provider), Err(Error::Relied));
    driver.finish_cleanup(consumer).unwrap();
    assert!(driver.committed(consumer).is_empty());
    driver.remove(consumer).unwrap();
    driver.begin_cleanup(provider).unwrap();
    let cleanup = driver.pending_action(provider).unwrap().clone();
    driver
        .complete_cleanup(&cleanup, CleanupOutcome::Drained)
        .unwrap();
    driver.finish_cleanup(provider).unwrap();
    driver.remove(provider).unwrap();
}
