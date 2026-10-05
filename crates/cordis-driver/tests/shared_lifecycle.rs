use cordis_driver::shared::{Decision, HostStatus, LifecycleDriver};
use cordis_driver::ActionKind;
use cordis_kernel::{Error, Port};

fn ready() -> HostStatus {
    HostStatus {
        available: true,
        failed: false,
        restart: false,
    }
}

#[test]
fn withdrawal_keeps_action_ownership_until_the_inflight_result_lands() {
    let mut driver = LifecycleDriver::new().unwrap();
    let id = driver.insert(None, vec![], vec![]).unwrap();
    assert_eq!(driver.decision(id, ready()), Some(Decision::Begin));
    driver.begin(id).unwrap();
    let setup = driver.pending_action(id).unwrap().clone();
    driver.retire(id).unwrap();
    assert_eq!(driver.decision(id, ready()), Some(Decision::Withdraw));
    driver.leave(id).unwrap();
    assert_eq!(driver.begin_cleanup(id), Err(Error::Relied));
    assert_eq!(driver.pending_action(id), Some(&setup));
    let mut forged = setup.clone();
    forged.generation += 1;
    assert_eq!(
        driver.complete_action(&forged).unwrap_err().code,
        "StaleAction"
    );
    driver.complete_action(&setup).unwrap();
    assert_eq!(
        driver.complete_action(&setup).unwrap_err().code,
        "StaleAction"
    );
    driver.begin_cleanup(id).unwrap();
    let cleanup = driver.pending_action(id).unwrap().clone();
    assert_eq!(cleanup.kind, ActionKind::Cleanup);
    assert_eq!(cleanup.generation, setup.generation);
    assert!(cleanup.action > setup.action);
    assert_eq!(driver.finish_cleanup(id), Err(Error::InvalidState));
    driver.complete_action(&cleanup).unwrap();
    driver.finish_cleanup(id).unwrap();
    driver.remove(id).unwrap();
    assert_eq!(
        driver.complete_action(&cleanup).unwrap_err().code,
        "StaleAction"
    );
}

#[test]
fn common_cleanup_arbitration_waits_for_consumer_setup_and_inverse() {
    let mut driver = LifecycleDriver::new().unwrap();
    let port = Port { key: 1, realm: 0 };
    let provider = driver.insert(None, vec![], vec![port]).unwrap();
    let consumer = driver.insert(None, vec![port], vec![]).unwrap();
    driver.begin(provider).unwrap();
    driver.settle_setup(provider).unwrap();
    driver.finish(provider).unwrap();
    driver.begin(consumer).unwrap();
    let setup = driver.pending_action(consumer).unwrap().clone();
    driver.retire(provider).unwrap();
    driver.leave(provider).unwrap();
    driver.leave(consumer).unwrap();
    assert_eq!(driver.begin_cleanup(provider), Err(Error::Relied));
    assert_eq!(driver.begin_cleanup(consumer), Err(Error::Relied));
    driver.complete_action(&setup).unwrap();
    driver.begin_cleanup(consumer).unwrap();
    let cleanup = driver.pending_action(consumer).unwrap().clone();
    assert_eq!(driver.begin_cleanup(provider), Err(Error::Relied));
    driver.complete_action(&cleanup).unwrap();
    driver.finish_cleanup(consumer).unwrap();
    driver.begin_cleanup(provider).unwrap();
}

#[test]
fn action_domains_and_retry_attempts_cannot_acknowledge_each_other() {
    let mut first = LifecycleDriver::new().unwrap();
    let mut second = LifecycleDriver::new().unwrap();
    let id = first.insert(None, vec![], vec![]).unwrap();
    let other = second.insert(None, vec![], vec![]).unwrap();
    first.begin(id).unwrap();
    second.begin(other).unwrap();
    let foreign = second.pending_action(other).unwrap().clone();
    assert_eq!(
        first.complete_action(&foreign).unwrap_err().code,
        "WrongDomain"
    );
    first.settle_setup(id).unwrap();
    first.leave(id).unwrap();
    first.begin_cleanup(id).unwrap();
    let failed = first.pending_action(id).unwrap().clone();
    first.complete_action(&failed).unwrap();
    let retry = first.retry_cleanup(id).unwrap();
    assert!(retry.action > failed.action);
    assert_eq!(
        first.complete_action(&failed).unwrap_err().code,
        "StaleAction"
    );
    assert_eq!(first.pending_action(id), Some(&retry));
}

#[test]
fn retiring_child_blocks_new_parent_episode_until_registry_removal() {
    let mut driver = LifecycleDriver::new().unwrap();
    let parent = driver.insert(None, vec![], vec![]).unwrap();
    let child = driver.insert(Some(parent), vec![], vec![]).unwrap();
    driver.retire(child).unwrap();
    assert_eq!(driver.decision(parent, ready()), None);
    assert_eq!(driver.decision(child, ready()), Some(Decision::Remove));
    driver.remove(child).unwrap();
    assert_eq!(driver.decision(parent, ready()), Some(Decision::Begin));
}
