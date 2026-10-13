use cordis_kernel::cleanup_groups::CleanupGroups;
use cordis_kernel::cleanup_journal::RestoreOutcome;
use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
use cordis_kernel::lifecycle_actions::CleanupOutcome;
use cordis_kernel::lifecycle_state::LifecycleState;
use cordis_kernel::setup_work::SetupWork;
use cordis_kernel::{Error, Phase, Port};

type Work = SetupWork<String, String>;
type Groups = CleanupGroups<String>;

fn settle_root(work: &mut Work) {
    let item = work
        .issue_root(String::from("actual setup input"))
        .ok()
        .unwrap();
    let reply = item.run(|input| {
        assert_eq!(input, "actual setup input");
        Ok::<(), String>(())
    });
    assert!(work.complete_root(reply).ok().unwrap().is_ok());
}
fn begin(state: &mut LifecycleState, id: usize, domain: u64) -> (Work, Groups) {
    let (mut work, groups) = state.begin_execution(id, domain).unwrap();
    settle_root(&mut work);
    (work, groups)
}
fn withdraw(state: &mut LifecycleState, id: usize, work: &mut Work, groups: &Groups) {
    state.leave(id).unwrap();
    work.withdraw();
    state.settle_execution(id, work, groups).unwrap();
    state.begin_cleanup(id).unwrap();
}
fn complete(groups: &mut Groups, group: usize, result: Result<(), &str>, retry: Option<String>) {
    let (ticket, _) = groups.pop(group).unwrap().unwrap();
    let report = groups
        .complete_result(group, ticket, result, retry, CleanupPolicy::DrainConsumed)
        .ok()
        .unwrap();
    assert_eq!(report.result, result);
}

#[test]
fn unbound_foreign_owner_domain_and_old_generation_cannot_drive_lifecycle() {
    let mut state = LifecycleState::new(100);
    let a = state.insert(None, vec![], vec![]).unwrap();
    let b = state.insert(None, vec![], vec![]).unwrap();
    let (mut work, mut groups) = begin(&mut state, a, 101);
    let (other_work, other_groups) = begin(&mut state, b, 102);
    let ticket = state.pending(a);
    assert_eq!(
        state.finish_execution(a, &other_work, &other_groups),
        Err(Error::InvalidState)
    );
    assert_eq!(state.pending(a), ticket);
    let mut unbound = Work::new(101);
    settle_root(&mut unbound);
    assert_eq!(
        state.finish_execution(a, &unbound, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(
        state.finish_execution(a, &work, &other_groups),
        Err(Error::InvalidState)
    );
    // Matching numeric cleanup domains alone cannot substitute an empty owner.
    let forged_empty = Groups::new(101);
    assert_eq!(
        state.finish_execution(a, &work, &forged_empty),
        Err(Error::InvalidState)
    );
    let mut foreign = LifecycleState::new(200);
    assert_eq!(foreign.insert(None, vec![], vec![]).unwrap(), a);
    let _ = begin(&mut foreign, a, 103);
    assert_eq!(
        foreign.finish_execution(a, &work, &groups),
        Err(Error::InvalidState)
    );

    state.finish_execution(a, &work, &groups).unwrap();
    withdraw(&mut state, a, &mut work, &groups);
    assert_eq!(
        state.release_execution(a, &mut work, &mut groups),
        Ok(CleanupOutcome::Succeeded)
    );
    let (new_work, new_groups) = begin(&mut state, a, 104);
    let current = state.pending(a);
    assert_eq!(
        state.settle_execution(a, &work, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(
        state.release_execution(a, &mut work, &mut groups),
        Err(Error::InvalidState)
    );
    assert_eq!(state.pending(a), current);
    state.finish_execution(a, &new_work, &new_groups).unwrap();
}

#[test]
fn real_dispatched_work_and_pending_stages_block_setup_acknowledgement() {
    let mut state = LifecycleState::new(201);
    let id = state.insert(None, vec![], vec![]).unwrap();
    let (mut work, mut groups) = begin(&mut state, id, 202);
    work.enqueue_child("queued child".into()).unwrap();
    let item = work.take_child().unwrap();
    let ticket = state.pending(id);
    assert_eq!(work.child_count(), 0);
    assert_eq!(
        state.settle_execution(id, &work, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(
        state.finish_execution(id, &work, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(state.pending(id), ticket);
    let receipt = item.run(|s| {
        assert_eq!(s, "queued child");
        s
    });
    assert_eq!(work.complete_request(receipt).ok().unwrap(), "queued child");
    let group = groups.add_iterator(203, vec![]).unwrap();
    assert!(groups.admit(group, Some(&[])));
    assert_eq!(
        state.settle_execution(id, &work, &groups),
        Err(Error::InvalidState)
    );
    assert!(groups.land_result::<String>(group, Ok(None)).is_ok());
    state.finish_execution(id, &work, &groups).unwrap();
    assert_eq!(state.kernel().phase(id), Some(Phase::Active));
}

#[test]
fn removed_groups_do_not_erase_consumed_failure_and_next_episode_starts_clean() {
    let mut state = LifecycleState::new(301);
    let id = state.insert(None, vec![], vec![]).unwrap();
    let (mut work, mut groups) = begin(&mut state, id, 302);
    state.finish_execution(id, &work, &groups).unwrap();
    let group = groups.add_iterator(303, vec![]).unwrap();
    groups.register(group, "consumed inverse".into()).unwrap();
    groups.cancel(group);
    complete(&mut groups, group, Err("one-shot failure"), None);
    assert!(groups.has_consumed_failure());
    assert!(groups.remove(group));
    assert!(groups.has_consumed_failure());
    withdraw(&mut state, id, &mut work, &groups);
    assert_eq!(
        state.release_execution(id, &mut work, &mut groups),
        Ok(CleanupOutcome::Drained)
    );
    assert!(groups.is_empty());
    assert!(groups.has_consumed_failure());
    assert!(work.enqueue_child("late".into()).is_err());
    let (mut work, mut groups) = begin(&mut state, id, 304);
    assert!(!groups.has_consumed_failure());
    state.finish_execution(id, &work, &groups).unwrap();
    withdraw(&mut state, id, &mut work, &groups);
    assert_eq!(
        state.release_execution(id, &mut work, &mut groups),
        Ok(CleanupOutcome::Succeeded)
    );
}

#[test]
fn release_waits_for_real_receipts_and_failed_cleanup_retains_provider_commitments() {
    let mut state = LifecycleState::new(401);
    let port = Port { key: 7, realm: 0 };
    let provider = state.insert(None, vec![], vec![port]).unwrap();
    let (provider_work, provider_groups) = begin(&mut state, provider, 402);
    state
        .finish_execution(provider, &provider_work, &provider_groups)
        .unwrap();
    let consumer = state.insert(None, vec![port], vec![]).unwrap();
    let (mut work, mut groups) = begin(&mut state, consumer, 403);
    state.finish_execution(consumer, &work, &groups).unwrap();
    let bindings = state.kernel().committed(consumer);
    groups.register(0, "retryable inverse".into()).unwrap();
    withdraw(&mut state, consumer, &mut work, &groups);
    let action = state.pending(consumer).unwrap();
    let (first, value) = groups.pop(0).unwrap().unwrap();
    assert_eq!(
        state.release_execution(consumer, &mut work, &mut groups),
        Err(Error::InvalidState)
    );
    assert_eq!(state.pending(consumer), Some(action));
    let report = groups
        .complete_result(
            0,
            first,
            Err("retry me"),
            Some(value),
            CleanupPolicy::DrainConsumed,
        )
        .ok()
        .unwrap();
    assert_eq!(report.outcome, RestoreOutcome::Failed);
    state.fail_execution(consumer, &work, &groups).unwrap();
    assert_eq!(state.kernel().committed(consumer), bindings);
    state.leave(provider).unwrap();
    assert_eq!(state.begin_cleanup(provider), Err(Error::Relied));
    assert_eq!(
        state.release_execution(consumer, &mut work, &mut groups),
        Err(Error::InvalidState)
    );
    let next = state.retry_execution(consumer, &work, &mut groups).unwrap();
    assert!(next.action > action.action);
    let (second, _) = groups.pop(0).unwrap().unwrap();
    assert_ne!(first.attempt, second.attempt);
    assert!(groups
        .complete_result(
            0,
            first,
            Ok::<(), &str>(()),
            None,
            CleanupPolicy::DrainConsumed
        )
        .is_err());
    assert_eq!(
        state.release_execution(consumer, &mut work, &mut groups),
        Err(Error::InvalidState)
    );
    assert!(groups
        .complete_result(
            0,
            second,
            Ok::<(), &str>(()),
            None,
            CleanupPolicy::DrainConsumed
        )
        .is_ok());
    assert_eq!(
        state.release_execution(consumer, &mut work, &mut groups),
        Ok(CleanupOutcome::Succeeded)
    );
    assert!(state.kernel().committed(consumer).is_empty());
    assert!(state.begin_cleanup(provider).is_ok());
}

#[test]
fn nonretryable_retained_failure_cannot_partially_advance_other_groups_or_lifecycle() {
    let mut state = LifecycleState::new(501);
    let id = state.insert(None, vec![], vec![]).unwrap();
    let (mut work, mut groups) = begin(&mut state, id, 502);
    state.finish_execution(id, &work, &groups).unwrap();
    groups.register(0, "retryable".into()).unwrap();
    let other = groups.add_iterator(503, vec![]).unwrap();
    groups
        .register(other, "consumed but retained".into())
        .unwrap();
    groups.cancel(other);
    withdraw(&mut state, id, &mut work, &groups);
    complete(&mut groups, 0, Err("retryable"), Some("again".into()));
    let (ticket, _) = groups.pop(other).unwrap().unwrap();
    assert!(groups
        .complete_result(
            other,
            ticket,
            Err("lost once"),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_ok());
    state.fail_execution(id, &work, &groups).unwrap();
    assert!(groups.get(0).unwrap().can_retry());
    assert_eq!(
        state.retry_execution(id, &work, &mut groups),
        Err(Error::InvalidState)
    );
    assert_eq!(state.pending(id), None);
    assert!(groups.get(0).unwrap().can_retry());
    assert!(groups.get(0).unwrap().has_failed());
    assert!(groups.get(other).unwrap().has_failed());
    assert!(!groups.has_consumed_failure());
}

#[test]
fn rejected_foreign_result_cannot_taint_a_successful_episode() {
    let mut state = LifecycleState::new(601);
    let id = state.insert(None, vec![], vec![]).unwrap();
    let (mut work, mut groups) = begin(&mut state, id, 602);
    state.finish_execution(id, &work, &groups).unwrap();
    let mut other = Groups::new(603);
    other.register(0, "foreign".into()).unwrap();
    let (ticket, _) = other.pop(0).unwrap().unwrap();
    let result = groups.complete_result(
        0,
        ticket,
        Err("foreign failed"),
        None,
        CleanupPolicy::DrainConsumed,
    );
    assert!(result.is_err());
    assert!(!groups.has_consumed_failure());
    withdraw(&mut state, id, &mut work, &groups);
    assert_eq!(
        state.release_execution(id, &mut work, &mut groups),
        Ok(CleanupOutcome::Succeeded)
    );
}
