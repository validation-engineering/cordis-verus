//! Cross-owner behavior of the production Node protocol, including failed cleanup.
use cordis_kernel::availability::CheckError;
use cordis_kernel::lifecycle_actions::CleanupOutcome;
use cordis_kernel::lifecycle_state::cleanup::CleanupCommand as C;
use cordis_kernel::node_runtime::NodeRuntime;
use cordis_kernel::{Phase, Port};

const PORT: Port = Port { key: 37, realm: 2 };

#[test]
fn version_history_and_failed_cleanup_keep_the_actual_committed_resources() {
    let mut core = NodeRuntime::new(77);
    let provider = core.insert(None, vec![], vec![PORT]).unwrap();
    let consumer = core.insert(None, vec![PORT], vec![]).unwrap();
    let provider_admission = core.begin(provider).unwrap();
    let publication = core
        .publish(provider, 1, PORT, 10)
        .map_err(|e| e.error)
        .unwrap();
    core.cleanup(C::SettleSetup {
        ticket: provider_admission,
    })
    .unwrap();
    core.finish(provider).unwrap();
    core.set_checked(publication.0, true);
    let old = core.request_check(consumer, PORT).unwrap().unwrap();
    for value in [11, 10] {
        core.replace(publication, provider, 1, value)
            .map_err(|e| e.error)
            .unwrap();
    }
    assert_eq!(core.store().observation(publication), Some((2, &10)));
    assert!(!core.current_check(old.ticket));
    assert_eq!(core.complete_check(old.ticket, true), Ok(false));
    assert_eq!(
        core.complete_check(old.ticket, true),
        Err(CheckError::Stale)
    );
    assert!(!core.ready(consumer));
    core.notify(&[PORT]).unwrap();
    let fresh = core.request_check(consumer, PORT).unwrap().unwrap();
    assert_eq!(fresh.value, old.value);
    assert_eq!(fresh.ticket.value_revision, 2);
    assert_eq!(core.complete_check(fresh.ticket, true), Ok(true));
    let admitted = core.begin(consumer).unwrap();
    let binding = core.admission(consumer).unwrap().resources()[0];
    assert_eq!(binding.publication, publication);
    core.cleanup(C::SettleSetup { ticket: admitted }).unwrap();
    core.finish(consumer).unwrap();
    let committed = core.state().kernel().committed(consumer);
    assert_eq!(committed[0].provider, provider);
    core.replace(publication, provider, 1, 12)
        .map_err(|e| e.error)
        .unwrap();
    assert_eq!(
        core.store().leased_observation(binding.lease),
        Ok((publication, 3, &12))
    );
    assert_eq!(core.state().kernel().committed(consumer), committed);

    core.cleanup(C::Withdraw { id: provider }).unwrap();
    core.revoke(publication).unwrap();
    core.cleanup(C::Withdraw { id: consumer }).unwrap();
    assert!(core
        .cleanup(C::Request {
            id: provider,
            reservation: false
        })
        .is_err());
    let failed = core
        .cleanup(C::Request {
            id: consumer,
            reservation: false,
        })
        .unwrap()
        .unwrap();
    core.cleanup(C::Report {
        ticket: failed,
        outcome: CleanupOutcome::Failed,
    })
    .unwrap();
    assert!(core.release(consumer, &[]).is_err());
    // Only replaced handles are deliverable while cleanup still retains 12.
    assert_eq!(core.drain_released(), vec![10, 11, 10]);
    assert!(core.drain_released().is_empty());
    assert_eq!(
        core.store().leased_observation(binding.lease),
        Ok((publication, 3, &12))
    );
    assert_eq!(core.state().kernel().committed(consumer), committed);
    let retry = core.cleanup(C::Retry { id: consumer }).unwrap().unwrap();
    assert_ne!(retry.action, failed.action);
    assert!(core
        .cleanup(C::Report {
            ticket: failed,
            outcome: CleanupOutcome::Succeeded
        })
        .is_err());
    core.cleanup(C::Report {
        ticket: retry,
        outcome: CleanupOutcome::Succeeded,
    })
    .unwrap();
    // Raw lifecycle release must not bypass the retained admission's lease batch.
    assert!(core
        .cleanup(C::Release {
            id: consumer,
            reservation: false
        })
        .is_err());
    assert!(core.store().leased_observation(binding.lease).is_ok());
    assert!(core.release(consumer, &[]).unwrap().is_empty());
    assert_eq!(core.state().kernel().phase(consumer), Some(Phase::Inactive));
    assert!(core.store().leased_observation(binding.lease).is_err());

    let ticket = core
        .cleanup(C::Request {
            id: provider,
            reservation: false,
        })
        .unwrap()
        .unwrap();
    core.cleanup(C::Report {
        ticket,
        outcome: CleanupOutcome::Succeeded,
    })
    .unwrap();
    let released = core.release(provider, &[publication]).unwrap();
    assert_eq!(released.len(), 1);
    assert_eq!(
        (released[0].publication, released[0].value),
        (publication, 12)
    );
    assert_eq!(core.store().value(publication), None);
    assert_eq!(core.drain_released(), vec![12]);
    assert!(core.release(provider, &[publication]).is_err());
    assert!(core.drain_released().is_empty());
    assert_eq!(core.store().registry().lease_record_count(), 0);
    let _actual_history = core.snapshot();
}

#[test]
fn reservation_adoption_and_dynamic_interfaces_use_the_same_protocol_owner() {
    let mut core = NodeRuntime::new(78);
    let provider = core.insert(None, vec![], vec![]).unwrap();
    core.declare_provision(provider, PORT).unwrap();
    core.episode_command(cordis_kernel::node_runtime::episode::Command::Prepare { id: provider })
        .unwrap();
    let publication = core
        .publish(provider, 0, PORT, 20)
        .map_err(|e| e.error)
        .unwrap();
    assert!(core.resolve(PORT, None, None).unwrap().is_none());
    assert_eq!(
        core.resolve(PORT, Some(provider), Some(0))
            .unwrap()
            .unwrap()
            .publication,
        publication
    );
    let admission = core.begin(provider).unwrap();
    core.adopt(publication, provider, 1).unwrap();
    assert_eq!(
        core.resolve(PORT, Some(provider), Some(0)),
        Err(cordis_kernel::node_runtime::reads::ReadError::Stale)
    );
    assert_eq!(
        core.resolve(PORT, Some(provider), Some(1))
            .unwrap()
            .unwrap()
            .publication,
        publication
    );
    core.cleanup(C::SettleSetup { ticket: admission }).unwrap();
    core.finish(provider).unwrap();
    let consumer = core.insert(None, vec![], vec![]).unwrap();
    core.configure_pending_dependencies(consumer, vec![PORT])
        .unwrap();
    core.begin(consumer).unwrap();
    assert_eq!(
        core.admission(consumer).unwrap().resources()[0].publication,
        publication
    );
    assert_eq!(
        core.store()
            .registry()
            .entry(publication)
            .unwrap()
            .generation,
        1
    );
    assert!(core
        .configure_pending_dependencies(consumer, vec![])
        .is_err());
    assert!(core.release_provision(provider, PORT).is_err());
    assert_eq!(
        core.state().kernel().committed(consumer)[0].provider,
        provider
    );
}

#[test]
fn retained_admission_survives_failure_restart_retry_and_rejects_late_errors() {
    use cordis_kernel::node_runtime::episode::{Command as E, EpisodeError};
    let mut core = NodeRuntime::new(79);
    let provider = core.insert(None, vec![], vec![PORT]).unwrap();
    let setup = core.begin(provider).unwrap();
    let publication = core
        .publish(provider, 1, PORT, 91)
        .map_err(|e| e.error)
        .unwrap();
    core.complete(setup, None).unwrap();
    core.finish(provider).unwrap();
    let consumer = core.insert(None, vec![PORT], vec![]).unwrap();
    let setup = core.begin(consumer).unwrap();
    let binding = core.admission(consumer).unwrap().resources()[0];
    core.episode_command(E::Fail {
        id: consumer,
        generation: 1,
        error: "child failed".into(),
    })
    .unwrap();
    core.episode_command(E::Fail {
        id: consumer,
        generation: 1,
        error: "later failure".into(),
    })
    .unwrap();
    assert_eq!(
        core.episode(consumer).unwrap().failed.as_deref(),
        Some("child failed")
    );
    core.episode_command(E::Restart { id: consumer }).unwrap();
    assert!(core.episode(consumer).unwrap().restart);
    core.complete(setup, None).unwrap();
    assert!(core.finish(consumer).is_err());
    assert!(core.begin(consumer).is_err());
    assert_eq!(core.admission(consumer).unwrap().ticket(), setup);
    core.cleanup(C::Withdraw { id: consumer }).unwrap();
    let failed = core
        .cleanup(C::Request {
            id: consumer,
            reservation: false,
        })
        .unwrap()
        .unwrap();
    core.complete(failed, Some("inverse failed".into()))
        .unwrap();
    assert!(core.episode(consumer).unwrap().cleanup_failed);
    assert_eq!(
        core.episode_command(E::NotifyRetry { id: consumer }),
        Err(EpisodeError::Closed)
    );
    assert!(core.release(consumer, &[]).is_err());
    assert_eq!(core.admission(consumer).unwrap().resources(), &[binding]);
    assert_eq!(
        core.store().leased_value(binding.lease),
        Ok((publication, &91))
    );
    let retry = core.cleanup(C::Retry { id: consumer }).unwrap().unwrap();
    assert!(!core.episode(consumer).unwrap().cleanup_failed);
    assert!(core
        .complete(failed, Some("late failed reply".into()))
        .is_err());
    assert_eq!(
        core.episode(consumer).unwrap().failed.as_deref(),
        Some("inverse failed")
    );
    assert_eq!(core.state().pending(consumer), Some(retry));
    assert_eq!(core.admission(consumer).unwrap().ticket(), setup);
    core.complete(retry, None).unwrap();
    core.release(consumer, &[]).unwrap();
    assert!(core.admission(consumer).is_none());
    assert!(!core.episode(consumer).unwrap().restart);
    // A successful inverse does not silently retry a failed setup.
    assert!(core.begin(consumer).is_err());
    core.episode_command(E::Restart { id: consumer }).unwrap();
    let next = core.begin(consumer).unwrap();
    assert!(next.generation > setup.generation);
    assert!(core.complete(setup, Some("old setup".into())).is_err());
    assert!(core.episode(consumer).unwrap().failed.is_none());
    assert_eq!(core.admission(consumer).unwrap().ticket(), next);
    assert_eq!(
        core.episode_command(E::Fail {
            id: consumer,
            generation: setup.generation,
            error: "old failure".into()
        }),
        Err(EpisodeError::Stale)
    );
    core.complete(next, None).unwrap();
    core.finish(consumer).unwrap();
    let _history = core.snapshot();
}

#[test]
fn prepared_owner_requires_its_successful_cleanup_and_complete_manifest_before_removal() {
    use cordis_kernel::node_runtime::episode::Command as E;
    let mut core = NodeRuntime::new(80);
    let id = core.insert(None, vec![], vec![PORT]).unwrap();
    core.episode_command(E::Seal { id, sealed: false }).unwrap();
    assert!(core.begin(id).is_err());
    assert!(core.validate(id, 0).is_err());
    assert!(core.publish(id, 0, PORT, 80).is_err());
    assert_eq!(core.store().retained_count(), 0);
    core.episode_command(E::Prepare { id }).unwrap();
    core.validate(id, 0).unwrap();
    let publication = core.publish(id, 0, PORT, 81).map_err(|e| e.error).unwrap();
    core.cleanup(C::Retire { id }).unwrap();
    assert!(core.validate(id, 0).is_err());
    assert!(core.cleanup(C::Remove { id }).is_err());
    let failed = core
        .cleanup(C::Request {
            id,
            reservation: true,
        })
        .unwrap()
        .unwrap();
    core.revoke(publication).unwrap();
    core.complete(failed, Some("reservation inverse".into()))
        .unwrap();
    assert!(core.episode(id).unwrap().prepared_cleanup);
    assert!(core.admission(id).is_none());
    assert!(core.release_reservation(id, &[publication]).is_err());
    let retry = core.cleanup(C::Retry { id }).unwrap().unwrap();
    core.complete(retry, None).unwrap();
    assert!(core.release_reservation(id, &[]).is_err());
    assert!(core.episode(id).unwrap().prepared);
    assert_eq!(core.store().value(publication), Some(&81));
    assert!(core.complete(failed, Some("stale".into())).is_err());
    assert_eq!(
        core.episode(id).unwrap().failed.as_deref(),
        Some("reservation inverse")
    );
    let released = core.release_reservation(id, &[publication]).unwrap();
    assert_eq!(released[0].value, 81);
    assert!(!core.episode(id).unwrap().prepared);
    assert!(!core.episode(id).unwrap().prepared_cleanup);
    assert!(core.episode(id).unwrap().failed.is_none());
    core.cleanup(C::Remove { id }).unwrap();
    assert!(core.episode(id).is_none());
}

#[test]
fn callback_scopes_survive_adoption_and_cleanup_but_never_gain_new_episode_authority() {
    use cordis_kernel::invocation_ledger::{ScopeError, ScopeHandle};
    use cordis_kernel::node_runtime::episode::Command as E;
    let mut core = NodeRuntime::new(83);
    let owner = core.insert(None, vec![], vec![PORT]).unwrap();
    core.episode_command(E::Prepare { id: owner }).unwrap();
    let prepared = core.begin_scope(owner, 0).unwrap();
    let publication = core
        .publish(owner, 0, PORT, 31)
        .map_err(|e| e.error)
        .unwrap();
    let setup = core.begin(owner).unwrap();
    core.adopt(publication, owner, setup.generation).unwrap();
    assert_eq!(
        core.check_scope_wait(&[prepared], owner),
        Err(ScopeError::StaleEpisode)
    );
    core.finish_scope(prepared).unwrap();
    let live = core.begin_scope(owner, setup.generation).unwrap();
    let sibling = core.begin_scope(owner, setup.generation).unwrap();
    core.complete(setup, None).unwrap();
    core.finish(owner).unwrap();
    let child = core.insert(Some(owner), vec![], vec![]).unwrap();
    let child_setup = core.begin(child).unwrap();
    let nested = core.begin_scope(child, child_setup.generation).unwrap();
    let blocked = core
        .check_scope_wait(&[nested, live], owner)
        .unwrap()
        .unwrap();
    assert_eq!(
        (blocked.scope, blocked.id, blocked.retained),
        (nested, child, child)
    );
    core.finish_scope(nested).unwrap();
    core.complete(child_setup, None).unwrap();
    core.finish(child).unwrap();
    core.cleanup(C::Withdraw { id: child }).unwrap();
    let child_cleanup = core
        .cleanup(C::Request {
            id: child,
            reservation: false,
        })
        .unwrap()
        .unwrap();
    core.complete(child_cleanup, None).unwrap();
    core.release_owned(child).unwrap();
    assert_eq!(
        core.check_scope_wait(&[nested, live], owner)
            .unwrap()
            .unwrap()
            .scope,
        live
    );
    assert_eq!(core.scopes_live(&[prepared, sibling]), Ok(true));
    assert_eq!(
        core.scopes_live(&[live, ScopeHandle { domain: 84, ..live }]),
        Err(ScopeError::WrongDomain)
    );
    core.cleanup(C::Withdraw { id: owner }).unwrap();
    core.withdraw_publications(owner).unwrap();
    let cleanup = core
        .cleanup(C::Request {
            id: owner,
            reservation: false,
        })
        .unwrap()
        .unwrap();
    core.complete(cleanup, Some("inverse failed".into()))
        .unwrap();
    assert!(core.release_owned(owner).is_err());
    assert_eq!(core.scopes_live(&[live, sibling]), Ok(true));
    let retry = core.cleanup(C::Retry { id: owner }).unwrap().unwrap();
    core.complete(retry, None).unwrap();
    assert_eq!(
        core.release_owned(owner).unwrap()[0].publication,
        publication
    );
    core.episode_command(E::Restart { id: owner }).unwrap();
    let next_setup = core.begin(owner).unwrap();
    assert!(next_setup.generation > setup.generation);
    let next = core.begin_scope(owner, next_setup.generation).unwrap();
    assert!(next.scope > sibling.scope);
    assert_eq!(
        core.check_scope_wait(&[live], owner),
        Err(ScopeError::StaleEpisode)
    );
    core.finish_scope(live).unwrap();
    assert_eq!(core.finish_scope(live), Err(ScopeError::Completed));
    assert_eq!(core.scopes_live(&[prepared, live, nested, next]), Ok(true));
    core.finish_scope(sibling).unwrap();
    core.finish_scope(next).unwrap();
    assert_eq!(core.invocation_count(), 0);
    let _actual_history = core.snapshot();
}

#[test]
fn actual_release_manifest_keeps_withdrawn_versions_and_excludes_reclaimed_or_foreign_slots() {
    let mut core = NodeRuntime::new(85);
    let extra = Port { key: 38, realm: 2 };
    let foreign_port = Port { key: 39, realm: 2 };
    let owner = core.insert(None, vec![], vec![PORT]).unwrap();
    let other = core.insert(None, vec![], vec![foreign_port]).unwrap();
    let setup = core.begin(owner).unwrap();
    let old = core
        .publish(owner, 1, PORT, 10)
        .map_err(|e| e.error)
        .unwrap();
    core.revoke(old).unwrap();
    let current = core
        .publish(owner, 1, PORT, 11)
        .map_err(|e| e.error)
        .unwrap();
    core.declare_provision(owner, extra).unwrap();
    let reclaimed = core
        .publish(owner, 1, extra, 12)
        .map_err(|e| e.error)
        .unwrap();
    core.revoke(reclaimed).unwrap();
    assert_eq!(core.reclaim(reclaimed), Ok(12));
    let other_setup = core.begin(other).unwrap();
    let foreign = core
        .publish(other, 1, foreign_port, 13)
        .map_err(|e| e.error)
        .unwrap();
    core.complete(other_setup, None).unwrap();
    core.finish(other).unwrap();
    assert_eq!(core.publications(owner), vec![old, current]);
    core.complete(setup, None).unwrap();
    core.finish(owner).unwrap();
    core.cleanup(C::Withdraw { id: owner }).unwrap();
    core.withdraw_publications(owner).unwrap();
    assert_eq!(core.restoring_publications(owner).unwrap(), &[current]);
    assert_eq!(core.store().value(current), Some(&11));
    let cleanup = core
        .cleanup(C::Request {
            id: owner,
            reservation: false,
        })
        .unwrap()
        .unwrap();
    core.complete(cleanup, Some("cleanup failed".into()))
        .unwrap();
    assert!(core.release_owned(owner).is_err());
    assert_eq!(core.drain_released(), vec![12]);
    assert!(core.drain_released().is_empty());
    assert_eq!(core.publications(owner), vec![old, current]);
    assert_eq!(core.restoring_publications(owner).unwrap(), &[current]);
    // Explicit revocation during cleanup removes fallback visibility; it does
    // not remove the retained slot from the release manifest.
    core.revoke(current).unwrap();
    assert!(core.restoring_publications(owner).unwrap().is_empty());
    let retry = core.cleanup(C::Retry { id: owner }).unwrap().unwrap();
    assert!(core.complete(cleanup, None).is_err());
    core.complete(retry, None).unwrap();
    let released = core.release_owned(owner).unwrap();
    assert_eq!(
        released
            .iter()
            .map(|v| (v.publication, v.value))
            .collect::<Vec<_>>(),
        vec![(old, 10), (current, 11)]
    );
    assert!(core.publications(owner).is_empty());
    assert_eq!(core.drain_released(), vec![10, 11]);
    assert!(core.drain_released().is_empty());
    assert!(core.restoring_publications(owner).is_none());
    assert_eq!(core.publications(other), vec![foreign]);
    assert_eq!(core.store().value(foreign), Some(&13));
    assert_eq!(core.store().value(reclaimed), None);
    let _actual_history = core.snapshot();
}

#[test]
fn delivery_rechecks_shared_withdrawn_handles_and_consumes_each_batch_once() {
    let mut core = NodeRuntime::new(84);
    let other = Port { key: 38, realm: 2 };
    let owner = core.insert(None, vec![], vec![PORT, other]).unwrap();
    let setup = core.begin(owner).unwrap();
    let first = core
        .publish(owner, 1, PORT, u64::MAX)
        .map_err(|e| e.error)
        .unwrap();
    let second = core
        .publish(owner, 1, other, u64::MAX)
        .map_err(|e| e.error)
        .unwrap();
    core.complete(setup, None).unwrap();
    core.finish(owner).unwrap();
    core.replace(first, owner, 1, 20)
        .map_err(|e| e.error)
        .unwrap();
    core.revoke(second).unwrap();
    // Visibility is insufficient: the withdrawn slot still retains the handle.
    assert!(core.drain_released().is_empty());
    assert_eq!(core.store().value(second), Some(&u64::MAX));
    assert_eq!(core.reclaim(second), Ok(u64::MAX));
    assert_eq!(core.drain_released(), vec![u64::MAX]);
    assert!(core.reclaim(second).is_err());
    assert!(core.drain_released().is_empty());
    for value in [21, 20, 20] {
        core.replace(first, owner, 1, value)
            .map_err(|e| e.error)
            .unwrap();
    }
    assert_eq!(core.drain_released(), vec![21]);
    assert_eq!(core.store().value(first), Some(&20));
    assert!(core.replace(first, owner, 0, 22).is_err());
    assert!(core.publish(owner, 1, PORT, 23).is_err());
    assert!(core.drain_released().is_empty());
    let _actual_history = core.snapshot();
}

#[test]
fn reads_keep_the_committed_slot_and_own_cleanup_view_until_successful_release() {
    use cordis_kernel::node_runtime::reads::{ReadError, Source};
    let mut core = NodeRuntime::new(85);
    let provider = core.insert(None, vec![], vec![PORT]).unwrap();
    let started = core.begin(provider).unwrap();
    let old = core
        .publish(provider, 1, PORT, 100)
        .map_err(|e| e.error)
        .unwrap();
    // Own reads work during setup, while unowned reads require an active owner.
    assert_eq!(core.resolve(PORT, None, None), Ok(None));
    assert_eq!(
        core.resolve(PORT, Some(provider), Some(1))
            .unwrap()
            .unwrap()
            .source,
        Source::Own
    );
    core.complete(started, None).unwrap();
    core.finish(provider).unwrap();
    let consumer = core.insert(Some(provider), vec![PORT], vec![]).unwrap();
    let started = core.begin(consumer).unwrap();
    core.complete(started, None).unwrap();
    core.finish(consumer).unwrap();
    core.replace(old, provider, 1, 101)
        .map_err(|e| e.error)
        .unwrap();
    core.revoke(old).unwrap();
    let new = core
        .publish(provider, 1, PORT, 200)
        .map_err(|e| e.error)
        .unwrap();
    let root = core.resolve(PORT, None, None).unwrap().unwrap();
    assert_eq!(
        (root.publication, root.value, root.source),
        (new, 200, Source::Root)
    );
    let bound = core
        .resolve(PORT, Some(consumer), Some(1))
        .unwrap()
        .unwrap();
    assert_eq!(
        (bound.publication, bound.value, bound.revision, bound.source),
        (old, 101, 1, Source::Committed { binding: 0 })
    );
    core.compact_bindings();
    core.compact_declarations();
    core.cleanup(C::Withdraw { id: provider }).unwrap();
    core.withdraw_publications(provider).unwrap();
    core.cleanup(C::Withdraw { id: consumer }).unwrap();
    assert_eq!(core.resolve(PORT, None, None), Ok(None));
    let saved = core
        .resolve(PORT, Some(provider), Some(1))
        .unwrap()
        .unwrap();
    assert_eq!(
        (saved.publication, saved.value, saved.source),
        (new, 200, Source::Restoring { index: 0 })
    );
    let failed = core
        .cleanup(C::Request {
            id: consumer,
            reservation: false,
        })
        .unwrap()
        .unwrap();
    core.complete(failed, Some("cleanup failed".into()))
        .unwrap();
    assert!(core.release_owned(consumer).is_err());
    assert_eq!(core.resolve(PORT, Some(consumer), Some(1)), Ok(Some(bound)));
    assert_eq!(core.resolve(PORT, Some(provider), Some(1)), Ok(Some(saved)));
    assert_eq!(
        core.resolve(PORT, Some(consumer), Some(0)),
        Err(ReadError::Stale)
    );
    assert_eq!(
        core.resolve(PORT, Some(usize::MAX), None),
        Err(ReadError::Unknown)
    );
    let retry = core.cleanup(C::Retry { id: consumer }).unwrap().unwrap();
    assert!(core.complete(failed, None).is_err());
    assert_eq!(core.resolve(PORT, Some(consumer), None), Ok(Some(bound)));
    core.complete(retry, None).unwrap();
    core.release_owned(consumer).unwrap();
    assert_eq!(core.resolve(PORT, Some(consumer), Some(1)), Ok(None));
    let cleanup = core
        .cleanup(C::Request {
            id: provider,
            reservation: false,
        })
        .unwrap()
        .unwrap();
    assert_eq!(core.resolve(PORT, Some(provider), Some(1)), Ok(Some(saved)));
    core.complete(cleanup, None).unwrap();
    core.release_owned(provider).unwrap();
    assert_eq!(core.resolve(PORT, Some(provider), Some(1)), Ok(None));
    let restarted = core.begin(provider).unwrap();
    assert_eq!(restarted.generation, 2);
    let later = core
        .publish(provider, 2, PORT, 300)
        .map_err(|e| e.error)
        .unwrap();
    core.complete(restarted, None).unwrap();
    core.finish(provider).unwrap();
    assert!(core.begin(consumer).is_err());
    core.episode_command(cordis_kernel::node_runtime::episode::Command::Restart { id: consumer })
        .unwrap();
    let restarted = core.begin(consumer).unwrap();
    assert_eq!(restarted.generation, 2);
    assert_eq!(
        core.resolve(PORT, Some(consumer), Some(1)),
        Err(ReadError::Stale)
    );
    let read = core
        .resolve(PORT, Some(consumer), Some(2))
        .unwrap()
        .unwrap();
    assert_eq!(
        (read.publication, read.value, read.source),
        (later, 300, Source::Committed { binding: 0 })
    );
}

#[test]
fn admission_policy_survives_rejection_cancellation_and_removal() {
    use cordis_kernel::node_runtime::policy::{PolicyError as P, Profile};
    use cordis_kernel::Error;
    let mut core = NodeRuntime::new(90);
    assert_eq!(
        core.mount(Some(42), vec![], vec![], true),
        Err(P::ParentClosed)
    );
    assert_eq!(
        core.mount(None, vec![PORT, PORT], vec![], true),
        Err(P::Kernel(Error::Conflict))
    );
    // Neither a rejected gate nor a rejected allocation freezes the profile.
    core.configure_profile(Profile::Harness).unwrap();
    assert_eq!(
        core.configure_profile(Profile::Cordis),
        Err(P::ProfileFrozen)
    );
    assert_eq!(
        core.seal_declarations(42, vec![]),
        Err(P::Kernel(Error::Unknown))
    );
    let parent = core.mount(None, vec![], vec![], false).unwrap();
    assert!(core.begin(parent).is_err());
    core.cleanup(C::Retire { id: parent }).unwrap();
    assert_eq!(
        core.mount(Some(parent), vec![], vec![], true),
        Err(P::ParentClosed)
    );
    core.seal_declarations(parent, vec![PORT]).unwrap();
    assert!(!core.episode(parent).unwrap().sealed);
    assert!(core.interfaces()[&parent].dependencies.is_empty());
    core.cleanup(C::Remove { id: parent }).unwrap();
    assert!(core.interfaces().is_empty());
    assert_eq!(
        core.configure_profile(Profile::Cordis),
        Err(P::ProfileFrozen)
    );
    assert_eq!(core.profile(), Profile::Harness);

    let mut default = NodeRuntime::new(91);
    let parent = default.mount(None, vec![], vec![], false).unwrap();
    default.seal_declarations(parent, vec![]).unwrap();
    assert_eq!(
        default.seal_declarations(parent, vec![PORT]),
        Err(P::AlreadySealed)
    );
    assert!(default.interfaces()[&parent].dependencies.is_empty());
    let setup = default.begin(parent).unwrap();
    default.complete(setup, None).unwrap();
    default.finish(parent).unwrap();
    default.cleanup(C::Withdraw { id: parent }).unwrap();
    assert!(!default.state().kernel().retired(parent));
    assert_eq!(
        default.mount(Some(parent), vec![], vec![], true),
        Err(P::ParentClosed)
    );
    assert_eq!(
        default.configure_profile(Profile::Harness),
        Err(P::ProfileFrozen)
    );
    assert_eq!(default.profile(), Profile::Cordis);
}

#[test]
fn notifications_select_actual_declarations_and_preserve_failed_cleanup_resources() {
    use cordis_kernel::node_runtime::policy::Profile;
    let other = Port {
        key: PORT.key,
        realm: PORT.realm + 1,
    };
    for profile in [Profile::Cordis, Profile::Harness] {
        let mut core = NodeRuntime::new(92);
        core.configure_profile(profile).unwrap();
        let provider = core.mount(None, vec![], vec![PORT, other], true).unwrap();
        let setup = core.begin(provider).unwrap();
        let publication = core
            .publish(provider, 1, PORT, 11)
            .map_err(|e| e.error)
            .unwrap();
        core.publish(provider, 1, other, 12)
            .map_err(|e| e.error)
            .unwrap();
        core.complete(setup, None).unwrap();
        core.finish(provider).unwrap();
        let matching = core.mount(None, vec![PORT], vec![], true).unwrap();
        let unrelated = core.mount(None, vec![other], vec![], true).unwrap();
        let blocked = core.mount(None, vec![PORT], vec![], true).unwrap();
        for id in [matching, unrelated, blocked] {
            let setup = core.begin(id).unwrap();
            core.complete(setup, Some("setup failed".into())).unwrap();
        }
        core.cleanup(C::Withdraw { id: blocked }).unwrap();
        let failed = core
            .cleanup(C::Request {
                id: blocked,
                reservation: false,
            })
            .unwrap()
            .unwrap();
        core.complete(failed, Some("inverse must retry".into()))
            .unwrap();
        let binding = core.admission(blocked).unwrap().resources()[0];
        // Empty notifications and a different realm must not clear this failure.
        core.notify(&[]).unwrap();
        assert_eq!(
            core.episode(matching).unwrap().failed.as_deref(),
            Some("setup failed")
        );
        core.notify(&[PORT, PORT]).unwrap();
        assert_eq!(
            core.episode(matching).unwrap().failed.is_none(),
            profile == Profile::Harness
        );
        assert_eq!(
            core.episode(unrelated).unwrap().failed.as_deref(),
            Some("setup failed")
        );
        assert_eq!(
            core.episode(blocked).unwrap().failed.as_deref(),
            Some("inverse must retry")
        );
        assert!(core.episode(blocked).unwrap().cleanup_failed);
        assert_eq!(core.admission(blocked).unwrap().resources(), &[binding]);
        assert_eq!(
            core.store().leased_value(binding.lease),
            Ok((publication, &11))
        );
        assert!(core.release(blocked, &[]).is_err());
        // Only explicit retry advances the failed cleanup, with a fresh ticket.
        let retry = core.cleanup(C::Retry { id: blocked }).unwrap().unwrap();
        assert_ne!(retry, failed);
        assert!(core.complete(failed, None).is_err());
        core.complete(retry, None).unwrap();
        core.release(blocked, &[]).unwrap();
        assert!(core.admission(blocked).is_none());
    }
}
