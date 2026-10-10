use cordis_kernel::action_ledger::{ActionKind, ActionTicket};
use cordis_kernel::lifecycle_actions::CleanupOutcome;
use cordis_kernel::lifecycle_state::cleanup::{CleanupCommand as C, CleanupReply};
use cordis_kernel::lifecycle_state::LifecycleState;
use cordis_kernel::{Binding, Phase, Port};

fn activate(state: &mut LifecycleState, id: usize) {
    let ticket = state.begin(id).unwrap();
    state.complete_setup(ticket).unwrap();
    state.finish(id).unwrap();
}
fn withdraw(state: &mut LifecycleState, id: usize) {
    assert!(state.execute_cleanup(C::Retire { id }).is_ok());
    assert!(state.execute_cleanup(C::Withdraw { id }).is_ok());
}
fn issued(reply: CleanupReply) -> ActionTicket {
    reply.unwrap().expect("admission returns its actual ticket")
}
fn report(ticket: ActionTicket, outcome: CleanupOutcome) -> C {
    C::Report { ticket, outcome }
}
fn release(id: usize) -> C {
    C::Release {
        id,
        reservation: false,
    }
}

#[test]
fn repeated_failed_prefixes_pin_the_provider_while_another_consumer_finishes() {
    let mut state = LifecycleState::new(120);
    let port = Port { key: 1, realm: 0 };
    let provider = state.insert(None, vec![], vec![port]).unwrap();
    let first = state.insert(None, vec![port], vec![]).unwrap();
    let second = state.insert(None, vec![port], vec![]).unwrap();
    for id in [provider, first, second] {
        activate(&mut state, id);
    }
    for id in [provider, first, second] {
        withdraw(&mut state, id);
    }
    let mut current = issued(state.execute_cleanup(C::Request {
        id: first,
        reservation: false,
    }));
    let other = issued(state.execute_cleanup(C::Request {
        id: second,
        reservation: false,
    }));
    let original = state.kernel().committed(first);
    assert_eq!(
        original,
        [Binding {
            key: 1,
            realm: 0,
            provider
        }]
    );
    assert!(state
        .execute_cleanup(report(current, CleanupOutcome::Failed))
        .is_ok());
    assert!(state
        .execute_cleanup(report(other, CleanupOutcome::Succeeded))
        .is_ok());
    let commands = [
        report(current, CleanupOutcome::Succeeded),
        release(first),
        release(second),
        C::Remove { id: second },
        C::Request {
            id: provider,
            reservation: false,
        },
    ];
    let run = state.run_cleanup(&commands);
    assert_eq!(
        run.replies.iter().map(Result::is_ok).collect::<Vec<_>>(),
        [false, false, true, true, false]
    );
    assert_eq!(state.kernel().committed(first), original);
    assert!(!state.kernel().contains(second));

    let mut consumed = vec![current];
    for _ in 0..5 {
        current = issued(state.execute_cleanup(C::Retry { id: first }));
        assert!(consumed.iter().all(|old| current.action > old.action));
        let mut commands: Vec<_> = consumed
            .iter()
            .map(|old| report(*old, CleanupOutcome::Succeeded))
            .collect();
        commands.extend([
            C::Retry { id: first },
            release(first),
            C::Request {
                id: provider,
                reservation: false,
            },
            C::Remove { id: provider },
        ]);
        assert!(state
            .run_cleanup(&commands)
            .replies
            .iter()
            .all(Result::is_err));
        assert_eq!(state.pending(first), Some(current));
        assert_eq!(state.kernel().committed(first), original);
        assert!(!state.kernel().cleanup_started(provider));
        assert!(state
            .execute_cleanup(report(current, CleanupOutcome::Failed))
            .is_ok());
        assert!(state.execute_cleanup(release(first)).is_err());
        consumed.push(current);
    }
    current = issued(state.execute_cleanup(C::Retry { id: first }));
    assert!(state
        .execute_cleanup(report(current, CleanupOutcome::Succeeded))
        .is_ok());
    assert_eq!(state.kernel().committed(first), original); // A report is not release.
    assert!(state.execute_cleanup(release(first)).is_ok());
    assert!(state.kernel().committed(first).is_empty());
    assert!(state.execute_cleanup(C::Remove { id: first }).is_ok());
    let cleanup = issued(state.execute_cleanup(C::Request {
        id: provider,
        reservation: false,
    }));
    let run = state.run_cleanup(&[
        report(cleanup, CleanupOutcome::Succeeded),
        release(provider),
        C::Remove { id: provider },
        report(current, CleanupOutcome::Succeeded),
    ]);
    assert_eq!(
        run.replies.iter().map(Result::is_ok).collect::<Vec<_>>(),
        [true, true, true, false]
    );
    assert!(!state.kernel().contains(provider));
}

#[test]
fn setup_reply_and_wrong_ticket_fields_cannot_authorize_cleanup() {
    let mut state = LifecycleState::new(121);
    let id = state.insert(None, vec![], vec![]).unwrap();
    let setup = state.begin(id).unwrap();
    withdraw(&mut state, id);
    assert!(state
        .execute_cleanup(C::Request {
            id,
            reservation: false
        })
        .is_err());
    assert!(state
        .execute_cleanup(report(setup, CleanupOutcome::Succeeded))
        .is_err());
    assert_eq!(state.pending(id), Some(setup));
    assert!(state
        .execute_cleanup(C::SettleSetup { ticket: setup })
        .is_ok());
    let cleanup = issued(state.execute_cleanup(C::Request {
        id,
        reservation: false,
    }));
    let forgeries = [
        ActionTicket {
            kind: ActionKind::Setup,
            ..cleanup
        },
        ActionTicket {
            domain: 122,
            ..cleanup
        },
        ActionTicket {
            generation: 0,
            ..cleanup
        },
        ActionTicket {
            action: setup.action,
            ..cleanup
        },
        ActionTicket {
            id: usize::MAX,
            ..cleanup
        },
    ];
    for ticket in forgeries {
        assert!(state
            .execute_cleanup(report(ticket, CleanupOutcome::Succeeded))
            .is_err());
        assert_eq!(state.pending(id), Some(cleanup));
        assert!(state.execute_cleanup(release(id)).is_err());
    }
    assert!(state
        .execute_cleanup(C::SettleSetup { ticket: cleanup })
        .is_err());
    assert!(state
        .execute_cleanup(report(cleanup, CleanupOutcome::Drained))
        .is_ok());
    assert!(state.execute_cleanup(release(id)).is_ok());
    assert_eq!(state.kernel().phase(id), Some(Phase::Inactive));
}

#[test]
fn generation_zero_reservation_uses_its_own_release_guard_after_retry() {
    let mut state = LifecycleState::new(123);
    let id = state.insert(None, vec![], vec![]).unwrap();
    assert!(state.execute_cleanup(C::Retire { id }).is_ok());
    let first = issued(state.execute_cleanup(C::Request {
        id,
        reservation: true,
    }));
    assert_eq!(first.generation, 0);
    assert!(state
        .execute_cleanup(report(first, CleanupOutcome::Failed))
        .is_ok());
    assert!(state.execute_cleanup(C::Remove { id }).is_err());
    let next = issued(state.execute_cleanup(C::Retry { id }));
    assert!(state
        .execute_cleanup(report(first, CleanupOutcome::Succeeded))
        .is_err());
    assert!(state
        .execute_cleanup(report(next, CleanupOutcome::Succeeded))
        .is_ok());
    assert!(state.execute_cleanup(release(id)).is_err());
    assert!(state
        .execute_cleanup(C::Release {
            id,
            reservation: true
        })
        .is_ok());
    assert_eq!(state.kernel().episode_generation(id), Some(0));
    assert_eq!(state.kernel().phase(id), Some(Phase::Inactive));
    assert!(!state.kernel().cleanup_started(id));
    assert!(state.execute_cleanup(C::Remove { id }).is_ok());
    assert!(state
        .execute_cleanup(report(next, CleanupOutcome::Succeeded))
        .is_err());
}

#[test]
fn completed_receipts_stay_rejected_after_real_episode_reactivation() {
    let mut state = LifecycleState::new(124);
    let id = state.insert(None, vec![], vec![]).unwrap();
    let mut completed = Vec::new();
    for generation in 1..=3 {
        activate(&mut state, id);
        assert_eq!(state.kernel().episode_generation(id), Some(generation));
        assert!(state.execute_cleanup(C::Withdraw { id }).is_ok());
        let ticket = issued(state.execute_cleanup(C::Request {
            id,
            reservation: false,
        }));
        for old in &completed {
            assert!(state
                .execute_cleanup(report(*old, CleanupOutcome::Succeeded))
                .is_err());
            assert_eq!(state.pending(id), Some(ticket));
        }
        assert!(state
            .execute_cleanup(report(ticket, CleanupOutcome::Succeeded))
            .is_ok());
        assert!(state.execute_cleanup(release(id)).is_ok());
        completed.push(ticket);
    }
}
