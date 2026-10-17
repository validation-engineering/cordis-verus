use cordis_kernel::configuration_batch::{Action, StepError};
use cordis_kernel::configuration_transaction::{Configuration, TransactionError};
use std::task::Poll;

#[test]
fn actual_update_results_gate_commit_and_reverse_recovery() {
    let mut state = Configuration::new("accepted");
    state
        .begin(
            "candidate",
            "captured factories",
            vec![
                Action::new(10_u64, 0),
                Action::new(20, 0),
                Action::new(30, 0),
            ],
        )
        .ok()
        .unwrap();
    assert!(matches!(state.commit(), Err(TransactionError::NotReady)));
    assert_eq!(
        state.poll_update::<&str, _>(|key, plan| {
            assert_eq!(*key, 10);
            *plan += 1;
            Poll::Pending
        }),
        Poll::Pending
    );
    assert!(matches!(state.commit(), Err(TransactionError::NotReady)));
    assert!(matches!(
        state.poll_update::<&str, _>(|key, plan| {
            assert_eq!((*key, *plan), (10, 1));
            *plan += 1;
            Poll::Ready(Ok(()))
        }),
        Poll::Ready(Ok(false))
    ));
    assert!(matches!(
        state.poll_update(|key, plan| {
            assert_eq!(*key, 20);
            *plan += 1;
            Poll::Ready(Err("forward failure"))
        }),
        Poll::Ready(Err(StepError::Callback("forward failure")))
    ));
    assert!(matches!(
        state.poll_update::<&str, _>(|_, _| panic!("failed batch cannot resume forward execution")),
        Poll::Ready(Err(StepError::Recovering))
    ));
    assert!(matches!(state.commit(), Err(TransactionError::NotReady)));
    assert!(state.recover("too early").is_err());
    assert_eq!(state.current(), &"accepted");
    assert_eq!(state.revision(), 0);
    assert_eq!(state.pending().unwrap().recovery, "captured factories");

    assert_eq!(
        state.poll_rollback(|key, plan| {
            assert_eq!((*key, *plan), (20, 1));
            *plan += 1;
            Poll::Ready(Err("inverse failure"))
        }),
        Poll::Ready(Err("inverse failure"))
    );
    // Unstarted plan 30 is discarded; the failed plan and its changed payload remain.
    assert_eq!(state.updates().actions().len(), 2);
    assert_eq!(
        state.poll_rollback::<&str, _>(|key, plan| {
            assert_eq!((*key, *plan), (20, 2));
            *plan += 1;
            Poll::Pending
        }),
        Poll::Pending
    );
    assert!(state.recover("still too early").is_err());
    assert_eq!(
        state.poll_rollback::<&str, _>(|key, plan| {
            assert_eq!((*key, *plan), (20, 3));
            Poll::Ready(Ok(()))
        }),
        Poll::Ready(Ok(false))
    );
    assert_eq!(
        state.poll_rollback::<&str, _>(|key, plan| {
            assert_eq!((*key, *plan), (10, 2));
            Poll::Ready(Ok(()))
        }),
        Poll::Ready(Ok(true))
    );
    let (old, pending) = state.recover("rebuilt accepted").ok().unwrap();
    assert_eq!(old, "accepted");
    assert_eq!(pending.candidate, "candidate");
    assert_eq!(state.current(), &"rebuilt accepted");
    assert_eq!(state.revision(), 0);
    assert!(matches!(state.commit(), Err(TransactionError::Idle))); // recovery does not leave a committable transaction
}

#[test]
fn commit_uses_the_owned_candidate_and_returns_the_exact_completed_plans() {
    let mut state = Configuration::new(5_u64);
    state
        .begin(8, 13, vec![Action::new("parent/child", 21)])
        .ok()
        .unwrap();
    assert_eq!(state.refresh(99), Err(99));
    assert!(state.begin(99, 100, vec![]).is_err());
    let (accepted, pending) = state.work();
    assert_eq!(*accepted, 5);
    pending.unwrap().recovery = 34;
    assert!(matches!(
        state.poll_update::<(), _>(|key, plan| {
            assert_eq!(*key, "parent/child");
            *plan = 55;
            Poll::Ready(Ok(()))
        }),
        Poll::Ready(Ok(true))
    ));
    let (old, recovery, actions) = state.commit().ok().unwrap();
    assert_eq!((old, recovery), (5, 34));
    assert_eq!(actions.actions()[0].key(), &"parent/child");
    assert_eq!(actions.actions()[0].payload(), &55);
    assert_eq!((*state.current(), state.revision()), (8, 1));
    assert!(matches!(state.commit(), Err(TransactionError::Idle)));
    state
        .begin(89, 144, vec![Action::new("unused", 233)])
        .ok()
        .unwrap();
    assert_eq!(
        state.poll_rollback::<(), _>(|_, _| panic!("unstarted plans have no inverse to run")),
        Poll::Ready(Ok(true))
    );
    state.recover(8).ok().unwrap();
    assert_eq!((*state.current(), state.revision()), (8, 1));
}

#[test]
fn structural_commit_requires_every_actual_phase_and_resumes_recovery() {
    use cordis_kernel::configuration_transaction::{Structure, StructureError};
    let mut state: Configuration<_, _, u64, ()> = Configuration::new("accepted");
    state
        .begin_structural("candidate", Vec::<Structure>::new(), vec![])
        .ok()
        .unwrap();
    // Empty update batches do not bypass structural lifecycle work.
    assert!(matches!(state.commit(), Err(TransactionError::NotReady)));
    assert!(state.recover("fabricated recovery").is_err());
    assert!(matches!(
        state.poll_update::<(), _>(|_, _| panic!("not prepared")),
        Poll::Ready(Err(StepError::Recovering))
    ));
    let phases = [
        Structure::Remove,
        Structure::SettleRemoved,
        Structure::Mount,
        Structure::SettleMounted,
    ];
    for (i, expected) in phases.into_iter().enumerate() {
        assert_eq!(state.structure(), Some(expected));
        assert_eq!(
            state.poll_structure::<&str, _>(|phase, accepted, pending| {
                assert_eq!(phase, expected);
                assert_eq!(*accepted, "accepted");
                pending.recovery.push(phase);
                Poll::Pending
            }),
            Poll::Pending
        );
        assert_eq!(state.structure(), Some(expected));
        assert!(matches!(state.commit(), Err(TransactionError::NotReady)));
        assert_eq!(
            state.poll_structure::<&str, _>(|_, _, _| Poll::Ready(Ok(()))),
            Poll::Ready(Ok(i == 3))
        );
    }
    assert!(matches!(state.commit(), Err(TransactionError::NotReady)));
    assert_eq!(
        state.poll_update::<(), _>(|_, _| panic!("empty batch")),
        Poll::Ready(Ok(true))
    );
    assert_eq!(state.structure(), Some(Structure::Adopt));
    assert_eq!(
        state.poll_structure(|_, _, _| Poll::Ready(Err("adoption failed"))),
        Poll::Ready(Err(StructureError::Callback("adoption failed")))
    );
    assert!(matches!(state.commit(), Err(TransactionError::NotReady)));
    assert_eq!(
        state.poll_rollback::<(), _>(|_, _| panic!("empty batch")),
        Poll::Ready(Ok(true))
    );
    for expected in [
        Structure::RecoverRemove,
        Structure::RecoverSettleRemoved,
        Structure::RecoverMount,
        Structure::RecoverSettleMounted,
    ] {
        assert_eq!(state.structure(), Some(expected));
        // Re-entering recover() after cancellation must not restart structural
        // work or destroy the record of already recreated nodes.
        assert_eq!(
            state.poll_rollback::<(), _>(|_, _| panic!("already drained")),
            Poll::Ready(Ok(true))
        );
        assert_eq!(state.structure(), Some(expected));
        assert!(state.recover("too early").is_err());
        assert_eq!(
            state.poll_structure::<(), _>(|phase, _, pending| {
                assert_eq!(phase, expected);
                pending.recovery.push(phase);
                Poll::Ready(Ok(()))
            }),
            Poll::Ready(Ok(expected == Structure::RecoverSettleMounted))
        );
    }
    assert!(matches!(state.commit(), Err(TransactionError::NotReady)));
    let (_, pending) = state.recover("reconstructed").ok().unwrap();
    assert_eq!(pending.recovery.len(), 8);
    assert_eq!(state.current(), &"reconstructed");
    assert_eq!(state.revision(), 0);

    state.begin_structural("next", vec![], vec![]).ok().unwrap();
    for _ in 0..4 {
        let _ = state.poll_structure::<(), _>(|_, _, _| Poll::Ready(Ok(())));
    }
    let _ = state.poll_update::<(), _>(|_, _| panic!("empty batch"));
    let _ = state.poll_structure::<(), _>(|phase, _, _| {
        assert_eq!(phase, Structure::Adopt);
        Poll::Ready(Ok(()))
    });
    state.commit().ok().unwrap();
    assert_eq!((state.current(), state.revision()), (&"next", 1));
}
