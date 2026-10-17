use cordis_kernel::cleanup_queue::completion::CleanupDispatch;
use cordis_kernel::execution::Execution;
use cordis_kernel::lifecycle_state::registration::shared_child::ChildCleanup;
use cordis_kernel::reversible_value::program::{Instruction, Program};
use cordis_kernel::reversible_value::{Applied, Branch, Operation, ReversibleValue, ValueError};

const END: Branch = Branch {
    matched: None,
    unmatched: None,
};
type Owner = Execution<(), (), (), ChildCleanup<(), ()>>;
fn apply(value: &ReversibleValue, operation: Operation) -> Applied {
    value.apply(operation, END).ok().unwrap()
}
fn restore(owner: &mut Owner) -> bool {
    match owner.dispatch_cleanup(0).unwrap().unwrap() {
        CleanupDispatch::Value { completion, .. } => completion.report.result.is_ok(),
        _ => panic!("expected the actual value inverse"),
    }
}

#[test]
fn actual_operation_and_result_select_the_continuation() {
    let value = ReversibleValue::new(41);
    let first = value
        .apply(
            Operation::Add(1),
            Branch {
                matched: Some(3),
                unmatched: Some(9),
            },
        )
        .ok()
        .unwrap();
    assert_eq!(
        (first.outcome.before, first.outcome.after, first.next),
        (41, 42, Some(3))
    );
    let compare = value
        .apply(
            Operation::CompareExchange {
                expected: 7,
                value: 99,
            },
            Branch {
                matched: Some(1),
                unmatched: Some(2),
            },
        )
        .ok()
        .unwrap();
    assert!(!compare.outcome.matched);
    assert_eq!(compare.next, Some(2));
    assert_eq!(value.snapshot().value(), 42);
    assert!(compare.inverse.restore().is_ok());
    assert!(first.inverse.restore().is_ok());
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (41, 0)
    );
}

#[test]
fn same_value_interference_retains_the_exact_inverse() {
    let value = ReversibleValue::new(7);
    let first = apply(&value, Operation::Replace(7));
    let second = apply(&value, Operation::Replace(7));
    let first = first.inverse.restore().err().unwrap();
    assert_eq!(value.snapshot().depth(), 2);
    assert!(second.inverse.restore().is_ok());
    assert!(first.restore().is_ok());
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (7, 0));
}

#[test]
fn inverse_keeps_its_original_shared_value() {
    let left = ReversibleValue::new(1);
    let right = ReversibleValue::new(1);
    let undo = apply(&left.clone(), Operation::Xor(3)).inverse;
    let other = apply(&right, Operation::Xor(3)).inverse;
    assert!(undo.restore().is_ok());
    assert_eq!(left.snapshot().value(), 1);
    assert_eq!(right.snapshot().value(), 2);
    assert!(other.restore().is_ok());
}

#[test]
fn concurrent_writes_restore_in_observed_order() {
    let value = ReversibleValue::new(0);
    let threads: Vec<_> = (0..16)
        .map(|_| {
            let value = value.clone();
            std::thread::spawn(move || apply(&value, Operation::Add(1)))
        })
        .collect();
    let mut applied: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();
    assert_eq!(value.snapshot().value(), 16);
    applied.sort_by_key(|applied| applied.outcome.after);
    for applied in applied.into_iter().rev() {
        assert!(applied.inverse.restore().is_ok());
    }
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (0, 0));
}

#[test]
fn overflow_and_closed_admission_do_not_modify_the_value() {
    let value = ReversibleValue::new(u64::MAX);
    let mut owner = Owner::new(7);
    assert!(matches!(
        owner.apply_value(0, &value, Operation::Add(1), END),
        Err(ValueError::Overflow)
    ));
    assert!(owner.dispatch_cleanup(0).unwrap().is_none());
    owner.withdraw();
    assert!(matches!(
        owner.apply_value(0, &value, Operation::Replace(0), END),
        Err(ValueError::Closed)
    ));
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (u64::MAX, 0)
    );
}

#[test]
fn cleanup_failure_keeps_payload_until_explicit_retry() {
    let value = ReversibleValue::new(10);
    let mut first = Owner::new(10);
    let mut second = Owner::new(20);
    first
        .apply_value(0, &value, Operation::Add(5), END)
        .unwrap();
    second
        .apply_value(0, &value, Operation::Add(7), END)
        .unwrap();
    first.withdraw();
    second.withdraw();
    assert!(!restore(&mut first));
    assert!(first.get(0).unwrap().has_failed());
    assert!(first.dispatch_cleanup(0).unwrap().is_none());
    assert!(restore(&mut second));
    assert_eq!(value.snapshot().value(), 15);
    first.retry(0).unwrap();
    assert!(restore(&mut first));
    assert_eq!(value.snapshot().value(), 10);
}

#[test]
fn outcome_branching_program_registers_every_inverse_in_order() {
    let value = ReversibleValue::new(5);
    let program = Program::new(vec![
        Instruction {
            operation: Operation::CompareExchange {
                expected: 4,
                value: 100,
            },
            branch: Branch {
                matched: Some(1),
                unmatched: Some(2),
            },
        },
        Instruction {
            operation: Operation::Replace(999),
            branch: END,
        },
        Instruction {
            operation: Operation::Add(3),
            branch: END,
        },
    ])
    .unwrap();
    let mut owner = Owner::new(30);
    let report = owner.run_value_program(0, &value, &program).unwrap();
    assert!(report.error.is_none());
    assert_eq!(report.outcomes.len(), 2);
    assert_eq!(report.snapshot.value(), 8);
    owner.withdraw();
    assert!(restore(&mut owner));
    assert_eq!(value.snapshot().value(), 5);
    assert!(restore(&mut owner));
    assert_eq!(value.snapshot().depth(), 0);
    assert!(owner.dispatch_cleanup(0).unwrap().is_none());
}

#[test]
fn failing_program_preserves_its_actual_successful_prefix() {
    let value = ReversibleValue::new(4);
    let program = Program::new(vec![
        Instruction {
            operation: Operation::Replace(u64::MAX),
            branch: Branch {
                matched: Some(1),
                unmatched: Some(1),
            },
        },
        Instruction {
            operation: Operation::Add(1),
            branch: END,
        },
    ])
    .unwrap();
    let mut owner = Owner::new(40);
    let report = owner.run_value_program(0, &value, &program).unwrap();
    assert_eq!(report.error, Some(ValueError::Overflow));
    assert_eq!(report.outcomes.len(), 1);
    assert_eq!(value.snapshot().value(), u64::MAX);
    owner.withdraw();
    assert!(restore(&mut owner));
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (4, 0));
}

#[test]
fn malformed_programs_are_rejected_before_execution() {
    for target in [0, 1, usize::MAX] {
        assert!(Program::new(vec![Instruction {
            operation: Operation::Add(1),
            branch: Branch {
                matched: Some(target),
                unmatched: None
            }
        }])
        .is_err());
    }
    let value = ReversibleValue::new(4);
    let mut owner = Owner::new(50);
    let report = owner
        .run_value_program(0, &value, &Program::new(vec![]).unwrap())
        .unwrap();
    assert!(report.error.is_none());
    assert!(report.outcomes.is_empty());
    assert_eq!(value.snapshot().depth(), 0);
}

#[test]
fn aliases_and_retained_cleanup_follow_allocations_after_concurrent_slot_replacement() {
    use cordis_kernel::reversible_value::{joint::Journal, slot::Slot};
    use std::sync::{mpsc, Arc};
    use std::time::Duration;

    let journal = Journal::new();
    let original = Arc::new(ReversibleValue::new_in(&journal, 10));
    let replacement = Arc::new(ReversibleValue::new_in(&journal, 100));
    let first = Arc::new(Slot::new(original.clone()));
    let alias = Slot::new(original.clone());
    let retained = first.capture();
    let write = apply(retained.value(), Operation::Add(5));
    assert_eq!(first.capture().observe_value().value(), 15);
    assert_eq!(alias.capture().observe_value().value(), 15);
    let before = retained.execution_snapshot();

    let worker_slot = first.clone();
    let worker_value = replacement.clone();
    let (done, completed) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        let replaced = worker_slot.replace(worker_value).ok().unwrap();
        let (old, new) = replaced.observations();
        assert_eq!((old.revision(), new.revision()), (0, 1));
        let _ = new.execution_snapshot();
        done.send(()).unwrap();
    });
    completed.recv_timeout(Duration::from_secs(10)).unwrap();
    worker.join().unwrap();
    let _ = before.refresh();
    let _ = retained.execution_snapshot();
    assert_eq!(first.capture().observe_value().value(), 100);
    assert_eq!(alias.capture().revision(), 0);
    assert_eq!(alias.capture().observe_value().value(), 15);
    assert!(!retained.check_result(true).accepted());

    assert!(write.inverse.restore().is_ok());
    assert_eq!(retained.observe_value().value(), 10);
    assert_eq!(alias.capture().observe_value().value(), 10);
    assert_eq!(
        (
            replacement.snapshot().value(),
            replacement.snapshot().depth()
        ),
        (100, 0)
    );
    let _ = retained.execution_snapshot();
}

#[test]
fn foreign_slot_target_keeps_its_own_inverse_after_return_to_local_object() {
    use cordis_kernel::reversible_value::{joint::Journal, slot::Slot};
    use std::sync::Arc;

    let journal = Journal::new();
    let local = Arc::new(ReversibleValue::new_in(&journal, 7));
    let foreign = Arc::new(ReversibleValue::new(7));
    let slot = Slot::new(local.clone());
    let local_capture = slot.capture();
    slot.replace(foreign.clone()).ok().unwrap();
    let foreign_capture = slot.capture();
    let write = apply(foreign_capture.value(), Operation::Add(3));
    let _ = foreign_capture.execution_snapshot();
    slot.replace(local.clone()).ok().unwrap();
    let _ = foreign_capture.execution_snapshot();
    let _ = local_capture.execution_snapshot();
    assert_eq!(slot.capture().revision(), 2);
    assert_eq!(slot.capture().observe_value().value(), 7);
    assert_eq!(foreign_capture.observe_value().value(), 10);
    assert!(write.inverse.restore().is_ok());
    assert_eq!((local.snapshot().value(), local.snapshot().depth()), (7, 0));
    assert_eq!(
        (foreign.snapshot().value(), foreign.snapshot().depth()),
        (7, 0)
    );
    assert!(!local_capture.check_result(true).accepted());
    assert!(!foreign_capture.check_result(true).accepted());
}
