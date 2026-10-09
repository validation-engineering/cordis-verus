//! Public API histories for the Unit/Child recovery profile.
//!
//! These tests never inject private state. They observe retained identities and
//! successful recovery; the no-op Unit does not make inverse order observable.
use cordis_kernel::mixed_driver as mixed;
use cordis_kernel::mixed_driver::fresh;
use cordis_kernel::Phase;

fn fresh_bank() -> Vec<fresh::Blueprint> {
    vec![
        fresh::Blueprint::new(vec![], vec![], vec![fresh::Instruction::Unit]),
        fresh::Blueprint::new(
            vec![],
            vec![],
            vec![
                fresh::Instruction::Child {
                    blueprint: 0,
                    next: Some(1),
                },
                fresh::Instruction::Child {
                    blueprint: 0,
                    next: Some(2),
                },
            ],
        ),
    ]
}

fn fresh_observations(
    driver: &fresh::FreshDriver,
    count: usize,
) -> Vec<(Option<Phase>, bool, Option<usize>)> {
    (0..count)
        .map(|id| {
            (
                driver.phase(id),
                driver.retired(id),
                driver.inverse_count(id),
            )
        })
        .collect()
}

#[test]
fn fresh_history_retains_retired_children_until_parent_recovery() {
    use fresh::Command::*;
    let commands = [
        Insert {
            parent: None,
            blueprint: 1,
        },
        Begin { actor: 0 },
        Step { actor: 0 },
        Step { actor: 0 },
        Step { actor: 0 }, // Implicit terminal Unit at pc == code length.
        Retire { actor: 1 },
        Begin { actor: 2 },
        Step { actor: 2 },
        Retire { actor: 2 },
        Depart { actor: 2 },
        Unload { actor: 2 },
        Insert {
            parent: Some(0),
            blueprint: 0,
        },
        Begin { actor: 3 },
        Step { actor: 3 },
        Retire { actor: 0 },
        Depart { actor: 0 },
    ];
    let report = fresh::run_script(fresh_bank(), &commands);
    assert_eq!(report.error, None);
    assert_eq!(report.transitions.len(), commands.len());
    assert_eq!(
        report.transitions[2],
        mixed::Transition::Step {
            actor: 0,
            outcome: mixed::Outcome::Child {
                child: 1,
                finished: false
            },
        }
    );
    assert_eq!(
        report.transitions[3],
        mixed::Transition::Step {
            actor: 0,
            outcome: mixed::Outcome::Child {
                child: 2,
                finished: false
            },
        }
    );
    assert_eq!(
        report.transitions[4],
        mixed::Transition::Step {
            actor: 0,
            outcome: mixed::Outcome::Finished,
        }
    );
    let mut machine = report.machine;
    assert_eq!(machine.phase(0), Some(Phase::Unloading));
    assert_eq!(machine.inverse_count(0), Some(3));
    for child in [1, 2] {
        assert!(machine.retired(child));
        assert_eq!(machine.phase(child), Some(Phase::Inactive));
        assert_eq!(machine.inverse_count(child), Some(0));
    }
    // Child 1 never began, while child 2 already recovered its own Unit.
    // Both are still captured by the parent's actual journal.
    let before = fresh_observations(&machine, 4);
    for child in [1, 2] {
        assert_eq!(machine.remove(child), Err(fresh::DriverError::Retained));
        assert_eq!(fresh_observations(&machine, 4), before);
    }
    machine.unload(0).unwrap();
    assert_eq!(machine.phase(0), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(0), Some(0));
    for child in [1, 2] {
        assert!(machine.retired(child));
        assert_eq!(machine.phase(child), Some(Phase::Inactive));
        machine.remove(child).unwrap();
        assert_eq!(machine.phase(child), None);
    }
    // This child has the same ownership parent but was inserted externally.
    // No receipt of the parent captures it, so parent recovery leaves it alone.
    assert!(!machine.retired(3));
    assert_eq!(machine.phase(3), Some(Phase::Active));
    assert_eq!(machine.inverse_count(3), Some(1));
}

#[test]
fn mixed_history_retires_captured_children_without_running_their_journals() {
    use mixed::Command::*;
    let leaf = mixed::Blueprint::new(vec![], vec![], vec![mixed::Instruction::Unit]);
    let parent = mixed::Blueprint::new(
        vec![],
        vec![],
        vec![
            mixed::Instruction::Child {
                expected: 1,
                blueprint: 0,
                next: Some(1),
            },
            mixed::Instruction::Child {
                expected: 3,
                blueprint: 0,
                next: Some(2),
            },
            mixed::Instruction::Unit,
        ],
    );
    let commands = [
        Insert {
            parent: None,
            blueprint: 1,
        },
        Begin { actor: 0 },
        Step { actor: 0 },
        Insert {
            parent: Some(0),
            blueprint: 0,
        }, // External child gets ID 2.
        Step { actor: 0 },
        Step { actor: 0 },
        Begin { actor: 1 },
        Step { actor: 1 },
        Retire { actor: 3 },
        Retire { actor: 0 },
        Depart { actor: 0 },
    ];
    let report = mixed::run_script(vec![leaf, parent], &commands);
    assert_eq!(report.error, None);
    assert_eq!(report.transitions.len(), commands.len());
    assert_eq!(
        report.transitions[2],
        mixed::Transition::Step {
            actor: 0,
            outcome: mixed::Outcome::Child {
                child: 1,
                finished: false
            },
        }
    );
    assert_eq!(
        report.transitions[4],
        mixed::Transition::Step {
            actor: 0,
            outcome: mixed::Outcome::Child {
                child: 3,
                finished: false
            },
        }
    );
    let mut machine = report.machine;
    assert_eq!(machine.phase(0), Some(Phase::Unloading));
    assert_eq!(machine.inverse_count(0), Some(3));
    assert_eq!(machine.remove(3), Err(mixed::DriverError::Retained));
    assert_eq!(machine.phase(3), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(0), Some(3));
    machine.unload(0).unwrap();
    assert_eq!(machine.phase(0), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(0), Some(0));
    assert!(machine.retired(1));
    assert_eq!(machine.phase(1), Some(Phase::Active));
    assert_eq!(machine.inverse_count(1), Some(1));
    assert!(machine.retired(3));
    assert_eq!(machine.phase(3), Some(Phase::Inactive));
    assert!(!machine.retired(2));
    assert_eq!(machine.phase(2), Some(Phase::Inactive));
    // The child's separate episode must still depart and restore its own Unit.
    machine.depart(1).unwrap();
    machine.unload(1).unwrap();
    assert_eq!(machine.inverse_count(1), Some(0));
    machine.remove(1).unwrap();
    machine.remove(3).unwrap();
    assert_eq!(machine.phase(2), Some(Phase::Inactive));
    assert!(!machine.retired(2));
}

#[test]
fn failed_script_retained_removal_keeps_a_recoverable_actual_prefix() {
    use fresh::Command::*;
    let commands = [
        Insert {
            parent: None,
            blueprint: 1,
        },
        Begin { actor: 0 },
        Step { actor: 0 },
        Step { actor: 0 },
        Step { actor: 0 },
        Retire { actor: 1 },
        Retire { actor: 0 },
        Depart { actor: 0 },
        Remove { actor: 1 }, // Fails even though this child is retired/Inactive.
        Unload { actor: 0 },
        Retire { actor: 2 },
    ];
    let report = fresh::run_script(fresh_bank(), &commands);
    assert_eq!(report.error, Some(fresh::DriverError::Retained));
    assert_eq!(report.transitions.len(), 8);
    for (transition, command) in report.transitions.iter().zip(&commands) {
        assert_eq!(transition.command(), *command);
    }
    let mut machine = report.machine;
    assert_eq!(machine.phase(0), Some(Phase::Unloading));
    assert_eq!(machine.inverse_count(0), Some(3));
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert!(machine.retired(1));
    assert!(!machine.retired(2)); // Commands after the first error did not run.
    let before = fresh_observations(&machine, 3);
    assert_eq!(machine.remove(1), Err(fresh::DriverError::Retained));
    assert_eq!(fresh_observations(&machine, 3), before);

    machine.unload(0).unwrap();
    assert_eq!(machine.phase(0), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(0), Some(0));
    for child in [1, 2] {
        assert!(machine.retired(child));
        assert_eq!(machine.phase(child), Some(Phase::Inactive));
        machine.remove(child).unwrap();
    }
    machine.remove(0).unwrap();
    assert_eq!(machine.phase(0), None);
}

#[test]
fn bootstrap_terminal_publication_failure_keeps_a_recoverable_child_receipt() {
    let missing = cordis_kernel::Port { key: 71, realm: 4 };
    let leaf = fresh::Blueprint::new(vec![], vec![], vec![fresh::Instruction::Unit]);
    let parent = fresh::Blueprint::new(
        vec![],
        vec![missing],
        vec![fresh::Instruction::Child {
            blueprint: 0,
            next: Some(1),
        }],
    );
    let setup = [
        fresh::Command::Insert {
            parent: None,
            blueprint: 1,
        },
        fresh::Command::Begin { actor: 0 },
    ];
    let report = fresh::run_from_empty(vec![leaf, parent], &setup, 0);
    assert_eq!(report.actor, 0);
    assert_eq!(
        report.status,
        fresh::FromEmptyStatus::Blocked(fresh::DriverError::IncompleteProvision)
    );
    assert_eq!(report.steps, 1);
    assert_eq!(report.setup.len(), setup.len());
    for (transition, command) in report.setup.iter().zip(&setup) {
        assert_eq!(transition.command(), *command);
    }
    let mut machine = report.machine;
    assert_eq!(machine.phase(0), Some(Phase::Loading));
    assert_eq!(machine.read(0, missing), None);
    // Child committed, but the implicit terminal Unit failed its publication
    // check and contributed no receipt. No second child was allocated.
    assert_eq!(machine.inverse_count(0), Some(1));
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(1), Some(0));
    assert!(!machine.retired(1));
    assert_eq!(machine.phase(2), None);

    machine.retire(0).unwrap();
    machine.depart(0).unwrap();
    assert_eq!(machine.phase(0), Some(Phase::Unloading));
    machine.unload(0).unwrap();
    assert_eq!(machine.phase(0), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(0), Some(0));
    assert_eq!(machine.read(0, missing), None);
    assert!(machine.retired(1));
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    machine.remove(1).unwrap();
    machine.remove(0).unwrap();
}
