use cordis_kernel::mixed_driver::fresh::{
    run_from_empty, Blueprint, Command, DriverError, FromEmptyStatus, Instruction, Outcome,
    Transition,
};
use cordis_kernel::{Error, Phase, Port};

fn service_key() -> Port {
    Port { key: 7, realm: 3 }
}

fn own_key() -> Port {
    Port { key: 8, realm: 3 }
}

fn provider() -> Blueprint {
    Blueprint::new(
        vec![],
        vec![service_key()],
        vec![Instruction::Provide {
            key: service_key(),
            value: 7,
            next: None,
        }],
    )
}

fn blueprints(complete: bool) -> Vec<Blueprint> {
    let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let last = if complete {
        Instruction::Provide {
            key: own_key(),
            value: 42,
            next: None,
        }
    } else {
        Instruction::Xor {
            key: own_key(),
            mask: 3,
            next: None,
        }
    };
    let parent = Blueprint::new(
        vec![service_key()],
        vec![own_key()],
        vec![
            Instruction::Xor {
                key: service_key(),
                mask: 5,
                next: Some(1),
            },
            Instruction::Child {
                blueprint: 0,
                next: Some(2),
            },
            last,
        ],
    );
    vec![leaf, provider(), parent]
}

fn prepared_prefix() -> Vec<Command> {
    vec![
        Command::Insert {
            parent: None,
            blueprint: 1,
        },
        Command::Begin { actor: 0 },
        Command::Step { actor: 0 },
        Command::Insert {
            parent: None,
            blueprint: 2,
        },
        Command::Begin { actor: 1 },
        Command::Step { actor: 1 },
    ]
}

fn assert_setup_prefix(transitions: &[Transition], commands: &[Command]) {
    assert!(transitions.len() <= commands.len());
    for (transition, command) in transitions.iter().zip(commands) {
        assert_eq!(transition.command(), *command);
    }
}

#[test]
fn setup_failure_stops_before_running_an_already_ready_actor() {
    let mut commands = prepared_prefix();
    commands.push(Command::Begin { actor: 99 });
    commands.push(Command::Step { actor: 1 });
    let report = run_from_empty(blueprints(true), &commands, 1);
    assert_eq!(report.actor, 1);
    assert_eq!(
        report.status,
        FromEmptyStatus::SetupFailed(DriverError::Unknown)
    );
    assert_eq!(report.steps, 0);
    assert_eq!(report.setup.len(), 6);
    assert_setup_prefix(&report.setup, &commands);
    assert_eq!(report.machine.phase(0), Some(Phase::Active));
    assert_eq!(report.machine.phase(1), Some(Phase::Loading));
    assert_eq!(report.machine.read(0, service_key()), Some(7 ^ 5));
    assert_eq!(report.machine.read(1, own_key()), None);
    assert_eq!(report.machine.inverse_count(1), Some(1));
    assert_eq!(report.machine.phase(2), None);

    // The next instruction was executable; only the setup failure prevented
    // the autonomous runner from creating this child and publishing the actor.
    let mut machine = report.machine;
    let resumed = machine.run_until_blocked(1);
    assert_eq!(resumed.steps, 2);
    assert_eq!(resumed.error, None);
    assert_eq!(machine.phase(1), Some(Phase::Active));
    assert_eq!(machine.phase(2), Some(Phase::Inactive));
    assert_eq!(machine.read(1, own_key()), Some(42));
}

#[test]
fn successful_bootstrap_composes_setup_and_run_effects_in_one_recoverable_journal() {
    let commands = prepared_prefix();
    let report = run_from_empty(blueprints(true), &commands, 1);
    assert_eq!(report.actor, 1);
    assert_eq!(report.status, FromEmptyStatus::Finished);
    assert_eq!(report.steps, 2);
    assert_eq!(report.setup.len(), commands.len());
    assert_setup_prefix(&report.setup, &commands);
    assert_eq!(
        report.setup[5],
        Transition::Step {
            actor: 1,
            outcome: Outcome::Advanced,
        }
    );
    assert_eq!(report.machine.phase(1), Some(Phase::Active));
    assert_eq!(report.machine.inverse_count(1), Some(3));
    assert_eq!(report.machine.read(0, service_key()), Some(7 ^ 5));
    assert_eq!(report.machine.read(1, own_key()), Some(42));
    assert_eq!(report.machine.phase(2), Some(Phase::Inactive));
    assert_eq!(report.machine.inverse_count(2), Some(0));
    assert_eq!(report.machine.phase(3), None);

    let mut machine = report.machine;
    assert_eq!(machine.remove(2), Err(DriverError::Retained));
    machine.retire(0).unwrap();
    machine.depart(0).unwrap();
    machine.depart(1).unwrap();
    machine.unload(1).unwrap();
    assert_eq!(machine.read(0, service_key()), Some(7));
    assert_eq!(machine.read(1, own_key()), None);
    assert_eq!(machine.inverse_count(1), Some(0));
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert!(machine.retired(2));
    machine.remove(2).unwrap();
    machine.unload(0).unwrap();
    machine.remove(0).unwrap();
}

#[test]
fn successful_setup_can_leave_a_strictly_blocked_run_with_its_committed_prefix() {
    let commands = prepared_prefix();
    let report = run_from_empty(blueprints(false), &commands, 1);
    assert_eq!(report.actor, 1);
    assert_eq!(
        report.status,
        FromEmptyStatus::Blocked(DriverError::MissingValue)
    );
    assert_eq!(report.steps, 1);
    assert_eq!(report.setup.len(), commands.len());
    assert_setup_prefix(&report.setup, &commands);
    assert_eq!(report.machine.phase(1), Some(Phase::Loading));
    assert_eq!(report.machine.inverse_count(1), Some(2));
    assert_eq!(report.machine.read(0, service_key()), Some(7 ^ 5));
    assert_eq!(report.machine.read(1, own_key()), None);
    assert_eq!(report.machine.phase(2), Some(Phase::Inactive));
    assert_eq!(report.machine.phase(3), None);

    let mut machine = report.machine;
    let retry = machine.run_until_blocked(1);
    assert_eq!(retry.steps, 0);
    assert_eq!(retry.error, Some(DriverError::MissingValue));
    assert_eq!(machine.inverse_count(1), Some(2));
    assert_eq!(machine.insert(None, 0), Ok(3));
}

#[test]
fn empty_setup_reports_an_unknown_actor_as_a_run_blockage() {
    let report = run_from_empty(vec![], &[], 99);
    assert_eq!(report.actor, 99);
    assert_eq!(
        report.status,
        FromEmptyStatus::Blocked(DriverError::Unknown)
    );
    assert_eq!(report.steps, 0);
    assert!(report.setup.is_empty());
    assert_eq!(report.machine.phase(99), None);
    assert_eq!(report.machine.phase(0), None);
}

#[test]
fn an_actor_completed_during_setup_keeps_the_real_autonomous_step_error() {
    let commands = [
        Command::Insert {
            parent: None,
            blueprint: 0,
        },
        Command::Begin { actor: 0 },
        Command::Step { actor: 0 },
    ];
    let report = run_from_empty(vec![provider()], &commands, 0);
    assert_eq!(report.actor, 0);
    assert_eq!(
        report.status,
        FromEmptyStatus::Blocked(DriverError::Kernel(Error::InvalidState))
    );
    assert_eq!(report.steps, 0);
    assert_eq!(report.setup.len(), commands.len());
    assert_setup_prefix(&report.setup, &commands);
    assert_eq!(report.machine.phase(0), Some(Phase::Active));
    assert_eq!(report.machine.inverse_count(0), Some(1));
    assert_eq!(report.machine.read(0, service_key()), Some(7));
}

#[test]
fn setup_commands_use_the_provider_state_at_each_call() {
    for publish_before_begin in [false, true] {
        let reader = Blueprint::new(
            vec![service_key()],
            vec![],
            vec![Instruction::Xor {
                key: service_key(),
                mask: 5,
                next: None,
            }],
        );
        let mut commands = vec![
            Command::Insert {
                parent: None,
                blueprint: 1,
            },
            Command::Insert {
                parent: None,
                blueprint: 0,
            },
        ];
        if publish_before_begin {
            commands.push(Command::Begin { actor: 1 });
            commands.push(Command::Step { actor: 1 });
        }
        commands.push(Command::Begin { actor: 0 });
        let report = run_from_empty(vec![provider(), reader], &commands, 0);
        assert_setup_prefix(&report.setup, &commands);
        if publish_before_begin {
            assert_eq!(report.status, FromEmptyStatus::Finished);
            assert_eq!(report.setup.len(), commands.len());
            assert_eq!(report.steps, 1);
            assert_eq!(report.machine.phase(0), Some(Phase::Active));
            assert_eq!(report.machine.read(1, service_key()), Some(7 ^ 5));
            assert_eq!(report.machine.inverse_count(0), Some(1));
        } else {
            assert_eq!(
                report.status,
                FromEmptyStatus::SetupFailed(DriverError::Kernel(Error::MissingDependency))
            );
            assert_eq!(report.setup.len(), 2);
            assert_eq!(report.steps, 0);
            assert_eq!(report.machine.phase(0), Some(Phase::Inactive));
            assert_eq!(report.machine.phase(1), Some(Phase::Inactive));
            assert_eq!(report.machine.read(1, service_key()), None);
            assert_eq!(report.machine.inverse_count(0), Some(0));
            // Registration needed neither an existing provider nor a published
            // dependency. Publication makes the previously rejected Begin work.
            let mut machine = report.machine;
            machine.begin(1).unwrap();
            assert_eq!(machine.step(1), Ok(Outcome::Finished));
            machine.begin(0).unwrap();
            let resumed = machine.run_until_blocked(0);
            assert_eq!(resumed.error, None);
            assert_eq!(resumed.steps, 1);
            assert_eq!(machine.read(1, service_key()), Some(7 ^ 5));
        }
    }
}

#[test]
fn setup_insert_checks_the_bank_prefix_and_registered_reservations() {
    let invalid = Blueprint::new(
        vec![],
        vec![service_key()],
        vec![Instruction::Provide {
            key: service_key(),
            value: 7,
            next: Some(0),
        }],
    );
    let commands = [
        Command::Insert {
            parent: None,
            blueprint: 2,
        },
        Command::Insert {
            parent: None,
            blueprint: 0,
        },
    ];
    let report = run_from_empty(
        vec![
            Blueprint::new(vec![], vec![], vec![Instruction::Unit]),
            invalid,
            Blueprint::new(vec![], vec![], vec![Instruction::Unit]),
        ],
        &commands,
        0,
    );
    assert_eq!(
        report.status,
        FromEmptyStatus::SetupFailed(DriverError::InvalidInstruction)
    );
    assert!(report.setup.is_empty());
    assert_eq!(report.steps, 0);
    assert_eq!(report.machine.phase(0), None);
    let mut machine = report.machine;
    assert_eq!(machine.insert(None, 0), Ok(0));

    for retired in [false, true] {
        let mut commands = vec![Command::Insert {
            parent: None,
            blueprint: 0,
        }];
        if retired {
            commands.push(Command::Retire { actor: 0 });
        }
        commands.push(Command::Insert {
            parent: None,
            blueprint: 0,
        });
        let report = run_from_empty(vec![provider()], &commands, 0);
        assert_eq!(
            report.status,
            FromEmptyStatus::SetupFailed(DriverError::Kernel(Error::Conflict))
        );
        assert_eq!(report.setup.len(), commands.len() - 1);
        assert_setup_prefix(&report.setup, &commands);
        assert_eq!(report.steps, 0);
        assert_eq!(report.machine.phase(0), Some(Phase::Inactive));
        assert_eq!(report.machine.retired(0), retired);
        assert_eq!(report.machine.read(0, service_key()), None);
        assert_eq!(report.machine.phase(1), None);
        let mut machine = report.machine;
        if !retired {
            machine.retire(0).unwrap();
        }
        machine.remove(0).unwrap();
        assert_eq!(machine.insert(None, 0), Ok(1));
        machine.begin(1).unwrap();
        assert_eq!(machine.step(1), Ok(Outcome::Finished));
        assert_eq!(machine.read(1, service_key()), Some(7));
    }
}

#[test]
fn setup_begin_and_step_failures_keep_the_prefix_at_the_failed_command() {
    for fail_begin in [false, true] {
        let mut commands = prepared_prefix();
        let expected_error = if fail_begin {
            commands.push(Command::Begin { actor: 1 });
            DriverError::Retained
        } else {
            commands.push(Command::Step { actor: 1 });
            commands.push(Command::Step { actor: 1 });
            DriverError::MissingValue
        };
        commands.push(Command::Insert {
            parent: None,
            blueprint: 0,
        });
        let report = run_from_empty(blueprints(fail_begin), &commands, 1);
        assert_eq!(report.status, FromEmptyStatus::SetupFailed(expected_error));
        assert_eq!(report.steps, 0);
        assert_eq!(report.setup.len(), if fail_begin { 6 } else { 7 });
        assert_setup_prefix(&report.setup, &commands);
        assert_eq!(report.machine.phase(1), Some(Phase::Loading));
        assert_eq!(report.machine.read(0, service_key()), Some(7 ^ 5));
        assert_eq!(report.machine.read(1, own_key()), None);
        assert_eq!(
            report.machine.inverse_count(1),
            Some(if fail_begin { 1 } else { 2 })
        );
        assert_eq!(
            report.machine.phase(2),
            if fail_begin {
                None
            } else {
                Some(Phase::Inactive)
            }
        );
        let mut machine = report.machine;
        assert_eq!(machine.insert(None, 0), Ok(if fail_begin { 2 } else { 3 }));
    }
}
