use cordis_kernel::mixed_driver::fresh::{
    run_script, Blueprint, Command, DriverError, FreshDriver, Instruction, Outcome, Transition,
};
use cordis_kernel::{Error, Phase, Port};

fn key() -> Port {
    Port { key: 7, realm: 3 }
}
fn leaf() -> Blueprint {
    Blueprint::new(vec![], vec![], vec![Instruction::Unit])
}
fn provider() -> Blueprint {
    Blueprint::new(
        vec![],
        vec![key()],
        vec![Instruction::Provide {
            key: key(),
            value: 7,
            next: None,
        }],
    )
}
fn parent() -> Blueprint {
    Blueprint::new(
        vec![key()],
        vec![],
        vec![
            Instruction::Xor {
                key: key(),
                mask: 5,
                next: Some(1),
            },
            Instruction::Child {
                blueprint: 0,
                next: Some(2),
            },
            Instruction::Xor {
                key: key(),
                mask: 3,
                next: None,
            },
        ],
    )
}
fn install(driver: &mut FreshDriver, blueprint: usize) -> usize {
    let id = driver.insert(None, blueprint).unwrap();
    driver.begin(id).unwrap();
    assert_eq!(driver.step(id), Ok(Outcome::Finished));
    id
}

#[test]
fn same_child_code_reactivates_after_cleanup_with_intervening_external_allocations() {
    let mut driver = FreshDriver::new(vec![leaf(), parent(), provider()]);
    let old_service = install(&mut driver, 2);
    let parent = driver.insert(None, 1).unwrap();
    driver.begin(parent).unwrap();
    assert_eq!(driver.step(parent), Ok(Outcome::Advanced));
    let external = driver.insert(None, 0).unwrap();
    assert_eq!(external, 2);
    assert_eq!(
        driver.step(parent),
        Ok(Outcome::Child {
            child: 3,
            finished: false
        })
    );
    assert_eq!(driver.step(parent), Ok(Outcome::Finished));
    assert_eq!(driver.read(old_service, key()), Some(7 ^ 5 ^ 3));
    driver.begin(3).unwrap();
    driver.step(3).unwrap();
    driver.retire(3).unwrap();
    assert_eq!(driver.remove(3), Err(DriverError::Retained));
    driver.retire(old_service).unwrap();
    driver.depart(old_service).unwrap();
    assert_eq!(
        driver.unload(old_service),
        Err(DriverError::Kernel(Error::Relied))
    );
    driver.depart(parent).unwrap();
    driver.unload(parent).unwrap();
    assert_eq!(driver.read(old_service, key()), Some(7));
    driver.depart(3).unwrap();
    driver.unload(3).unwrap();
    driver.remove(3).unwrap();
    driver.unload(old_service).unwrap();
    driver.remove(old_service).unwrap();
    let new_service = install(&mut driver, 2);
    assert_eq!(new_service, 4);
    assert!(!driver.retired(parent));
    driver.begin(parent).unwrap();
    driver.step(parent).unwrap();
    assert_eq!(driver.insert(None, 0), Ok(5));
    assert_eq!(
        driver.step(parent),
        Ok(Outcome::Child {
            child: 6,
            finished: false
        })
    );
    driver.step(parent).unwrap();
    assert_eq!(driver.read(new_service, key()), Some(7 ^ 5 ^ 3));
    assert_eq!(driver.phase(3), None);
    assert!(!driver.retired(6));
    driver.retire(new_service).unwrap();
    driver.depart(new_service).unwrap();
    driver.depart(parent).unwrap();
    driver.unload(parent).unwrap();
    assert_eq!(driver.read(new_service, key()), Some(7));
    assert!(driver.retired(6));
    driver.remove(6).unwrap();
    assert_eq!(driver.phase(external), Some(Phase::Inactive));
}

#[test]
fn actual_script_refinement_covers_both_births_in_one_fixed_program_history() {
    use Command::*;
    let commands = [
        Insert {
            parent: None,
            blueprint: 2,
        },
        Begin { actor: 0 },
        Step { actor: 0 },
        Insert {
            parent: None,
            blueprint: 1,
        },
        Begin { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 },
        Retire { actor: 0 },
        Depart { actor: 0 },
        Depart { actor: 1 },
        Unload { actor: 1 },
        Remove { actor: 2 },
        Unload { actor: 0 },
        Remove { actor: 0 },
        Insert {
            parent: None,
            blueprint: 2,
        },
        Begin { actor: 3 },
        Step { actor: 3 },
        Begin { actor: 1 },
        Step { actor: 1 },
        Insert {
            parent: None,
            blueprint: 0,
        },
        Step { actor: 1 },
        Step { actor: 1 },
        Retire { actor: 3 },
        Depart { actor: 3 },
        Depart { actor: 1 },
        Unload { actor: 1 },
        Remove { actor: 5 },
        Unload { actor: 3 },
        Remove { actor: 3 },
    ];
    let report = run_script(vec![leaf(), parent(), provider()], &commands);
    assert_eq!(report.error, None);
    assert_eq!(report.transitions.len(), commands.len());
    assert_eq!(
        report.transitions[6],
        Transition::Step {
            actor: 1,
            outcome: Outcome::Child {
                child: 2,
                finished: false
            }
        }
    );
    assert_eq!(
        report.transitions[21],
        Transition::Step {
            actor: 1,
            outcome: Outcome::Child {
                child: 5,
                finished: false
            }
        }
    );
    assert_eq!(report.machine.phase(1), Some(Phase::Inactive));
    assert_eq!(report.machine.inverse_count(1), Some(0));
    assert!(!report.machine.retired(1));
    assert_eq!(report.machine.phase(2), None);
    assert_eq!(report.machine.phase(5), None);
    assert_eq!(report.machine.phase(4), Some(Phase::Inactive));
}

#[test]
fn failed_terminal_birth_rolls_back_allocator_and_prior_journal() {
    let prior_key = Port { key: 8, realm: 3 };
    let incomplete = Blueprint::new(
        vec![],
        vec![key(), prior_key],
        vec![
            Instruction::Provide {
                key: prior_key,
                value: 55,
                next: Some(1),
            },
            Instruction::Child {
                blueprint: 0,
                next: None,
            },
        ],
    );
    let mut driver = FreshDriver::new(vec![leaf(), incomplete]);
    let actor = driver.insert(None, 1).unwrap();
    driver.begin(actor).unwrap();
    assert_eq!(driver.step(actor), Ok(Outcome::Advanced));
    assert_eq!(driver.step(actor), Err(DriverError::IncompleteProvision));
    assert_eq!(driver.phase(actor), Some(Phase::Loading));
    assert_eq!(driver.inverse_count(actor), Some(1));
    assert_eq!(driver.read(actor, key()), None);
    assert_eq!(driver.read(actor, prior_key), Some(55));
    assert_eq!(driver.phase(1), None);
    assert_eq!(driver.step(actor), Err(DriverError::IncompleteProvision));
    assert_eq!(driver.inverse_count(actor), Some(1));
    assert_eq!(driver.read(actor, prior_key), Some(55));
    assert_eq!(driver.insert(None, 0), Ok(1));
}

#[test]
fn checked_blueprint_dag_and_continuation_failures_do_not_consume_ids() {
    let cycle = Blueprint::new(
        vec![],
        vec![],
        vec![Instruction::Child {
            blueprint: 1,
            next: None,
        }],
    );
    let backwards = Blueprint::new(
        vec![],
        vec![],
        vec![Instruction::Child {
            blueprint: 0,
            next: Some(0),
        }],
    );
    let outside = Blueprint::new(
        vec![],
        vec![],
        vec![Instruction::Child {
            blueprint: 0,
            next: Some(2),
        }],
    );
    for invalid in [cycle, backwards, outside] {
        let mut driver = FreshDriver::new(vec![leaf(), invalid]);
        assert_eq!(driver.insert(None, 1), Err(DriverError::InvalidInstruction));
        assert_eq!(driver.insert(None, 99), Err(DriverError::InvalidBlueprint));
        assert_eq!(driver.insert(None, 0), Ok(0));
    }
}

#[test]
fn loading_drift_aborts_before_allocating_or_recording_a_child() {
    let mut driver = FreshDriver::new(vec![leaf(), parent(), provider()]);
    let service = install(&mut driver, 2);
    let parent = driver.insert(None, 1).unwrap();
    driver.begin(parent).unwrap();
    driver.step(parent).unwrap();
    driver.retire(service).unwrap();
    driver.depart(service).unwrap();
    assert_eq!(
        driver.step(parent),
        Err(DriverError::Kernel(Error::Changed))
    );
    assert_eq!(driver.inverse_count(parent), Some(1));
    assert_eq!(driver.read(service, key()), Some(7 ^ 5));
    assert_eq!(driver.phase(2), None);
    driver.depart(parent).unwrap();
    driver.unload(parent).unwrap();
    assert_eq!(driver.read(service, key()), Some(7));
    assert_eq!(driver.insert(None, 0), Ok(2));
}

#[test]
fn script_stops_at_strict_failure_and_preserves_complete_successful_prefix() {
    let report = run_script(
        vec![leaf(), parent(), provider()],
        &[
            Command::Insert {
                parent: None,
                blueprint: 2,
            },
            Command::Begin { actor: 0 },
            Command::Step { actor: 0 },
            Command::Insert {
                parent: None,
                blueprint: 1,
            },
            Command::Begin { actor: 1 },
            Command::Step { actor: 1 },
            Command::Step { actor: 1 },
            Command::Step { actor: 1 },
            Command::Retire { actor: 2 },
            Command::Remove { actor: 2 },
            Command::Retire { actor: 1 },
        ],
    );
    assert_eq!(report.error, Some(DriverError::Retained));
    assert_eq!(report.transitions.len(), 9);
    assert_eq!(report.machine.inverse_count(1), Some(3));
    assert_eq!(report.machine.read(0, key()), Some(7 ^ 5 ^ 3));
    assert_eq!(report.machine.phase(1), Some(Phase::Active));
    assert!(!report.machine.retired(1));
}

#[test]
fn allocation_keeps_the_selected_nonzero_child_blueprint() {
    let child_key = Port { key: 99, realm: 3 };
    let child = Blueprint::new(
        vec![],
        vec![child_key],
        vec![Instruction::Provide {
            key: child_key,
            value: 42,
            next: None,
        }],
    );
    let parent = Blueprint::new(
        vec![],
        vec![],
        vec![Instruction::Child {
            blueprint: 1,
            next: None,
        }],
    );
    let mut driver = FreshDriver::new(vec![leaf(), child, parent]);
    let owner = driver.insert(None, 2).unwrap();
    driver.begin(owner).unwrap();
    assert_eq!(
        driver.step(owner),
        Ok(Outcome::Child {
            child: 1,
            finished: true
        })
    );
    driver.begin(1).unwrap();
    assert_eq!(driver.step(1), Ok(Outcome::Finished));
    assert_eq!(driver.read(1, child_key), Some(42));
}

#[test]
fn terminal_provision_must_fill_the_last_missing_slot_and_failure_keeps_prior_steps() {
    let first = Port { key: 80, realm: 3 };
    let last = Port { key: 81, realm: 3 };
    let missing = Port { key: 82, realm: 3 };
    for leave_missing in [false, true] {
        let mut provisions = vec![first, last];
        if leave_missing {
            provisions.push(missing);
        }
        let blueprint = Blueprint::new(
            vec![],
            provisions,
            vec![
                Instruction::Provide {
                    key: first,
                    value: 10,
                    next: Some(1),
                },
                Instruction::Provide {
                    key: last,
                    value: 20,
                    next: None,
                },
            ],
        );
        let mut driver = FreshDriver::new(vec![blueprint]);
        let actor = driver.insert(None, 0).unwrap();
        driver.begin(actor).unwrap();
        assert_eq!(driver.step(actor), Ok(Outcome::Advanced));
        assert_eq!(driver.read(actor, first), Some(10));
        assert_eq!(driver.phase(actor), Some(Phase::Loading));
        assert_eq!(driver.inverse_count(actor), Some(1));
        if leave_missing {
            assert_eq!(driver.step(actor), Err(DriverError::IncompleteProvision));
            assert_eq!(driver.read(actor, last), None);
            assert_eq!(driver.read(actor, first), Some(10));
            assert_eq!(driver.read(actor, missing), None);
            assert_eq!(driver.phase(actor), Some(Phase::Loading));
            assert_eq!(driver.inverse_count(actor), Some(1));
            assert_eq!(driver.step(actor), Err(DriverError::IncompleteProvision));
        } else {
            assert_eq!(driver.step(actor), Ok(Outcome::Finished));
            assert_eq!(driver.read(actor, last), Some(20));
            assert_eq!(driver.phase(actor), Some(Phase::Active));
            assert_eq!(driver.inverse_count(actor), Some(2));
        }
    }
}

#[test]
fn fresh_child_retries_after_reservation_removal_without_consuming_an_id_on_failure() {
    let child_key = Port { key: 90, realm: 3 };
    let child = Blueprint::new(
        vec![],
        vec![child_key],
        vec![Instruction::Provide {
            key: child_key,
            value: 42,
            next: None,
        }],
    );
    let parent = Blueprint::new(
        vec![],
        vec![],
        vec![Instruction::Child {
            blueprint: 0,
            next: None,
        }],
    );
    let mut driver = FreshDriver::new(vec![child, parent]);
    let owner = driver.insert(None, 1).unwrap();
    driver.begin(owner).unwrap();
    let reservation = driver.insert(None, 0).unwrap();
    assert_eq!(reservation, 1);
    assert_eq!(driver.read(reservation, child_key), None);
    assert_eq!(
        driver.step(owner),
        Err(DriverError::Kernel(Error::Conflict))
    );
    assert_eq!(driver.phase(owner), Some(Phase::Loading));
    assert_eq!(driver.inverse_count(owner), Some(0));
    assert_eq!(driver.phase(2), None);
    driver.retire(reservation).unwrap();
    assert_eq!(
        driver.step(owner),
        Err(DriverError::Kernel(Error::Conflict))
    );
    driver.remove(reservation).unwrap();
    assert_eq!(
        driver.step(owner),
        Ok(Outcome::Child {
            child: 2,
            finished: true,
        })
    );
    assert_eq!(driver.inverse_count(owner), Some(1));
    assert_eq!(driver.phase(owner), Some(Phase::Active));
    driver.begin(2).unwrap();
    assert_eq!(driver.step(2), Ok(Outcome::Finished));
    assert_eq!(driver.read(2, child_key), Some(42));
}

#[test]
fn run_until_blocked_follows_jumps_and_runs_xor_child_and_last_provision() {
    let published = Port { key: 83, realm: 3 };
    let program = Blueprint::new(
        vec![key()],
        vec![published],
        vec![
            Instruction::Xor {
                key: key(),
                mask: 5,
                next: Some(2),
            },
            Instruction::Provide {
                key: published,
                value: 999,
                next: None,
            },
            Instruction::Child {
                blueprint: 0,
                next: Some(3),
            },
            Instruction::Provide {
                key: published,
                value: 42,
                next: None,
            },
        ],
    );
    let mut driver = FreshDriver::new(vec![leaf(), program, provider()]);
    let service = install(&mut driver, 2);
    let actor = driver.insert(None, 1).unwrap();
    driver.begin(actor).unwrap();
    let external = driver.insert(None, 0).unwrap();
    assert_eq!(external, 2);

    let report = driver.run_until_blocked(actor);
    assert_eq!(report.steps, 3);
    assert_eq!(report.error, None);
    assert_eq!(driver.phase(actor), Some(Phase::Active));
    assert_eq!(driver.read(service, key()), Some(7 ^ 5));
    assert_eq!(driver.read(actor, published), Some(42));
    assert_eq!(driver.inverse_count(actor), Some(3));
    assert_eq!(driver.phase(3), Some(Phase::Inactive));
    assert_eq!(driver.inverse_count(3), Some(0));
    assert_eq!(driver.phase(4), None);
    assert_eq!(driver.phase(external), Some(Phase::Inactive));
}

#[test]
fn run_until_blocked_keeps_and_recovers_the_prefix_before_a_missing_value() {
    let missing = Port { key: 84, realm: 3 };
    let program = Blueprint::new(
        vec![key()],
        vec![missing],
        vec![
            Instruction::Xor {
                key: key(),
                mask: 5,
                next: Some(1),
            },
            Instruction::Child {
                blueprint: 0,
                next: Some(2),
            },
            Instruction::Xor {
                key: missing,
                mask: 1,
                next: None,
            },
        ],
    );
    let mut driver = FreshDriver::new(vec![leaf(), program, provider()]);
    let service = install(&mut driver, 2);
    let actor = driver.insert(None, 1).unwrap();
    driver.begin(actor).unwrap();

    let report = driver.run_until_blocked(actor);
    assert_eq!(report.steps, 2);
    assert_eq!(report.error, Some(DriverError::MissingValue));
    assert_eq!(driver.phase(actor), Some(Phase::Loading));
    assert_eq!(driver.read(service, key()), Some(7 ^ 5));
    assert_eq!(driver.read(actor, missing), None);
    assert_eq!(driver.inverse_count(actor), Some(2));
    assert_eq!(driver.phase(2), Some(Phase::Inactive));

    let retry = driver.run_until_blocked(actor);
    assert_eq!(retry.steps, 0);
    assert_eq!(retry.error, Some(DriverError::MissingValue));
    assert_eq!(driver.read(service, key()), Some(7 ^ 5));
    assert_eq!(driver.inverse_count(actor), Some(2));
    assert_eq!(driver.insert(None, 0), Ok(3));

    driver.retire(service).unwrap();
    driver.depart(service).unwrap();
    driver.depart(actor).unwrap();
    driver.unload(actor).unwrap();
    assert_eq!(driver.read(service, key()), Some(7));
    assert_eq!(driver.phase(actor), Some(Phase::Inactive));
    assert_eq!(driver.inverse_count(actor), Some(0));
    assert!(driver.retired(2));
    driver.remove(2).unwrap();
    assert_eq!(driver.phase(3), Some(Phase::Inactive));
}

#[test]
fn run_until_blocked_rolls_back_a_terminal_child_but_keeps_prior_provision() {
    let saved = Port { key: 85, realm: 3 };
    let missing = Port { key: 86, realm: 3 };
    let program = Blueprint::new(
        vec![],
        vec![saved, missing],
        vec![
            Instruction::Provide {
                key: saved,
                value: 55,
                next: Some(1),
            },
            Instruction::Child {
                blueprint: 0,
                next: None,
            },
        ],
    );
    let mut driver = FreshDriver::new(vec![leaf(), program]);
    let actor = driver.insert(None, 1).unwrap();
    driver.begin(actor).unwrap();

    let report = driver.run_until_blocked(actor);
    assert_eq!(report.steps, 1);
    assert_eq!(report.error, Some(DriverError::IncompleteProvision));
    assert_eq!(driver.phase(actor), Some(Phase::Loading));
    assert_eq!(driver.inverse_count(actor), Some(1));
    assert_eq!(driver.read(actor, saved), Some(55));
    assert_eq!(driver.read(actor, missing), None);
    assert_eq!(driver.phase(1), None);
    let retry = driver.run_until_blocked(actor);
    assert_eq!(retry.steps, 0);
    assert_eq!(retry.error, Some(DriverError::IncompleteProvision));
    assert_eq!(driver.inverse_count(actor), Some(1));
    assert_eq!(driver.read(actor, saved), Some(55));
    assert_eq!(driver.insert(None, 0), Ok(1));
}

#[test]
fn run_until_blocked_counts_implicit_unit_after_empty_code_and_a_jump_to_the_end() {
    let published = Port { key: 87, realm: 3 };
    let empty = Blueprint::new(vec![], vec![], vec![]);
    let jump = Blueprint::new(
        vec![],
        vec![published],
        vec![
            Instruction::Provide {
                key: published,
                value: 33,
                next: Some(3),
            },
            Instruction::Provide {
                key: published,
                value: 999,
                next: None,
            },
            Instruction::Xor {
                key: published,
                mask: 7,
                next: None,
            },
        ],
    );
    let mut driver = FreshDriver::new(vec![empty, jump]);
    let empty_actor = driver.insert(None, 0).unwrap();
    driver.begin(empty_actor).unwrap();
    let empty_report = driver.run_until_blocked(empty_actor);
    assert_eq!(empty_report.steps, 1);
    assert_eq!(empty_report.error, None);
    assert_eq!(driver.phase(empty_actor), Some(Phase::Active));
    assert_eq!(driver.inverse_count(empty_actor), Some(1));

    let actor = driver.insert(None, 1).unwrap();
    driver.begin(actor).unwrap();
    let report = driver.run_until_blocked(actor);
    assert_eq!(report.steps, 2);
    assert_eq!(report.error, None);
    assert_eq!(driver.read(actor, published), Some(33));
    assert_eq!(driver.phase(actor), Some(Phase::Active));
    assert_eq!(driver.inverse_count(actor), Some(2));
}

#[test]
fn run_until_blocked_preserves_step_errors_for_unknown_inactive_and_active_actors() {
    let mut driver = FreshDriver::new(vec![leaf()]);
    let actor = driver.insert(None, 0).unwrap();
    let unknown = driver.run_until_blocked(99);
    assert_eq!(unknown.steps, 0);
    assert_eq!(unknown.error, Some(DriverError::Unknown));
    assert_eq!(driver.phase(actor), Some(Phase::Inactive));
    assert_eq!(driver.inverse_count(actor), Some(0));

    let inactive = driver.run_until_blocked(actor);
    assert_eq!(inactive.steps, 0);
    assert_eq!(
        inactive.error,
        Some(DriverError::Kernel(Error::InvalidState))
    );
    driver.begin(actor).unwrap();
    let completed = driver.run_until_blocked(actor);
    assert_eq!(completed.steps, 1);
    assert_eq!(completed.error, None);
    let active = driver.run_until_blocked(actor);
    assert_eq!(active.steps, 0);
    assert_eq!(active.error, Some(DriverError::Kernel(Error::InvalidState)));
    assert_eq!(driver.phase(actor), Some(Phase::Active));
    assert_eq!(driver.inverse_count(actor), Some(1));
}

#[test]
fn run_until_blocked_stops_after_a_terminal_child_without_running_the_child() {
    let parent = Blueprint::new(
        vec![],
        vec![],
        vec![Instruction::Child {
            blueprint: 0,
            next: None,
        }],
    );
    let mut driver = FreshDriver::new(vec![leaf(), parent]);
    let actor = driver.insert(None, 1).unwrap();
    driver.begin(actor).unwrap();
    let report = driver.run_until_blocked(actor);
    assert_eq!(report.steps, 1);
    assert_eq!(report.error, None);
    assert_eq!(driver.phase(actor), Some(Phase::Active));
    assert_eq!(driver.inverse_count(actor), Some(1));
    assert_eq!(driver.phase(1), Some(Phase::Inactive));
    assert_eq!(driver.inverse_count(1), Some(0));
    assert_eq!(driver.phase(2), None);
}
