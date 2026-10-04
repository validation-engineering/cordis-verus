use cordis_kernel::mixed_driver::fresh::{
    run_script, Blueprint, Command, DriverError, FreshDriver, Instruction, Outcome,
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
        report.transitions[6].outcome,
        Some(Outcome::Child {
            child: 2,
            finished: false
        })
    );
    assert_eq!(
        report.transitions[21].outcome,
        Some(Outcome::Child {
            child: 5,
            finished: false
        })
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
