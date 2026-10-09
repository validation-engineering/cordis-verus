use cordis_kernel::mixed_driver::{Blueprint, DriverError, Instruction, MixedDriver, Outcome};
use cordis_kernel::{Error, Phase, Port};

fn key() -> Port {
    Port { key: 7, realm: 3 }
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

fn consumer(mask: u64) -> Blueprint {
    Blueprint::new(
        vec![key()],
        vec![],
        vec![Instruction::Xor {
            key: key(),
            mask,
            next: None,
        }],
    )
}

fn install(driver: &mut MixedDriver, blueprint: usize) -> usize {
    let id = driver.insert(None, blueprint).unwrap();
    driver.begin(id).unwrap();
    assert_eq!(driver.step(id), Ok(Outcome::Finished));
    id
}

#[test]
fn two_consumers_share_actual_provider_and_remove_only_their_own_effects() {
    let mut driver = MixedDriver::new(vec![provider(), consumer(5), consumer(3)]);
    let service = install(&mut driver, 0);
    let a = install(&mut driver, 1);
    let b = install(&mut driver, 2);
    assert_eq!(driver.read(service, key()), Some(7 ^ 5 ^ 3));
    driver.retire(a).unwrap();
    driver.depart(a).unwrap();
    driver.unload(a).unwrap();
    assert_eq!(driver.read(service, key()), Some(7 ^ 3));
    assert_eq!(driver.phase(b), Some(Phase::Active));
    assert_eq!(driver.inverse_count(b), Some(1));
    driver.retire(b).unwrap();
    driver.depart(b).unwrap();
    driver.unload(b).unwrap();
    assert_eq!(driver.read(service, key()), Some(7));
}

#[test]
fn relied_provider_cleanup_is_atomic_and_consumers_keep_their_captured_provider() {
    let mut driver = MixedDriver::new(vec![provider(), consumer(5)]);
    let service = install(&mut driver, 0);
    let client = install(&mut driver, 1);
    driver.retire(service).unwrap();
    driver.depart(service).unwrap();
    assert_eq!(
        driver.unload(service),
        Err(DriverError::Kernel(Error::Relied))
    );
    assert_eq!(driver.phase(service), Some(Phase::Unloading));
    assert_eq!(driver.read(service, key()), Some(7 ^ 5));
    assert_eq!(driver.inverse_count(service), Some(1));
    assert_eq!(driver.inverse_count(client), Some(1));
    driver.depart(client).unwrap();
    driver.unload(client).unwrap();
    assert_eq!(driver.read(service, key()), Some(7));
    driver.unload(service).unwrap();
    assert_eq!(driver.read(service, key()), None);
}

#[test]
fn one_real_lifo_journal_interleaves_foreign_payload_and_actual_child_receipts() {
    let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let mixed = Blueprint::new(
        vec![key()],
        vec![],
        vec![
            Instruction::Xor {
                key: key(),
                mask: 5,
                next: Some(1),
            },
            Instruction::Child {
                expected: 2,
                blueprint: 0,
                next: Some(2),
            },
            Instruction::Xor {
                key: key(),
                mask: 3,
                next: None,
            },
        ],
    );
    let mut driver = MixedDriver::new(vec![leaf, mixed, provider()]);
    let service = install(&mut driver, 2);
    let parent = driver.insert(None, 1).unwrap();
    driver.begin(parent).unwrap();
    assert_eq!(driver.step(parent), Ok(Outcome::Advanced));
    assert_eq!(
        driver.step(parent),
        Ok(Outcome::Child {
            child: 2,
            finished: false
        })
    );
    assert_eq!(driver.step(parent), Ok(Outcome::Finished));
    assert_eq!(driver.inverse_count(parent), Some(3));
    assert_eq!(driver.read(service, key()), Some(7 ^ 5 ^ 3));
    driver.begin(2).unwrap();
    driver.step(2).unwrap();
    driver.retire(2).unwrap();
    assert_eq!(driver.remove(2), Err(DriverError::Retained));
    driver.retire(parent).unwrap();
    driver.depart(parent).unwrap();
    driver.unload(parent).unwrap();
    assert_eq!(driver.read(service, key()), Some(7));
    assert_eq!(driver.inverse_count(parent), Some(0));
    assert!(driver.retired(2));
    assert_eq!(driver.phase(2), Some(Phase::Active));
    driver.depart(2).unwrap();
    driver.unload(2).unwrap();
    driver.remove(2).unwrap();
    driver.remove(parent).unwrap();
}

#[test]
fn expected_child_mismatch_keeps_prior_shared_effect_and_instruction_pending() {
    let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let parent = Blueprint::new(
        vec![key()],
        vec![],
        vec![
            Instruction::Xor {
                key: key(),
                mask: 5,
                next: Some(1),
            },
            Instruction::Child {
                expected: 99,
                blueprint: 0,
                next: None,
            },
        ],
    );
    let mut driver = MixedDriver::new(vec![leaf, parent, provider()]);
    let service = install(&mut driver, 2);
    let parent = driver.insert(None, 1).unwrap();
    driver.begin(parent).unwrap();
    driver.step(parent).unwrap();
    for _ in 0..2 {
        assert_eq!(driver.step(parent), Err(DriverError::UnexpectedChild));
        assert_eq!(driver.read(service, key()), Some(7 ^ 5));
        assert_eq!(driver.phase(parent), Some(Phase::Loading));
        assert_eq!(driver.inverse_count(parent), Some(1));
    }
    assert_eq!(driver.insert(None, 0), Ok(2));
}

#[test]
fn terminal_failure_discards_both_new_child_and_uncommitted_payload() {
    let second = Port { key: 8, realm: 3 };
    let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let parent = Blueprint::new(
        vec![],
        vec![key()],
        vec![Instruction::Child {
            expected: 1,
            blueprint: 0,
            next: None,
        }],
    );
    let incomplete = Blueprint::new(
        vec![],
        vec![second, key()],
        vec![Instruction::Provide {
            key: second,
            value: 99,
            next: None,
        }],
    );
    let mut driver = MixedDriver::new(vec![leaf, parent, incomplete]);
    let parent = driver.insert(None, 1).unwrap();
    driver.begin(parent).unwrap();
    assert_eq!(driver.step(parent), Err(DriverError::IncompleteProvision));
    assert_eq!(driver.phase(1), None);
    assert_eq!(driver.inverse_count(parent), Some(0));
    assert_eq!(driver.insert(None, 0), Ok(1));
    let mut payload = MixedDriver::new(vec![
        provider(),
        Blueprint::new(
            vec![],
            vec![key(), second],
            vec![Instruction::Provide {
                key: key(),
                value: 99,
                next: None,
            }],
        ),
    ]);
    let owner = payload.insert(None, 1).unwrap();
    payload.begin(owner).unwrap();
    assert_eq!(payload.step(owner), Err(DriverError::IncompleteProvision));
    assert_eq!(payload.read(owner, key()), None);
    assert_eq!(payload.inverse_count(owner), Some(0));
}

#[test]
fn missing_payload_is_a_failure_and_never_an_identity_operation() {
    let mut driver = MixedDriver::new(vec![Blueprint::new(
        vec![],
        vec![key()],
        vec![Instruction::Xor {
            key: key(),
            mask: 5,
            next: None,
        }],
    )]);
    let actor = driver.insert(None, 0).unwrap();
    driver.begin(actor).unwrap();
    assert_eq!(driver.step(actor), Err(DriverError::MissingValue));
    assert_eq!(driver.read(actor, key()), None);
    assert_eq!(driver.inverse_count(actor), Some(0));
}

#[test]
fn invalid_code_and_recursive_blueprints_do_not_consume_an_identity() {
    for instruction in [
        Instruction::Xor {
            key: key(),
            mask: 1,
            next: Some(0),
        },
        Instruction::Xor {
            key: key(),
            mask: 1,
            next: Some(2),
        },
        Instruction::Child {
            expected: 1,
            blueprint: 0,
            next: None,
        },
    ] {
        let invalid = Blueprint::new(vec![key()], vec![], vec![instruction]);
        let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
        let mut driver = MixedDriver::new(vec![invalid, leaf]);
        assert_eq!(driver.insert(None, 0), Err(DriverError::InvalidInstruction));
        assert_eq!(driver.phase(0), None);
        // The prefix validator intentionally also rejects a blueprint whose
        // lower-ranked bank contains invalid code.
        assert_eq!(driver.insert(None, 1), Err(DriverError::InvalidInstruction));
    }
    let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let invalid = Blueprint::new(
        vec![],
        vec![],
        vec![Instruction::Child {
            expected: 1,
            blueprint: 1,
            next: None,
        }],
    );
    let mut driver = MixedDriver::new(vec![leaf, invalid]);
    assert_eq!(driver.insert(None, 1), Err(DriverError::InvalidInstruction));
    assert_eq!(driver.insert(None, 0), Ok(0));
}

#[test]
fn changed_target_aborts_a_synchronous_loading_stage_without_landing_it() {
    let code = Blueprint::new(
        vec![key()],
        vec![],
        vec![
            Instruction::Xor {
                key: key(),
                mask: 5,
                next: Some(1),
            },
            Instruction::Xor {
                key: key(),
                mask: 3,
                next: None,
            },
        ],
    );
    let mut driver = MixedDriver::new(vec![provider(), code]);
    let service = install(&mut driver, 0);
    let client = driver.insert(None, 1).unwrap();
    driver.begin(client).unwrap();
    driver.step(client).unwrap();
    driver.retire(service).unwrap();
    driver.depart(service).unwrap();
    assert_eq!(
        driver.step(client),
        Err(DriverError::Kernel(Error::Changed))
    );
    assert_eq!(driver.read(service, key()), Some(7 ^ 5));
    assert_eq!(driver.inverse_count(client), Some(1));
    assert_eq!(driver.phase(client), Some(Phase::Loading));
    driver.depart(client).unwrap();
    driver.unload(client).unwrap();
    assert_eq!(driver.read(service, key()), Some(7));
    assert_eq!(driver.phase(client), Some(Phase::Inactive));
}

#[test]
fn fixed_child_name_profile_rejects_a_second_activation_with_a_new_allocator() {
    let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let parent = Blueprint::new(
        vec![key()],
        vec![],
        vec![Instruction::Child {
            expected: 2,
            blueprint: 0,
            next: None,
        }],
    );
    let mut driver = MixedDriver::new(vec![leaf, parent, provider()]);
    let service = install(&mut driver, 2);
    let owner = driver.insert(None, 1).unwrap();
    driver.begin(owner).unwrap();
    assert_eq!(
        driver.step(owner),
        Ok(Outcome::Child {
            child: 2,
            finished: true
        })
    );
    driver.retire(service).unwrap();
    driver.depart(service).unwrap();
    driver.depart(owner).unwrap();
    driver.unload(owner).unwrap();
    driver.unload(service).unwrap();
    driver.remove(service).unwrap();
    assert_eq!(install(&mut driver, 2), 3);
    driver.begin(owner).unwrap();
    assert_eq!(driver.step(owner), Err(DriverError::UnexpectedChild));
    assert_eq!(driver.inverse_count(owner), Some(0));
    assert_eq!(driver.phase(owner), Some(Phase::Loading));
    assert!(driver.retired(2));
}

#[test]
fn verified_script_entry_runs_shared_payload_child_restore_and_strict_failure_prefix() {
    use cordis_kernel::mixed_driver::{run_script, Command};
    let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let mixed = Blueprint::new(
        vec![key()],
        vec![],
        vec![
            Instruction::Xor {
                key: key(),
                mask: 5,
                next: Some(1),
            },
            Instruction::Child {
                expected: 2,
                blueprint: 0,
                next: Some(2),
            },
            Instruction::Xor {
                key: key(),
                mask: 3,
                next: None,
            },
        ],
    );
    let commands = vec![
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
        Command::Insert {
            parent: None,
            blueprint: 3,
        },
        Command::Begin { actor: 3 },
        Command::Step { actor: 3 },
        Command::Begin { actor: 2 },
        Command::Step { actor: 2 },
        Command::Retire { actor: 1 },
        Command::Depart { actor: 1 },
        Command::Unload { actor: 1 },
        Command::Depart { actor: 2 },
        Command::Unload { actor: 2 },
        Command::Remove { actor: 2 },
        Command::Remove { actor: 1 },
        Command::Remove { actor: 0 },
        Command::Retire { actor: 3 },
    ];
    let report = run_script(vec![leaf, mixed, provider(), consumer(8)], &commands);
    assert_eq!(report.error, Some(DriverError::NonemptyTable));
    assert_eq!(report.transitions.len(), 20);
    for (transition, command) in report.transitions.iter().zip(&commands) {
        assert_eq!(transition.command(), *command);
    }
    assert_eq!(report.machine.read(0, key()), Some(7 ^ 8));
    assert_eq!(report.machine.phase(1), None);
    assert_eq!(report.machine.phase(2), None);
    assert_eq!(report.machine.phase(3), Some(Phase::Active));
    assert!(!report.machine.retired(3));
}

#[test]
fn insertion_checks_raw_declarations_and_preserves_validation_priority() {
    let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let duplicate_dependencies =
        Blueprint::new(vec![key(), key()], vec![], vec![Instruction::Unit]);
    let duplicate_provisions = Blueprint::new(vec![], vec![key(), key()], vec![Instruction::Unit]);
    let missing_dependency = Blueprint::new(vec![key()], vec![], vec![Instruction::Unit]);
    let mut driver = MixedDriver::new(vec![
        leaf,
        duplicate_dependencies,
        duplicate_provisions,
        missing_dependency,
    ]);

    // Blueprint checks happen before the kernel's parent/declaration checks.
    assert_eq!(
        driver.insert(Some(99), 4),
        Err(DriverError::InvalidBlueprint)
    );
    assert_eq!(
        driver.insert(Some(99), 2),
        Err(DriverError::InvalidBlueprint)
    );
    assert_eq!(
        driver.insert(Some(99), 1),
        Err(DriverError::Kernel(Error::Unknown))
    );
    assert_eq!(
        driver.insert(None, 1),
        Err(DriverError::Kernel(Error::Conflict))
    );
    assert_eq!(driver.phase(0), None);
    assert_eq!(driver.inverse_count(0), None);

    // Registration checks declarations, not whether dependencies can activate.
    assert_eq!(driver.insert(None, 3), Ok(0));
    assert_eq!(driver.phase(0), Some(Phase::Inactive));
    driver.retire(0).unwrap();
    assert_eq!(driver.insert(Some(0), 0), Ok(1));
    assert_eq!(driver.phase(1), Some(Phase::Inactive));
    assert!(driver.retired(0));
}

#[test]
fn insertion_reservations_include_realm_and_survive_retirement_until_removal() {
    let other_realm = Port { key: 7, realm: 4 };
    let mut driver = MixedDriver::new(vec![
        Blueprint::new(vec![], vec![key()], vec![Instruction::Unit]),
        Blueprint::new(vec![], vec![other_realm], vec![Instruction::Unit]),
    ]);
    let owner = driver.insert(None, 0).unwrap();
    assert_eq!(owner, 0);
    driver.retire(owner).unwrap();
    assert_eq!(
        driver.insert(None, 0),
        Err(DriverError::Kernel(Error::Conflict))
    );
    assert_eq!(driver.phase(owner), Some(Phase::Inactive));
    assert!(driver.retired(owner));
    assert_eq!(driver.read(owner, key()), None);
    assert_eq!(driver.inverse_count(owner), Some(0));
    assert_eq!(driver.phase(1), None);

    assert_eq!(driver.insert(None, 1), Ok(1));
    driver.remove(owner).unwrap();
    assert_eq!(driver.phase(owner), None);
    assert_eq!(driver.insert(None, 0), Ok(2));
    assert_eq!(driver.phase(1), Some(Phase::Inactive));
    assert_eq!(driver.phase(2), Some(Phase::Inactive));
}
