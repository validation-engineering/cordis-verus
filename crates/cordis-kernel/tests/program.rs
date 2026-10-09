use cordis_kernel::program::{Instruction, Outcome, ProgramEpisode, ProgramError};
use cordis_kernel::Binding;

fn run(program: &mut ProgramEpisode) {
    loop {
        assert!(program.admit(Some(&[])));
        if program.step().unwrap() == Outcome::Finished {
            break;
        }
    }
}

#[test]
fn fixed_program_reads_previous_stage_and_recovers_exactly() {
    let code = vec![
        Instruction::Set {
            index: 0,
            value: 19,
            next: 1,
        },
        Instruction::Copy {
            source: 0,
            index: 1,
            next: 2,
        },
    ];
    let mut program = ProgramEpisode::new(code, vec![3, 7], 42, vec![]).unwrap();
    assert_eq!(program.step(), Err(ProgramError::NotAdmitted));
    run(&mut program);
    assert_eq!(program.read(0), Some(19));
    assert_eq!(program.read(1), Some(19));
    assert_eq!(program.remaining_now(), 0);
    assert!(program.rollback());
    assert_eq!(program.read(0), Some(3));
    assert_eq!(program.read(1), Some(7));
    assert_eq!(program.position_now(), 0);
    assert!(program.restart(vec![]));
    run(&mut program);
    assert_eq!(program.read(1), Some(19));
}

#[test]
fn dynamic_branch_selects_values_and_continuation_from_entry_context() {
    for (entry, expected, next) in [(5, 23, 2), (6, 31, 3)] {
        let mut program = ProgramEpisode::new(
            vec![
                Instruction::BranchWrite {
                    test: 0,
                    expected: 5,
                    index: 0,
                    equal_value: 23,
                    unequal_value: 31,
                    equal_next: 2,
                    unequal_next: 3,
                },
                Instruction::Set {
                    index: 0,
                    value: 99,
                    next: 3,
                },
                Instruction::Copy {
                    source: 0,
                    index: 1,
                    next: 3,
                },
            ],
            vec![entry, 0],
            1,
            vec![],
        )
        .unwrap();
        assert!(program.admit(Some(&[])));
        let rank = program.remaining_now();
        assert_eq!(program.step(), Ok(Outcome::Advanced));
        assert_eq!(program.position_now(), next);
        assert!(program.remaining_now() < rank);
        assert_eq!(program.read(0), Some(expected));
        run(&mut program);
        assert_eq!(program.read(1), Some(if entry == 5 { 23 } else { 0 }));
        assert!(program.rollback());
        assert_eq!(program.read(0), Some(entry));
    }
}

#[test]
fn reject_invalid_indices_and_nonforward_continuations() {
    for instruction in [
        Instruction::Set {
            index: 0,
            value: 1,
            next: 0,
        },
        Instruction::Set {
            index: 0,
            value: 1,
            next: 2,
        },
        Instruction::Copy {
            source: 1,
            index: 0,
            next: 1,
        },
        Instruction::BranchWrite {
            test: 0,
            expected: 0,
            index: 0,
            equal_value: 1,
            unequal_value: 2,
            equal_next: 1,
            unequal_next: 0,
        },
    ] {
        assert!(matches!(
            ProgramEpisode::new(vec![instruction], vec![0], 0, vec![]),
            Err(ProgramError::InvalidInstruction)
        ));
    }
}

#[test]
fn cancellation_retains_admitted_code_stage_and_its_actual_inverse() {
    let binding = Binding {
        key: 7,
        realm: 0,
        provider: 8,
    };
    let mut program = ProgramEpisode::new(
        vec![Instruction::Set {
            index: 0,
            value: 13,
            next: 1,
        }],
        vec![4],
        2,
        vec![binding],
    )
    .unwrap();
    assert!(program.admit(Some(&[binding])));
    program.cancel();
    assert!(!program.rollback());
    assert!(program.is_pending());
    assert_eq!(program.step(), Ok(Outcome::Advanced));
    assert!(program.is_settled());
    assert_eq!(program.read(0), Some(13));
    assert!(program.rollback());
    assert_eq!(program.read(0), Some(4));
}

#[test]
fn absent_target_prevents_starting_a_code_stage() {
    let mut program = ProgramEpisode::new(
        vec![Instruction::Set {
            index: 0,
            value: 13,
            next: 1,
        }],
        vec![4],
        2,
        vec![],
    )
    .unwrap();
    assert!(!program.admit(None));
    assert_eq!(program.step(), Err(ProgramError::NotAdmitted));
    assert_eq!(program.read(0), Some(4));
    assert!(program.is_settled());
    assert!(program.rollback());
}

#[test]
fn empty_program_still_requires_admission_for_terminal_yield() {
    let mut program = ProgramEpisode::new(vec![], vec![9], 0, vec![]).unwrap();
    assert_eq!(program.step(), Err(ProgramError::NotAdmitted));
    assert!(program.admit(Some(&[])));
    assert_eq!(program.step(), Ok(Outcome::Finished));
    assert!(program.rollback());
    assert_eq!(program.read(0), Some(9));
}

use cordis_kernel::program::{ProgramDriver, ProgramDriverError};
use cordis_kernel::{Error, Phase, Port};

fn finish_driver(driver: &mut ProgramDriver, id: usize) {
    loop {
        assert!(driver.admit(id).unwrap());
        if driver.step(id).unwrap() == Outcome::Finished {
            break;
        }
    }
    driver.finish(id).unwrap();
}

#[test]
fn guarded_program_interpreter_recovers_consumers_before_provider() {
    let mut driver = ProgramDriver::new();
    let port = Port { key: 1, realm: 2 };
    let provider = driver
        .insert(
            None,
            vec![],
            vec![port],
            vec![Instruction::Set {
                index: 0,
                value: 99,
                next: 1,
            }],
            vec![0],
            0,
        )
        .unwrap();
    let consumer = driver
        .insert(
            None,
            vec![port],
            vec![Port { key: 2, realm: 2 }],
            vec![Instruction::Set {
                index: 0,
                value: 100,
                next: 1,
            }],
            vec![1],
            1,
        )
        .unwrap();
    driver.begin(provider).unwrap();
    finish_driver(&mut driver, provider);
    driver.begin(consumer).unwrap();
    finish_driver(&mut driver, consumer);
    assert_eq!(driver.read(provider, 0), Some(99));
    assert_eq!(driver.read(consumer, 0), Some(100));
    driver.retire(provider).unwrap();
    driver.depart(provider).unwrap();
    assert_eq!(
        driver.unload(provider),
        Err(ProgramDriverError::Kernel(Error::Relied))
    );
    assert_eq!(driver.read(provider, 0), Some(99));
    driver.depart(consumer).unwrap();
    driver.unload(consumer).unwrap();
    assert_eq!(driver.read(consumer, 0), Some(1));
    driver.unload(provider).unwrap();
    assert_eq!(driver.read(provider, 0), Some(0));
    driver.remove(provider).unwrap();
    assert_eq!(driver.phase(provider), None);
}

#[test]
fn pending_program_stage_lands_after_retirement_and_cannot_publish_early() {
    let mut driver = ProgramDriver::new();
    let id = driver
        .insert(
            None,
            vec![],
            vec![Port { key: 3, realm: 2 }],
            vec![Instruction::Set {
                index: 0,
                value: 12,
                next: 1,
            }],
            vec![3],
            0,
        )
        .unwrap();
    driver.begin(id).unwrap();
    assert_eq!(driver.finish(id), Err(ProgramDriverError::Pending));
    assert!(driver.admit(id).unwrap());
    driver.retire(id).unwrap();
    assert_eq!(driver.depart(id), Err(ProgramDriverError::Pending));
    assert_eq!(driver.step(id), Ok(Outcome::Advanced));
    assert_eq!(driver.read(id, 0), Some(12));
    assert_eq!(driver.finish(id), Err(ProgramDriverError::Pending));
    driver.depart(id).unwrap();
    driver.unload(id).unwrap();
    assert_eq!(driver.phase(id), Some(Phase::Inactive));
    assert_eq!(driver.read(id, 0), Some(3));
}

#[test]
fn invalid_program_is_rejected_before_registry_allocation() {
    let mut driver = ProgramDriver::new();
    assert_eq!(
        driver.insert(
            None,
            vec![],
            vec![Port { key: 3, realm: 2 }],
            vec![Instruction::Set {
                index: 0,
                value: 1,
                next: 0
            }],
            vec![0],
            0
        ),
        Err(ProgramDriverError::Program(
            ProgramError::InvalidInstruction
        ))
    );
    let id = driver
        .insert(None, vec![], vec![], vec![], vec![], 0)
        .unwrap();
    assert_eq!(id, 0);
    driver.begin(id).unwrap();
    finish_driver(&mut driver, id);
    assert_eq!(driver.phase(id), Some(Phase::Active));
}

#[test]
fn mapped_driver_rejects_ambiguous_or_incomplete_layouts() {
    let mut driver = ProgramDriver::new();
    let port = Port { key: 1, realm: 0 };
    assert_eq!(
        driver.insert(None, vec![], vec![], vec![], vec![0], 0),
        Err(ProgramDriverError::InvalidLayout)
    );
    assert_eq!(
        driver.insert(None, vec![], vec![port, port], vec![], vec![0, 0], 0),
        Err(ProgramDriverError::InvalidLayout)
    );
    let id = driver
        .insert(None, vec![], vec![port], vec![], vec![0], 0)
        .unwrap();
    driver.begin(id).unwrap();
    assert!(driver.admit(id).unwrap());
    assert_eq!(driver.step(id), Ok(Outcome::Finished));
    assert_eq!(
        driver.finish(id),
        Err(ProgramDriverError::IncompleteProvision)
    );
    assert_eq!(driver.phase(id), Some(Phase::Loading));
    driver.retire(id).unwrap();
    driver.depart(id).unwrap();
    driver.unload(id).unwrap();
    assert_eq!(driver.read(id, 0), Some(0));
}

#[test]
fn branch_skipping_a_declared_cell_cannot_publish() {
    let mut driver = ProgramDriver::new();
    let id = driver
        .insert(
            None,
            vec![],
            vec![Port { key: 1, realm: 0 }, Port { key: 2, realm: 0 }],
            vec![
                Instruction::BranchWrite {
                    test: 0,
                    expected: 0,
                    index: 0,
                    equal_value: 7,
                    unequal_value: 8,
                    equal_next: 2,
                    unequal_next: 1,
                },
                Instruction::Set {
                    index: 1,
                    value: 9,
                    next: 2,
                },
            ],
            vec![0, 0],
            0,
        )
        .unwrap();
    driver.begin(id).unwrap();
    assert!(driver.admit(id).unwrap());
    assert_eq!(driver.step(id), Ok(Outcome::Advanced));
    assert!(driver.admit(id).unwrap());
    assert_eq!(driver.step(id), Ok(Outcome::Finished));
    assert_eq!(
        driver.finish(id),
        Err(ProgramDriverError::IncompleteProvision)
    );
    assert_eq!(driver.read(id, 0), Some(7));
    assert_eq!(driver.read(id, 1), Some(0));
}

#[test]
fn checked_runner_counts_real_branch_steps_and_recovers_cells() {
    let committed = vec![Binding {
        key: 7,
        realm: 2,
        provider: 9,
    }];
    for (entry, writes, final_value) in [(5, 2, 23), (6, 1, 31)] {
        let code = vec![
            Instruction::BranchWrite {
                test: 0,
                expected: 5,
                index: 0,
                equal_value: 23,
                unequal_value: 31,
                equal_next: 2,
                unequal_next: 3,
            },
            Instruction::Set {
                index: 0,
                value: 99,
                next: 3,
            },
            Instruction::Copy {
                source: 0,
                index: 1,
                next: 3,
            },
        ];
        let values = vec![entry, 0];
        let mut program =
            ProgramEpisode::new(code.clone(), values.clone(), 4, committed.clone()).unwrap();
        let count = program.run_to_completion(&committed).unwrap();
        assert_eq!(count.writes, writes);
        assert_eq!(count.steps, writes as u128 + 1);
        assert!(program.has_ended());
        assert_eq!(program.read(0), Some(final_value));
        assert_eq!(program.read(1), Some(if entry == 5 { 23 } else { 0 }));
        assert_eq!(
            program.run_to_completion(&committed),
            Err(ProgramError::NotAdmitted)
        );
        assert_eq!(program.read(0), Some(final_value));
        assert_eq!(program.read(1), Some(if entry == 5 { 23 } else { 0 }));
        assert!(program.rollback());
        assert_eq!(program.read(0), Some(entry));
        assert_eq!(program.read(1), Some(0));

        let (recovered, recovered_count) =
            ProgramEpisode::execute_and_recover(code, values, 4, committed.clone(), &committed)
                .unwrap();
        assert_eq!(recovered_count, count);
        assert!(recovered.is_settled());
        assert!(!recovered.is_pending());
        assert!(!recovered.has_ended());
        assert_eq!(recovered.position_now(), 0);
        assert_eq!(recovered.read(0), Some(entry));
        assert_eq!(recovered.read(1), Some(0));
    }
}

#[test]
fn checked_client_counts_empty_terminal_step_and_rejects_invalid_domain() {
    let (recovered, count) =
        ProgramEpisode::execute_and_recover(vec![], vec![9], 0, vec![], &[]).unwrap();
    assert_eq!(count.writes, 0);
    assert_eq!(count.steps, 1);
    assert_eq!(recovered.read(0), Some(9));
    assert!(recovered.is_settled());
    assert!(!recovered.is_pending());
    let target = [Binding {
        key: 1,
        realm: 0,
        provider: 2,
    }];
    let code = vec![Instruction::Set {
        index: 0,
        value: 99,
        next: 1,
    }];
    let mut mismatched = ProgramEpisode::new(code.clone(), vec![9], 0, vec![]).unwrap();
    assert_eq!(
        mismatched.run_to_completion(&target),
        Err(ProgramError::NotAdmitted)
    );
    assert_eq!(mismatched.position_now(), 0);
    assert_eq!(mismatched.read(0), Some(9));
    assert!(mismatched.is_settled());
    let mut pending = ProgramEpisode::new(code.clone(), vec![9], 0, vec![]).unwrap();
    assert!(pending.admit(Some(&[])));
    assert_eq!(
        pending.run_to_completion(&[]),
        Err(ProgramError::NotAdmitted)
    );
    assert!(pending.is_pending());
    assert_eq!(pending.position_now(), 0);
    assert_eq!(pending.read(0), Some(9));
    assert!(matches!(
        ProgramEpisode::execute_and_recover(code, vec![9], 0, vec![], &target),
        Err(ProgramError::NotAdmitted)
    ));
    for instruction in [
        Instruction::Set {
            index: 0,
            value: 1,
            next: 0,
        },
        Instruction::Set {
            index: 1,
            value: 1,
            next: 1,
        },
    ] {
        assert!(matches!(
            ProgramEpisode::execute_and_recover(vec![instruction], vec![0], 0, vec![], &[]),
            Err(ProgramError::InvalidInstruction)
        ));
    }
}

#[test]
fn checked_runners_accept_reordered_and_repeated_complete_bindings() {
    let a = Binding {
        key: 1,
        realm: 2,
        provider: 3,
    };
    let b = Binding {
        key: 4,
        realm: 5,
        provider: 6,
    };
    let code = vec![Instruction::Set {
        index: 0,
        value: 17,
        next: 1,
    }];
    for (captured, target) in [(vec![a, b], vec![b, a, b]), (vec![a, a, b], vec![b, a])] {
        let mut program = ProgramEpisode::new(code.clone(), vec![9], 0, captured.clone()).unwrap();
        let count = program.run_to_completion(&target).unwrap();
        assert_eq!(count.writes, 1);
        assert_eq!(count.steps, 2);
        assert_eq!(program.read(0), Some(17));
        assert!(program.rollback());
        assert_eq!(program.read(0), Some(9));
        let (recovered, recovered_count) =
            ProgramEpisode::execute_and_recover(code.clone(), vec![9], 0, captured, &target)
                .unwrap();
        assert_eq!(recovered_count, count);
        assert_eq!(recovered.read(0), Some(9));
    }
    for target in [
        vec![a],
        vec![a, b, Binding { key: 7, ..b }],
        vec![a, Binding { provider: 8, ..b }],
    ] {
        let mut program = ProgramEpisode::new(code.clone(), vec![9], 0, vec![a, b]).unwrap();
        assert_eq!(
            program.run_to_completion(&target),
            Err(ProgramError::NotAdmitted)
        );
        assert_eq!(program.read(0), Some(9));
        assert_eq!(program.position_now(), 0);
    }
}
