use cordis_kernel::mixed_driver::fresh::{
    compaction::{self, Error as CompactError},
    run_script, Blueprint, Command, Instruction, Outcome, Transition,
};
use cordis_kernel::{Phase, Port};

fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}

fn bank() -> Vec<Blueprint> {
    vec![
        Blueprint::new(vec![], vec![], vec![Instruction::Unit]),
        Blueprint::new(
            vec![port(0)],
            vec![],
            vec![Instruction::Xor {
                key: port(0),
                mask: 3,
                next: None,
            }],
        ),
        Blueprint::new(
            vec![],
            vec![port(0)],
            vec![
                Instruction::Provide {
                    key: port(0),
                    value: 10,
                    next: Some(1),
                },
                Instruction::Child {
                    blueprint: 1,
                    next: None,
                },
            ],
        ),
        Blueprint::new(
            vec![],
            vec![port(1)],
            vec![Instruction::Provide {
                key: port(1),
                value: 23,
                next: None,
            }],
        ),
        Blueprint::new(vec![port(0)], vec![], vec![Instruction::Unit]),
        Blueprint::new(
            vec![],
            vec![port(2)],
            vec![
                Instruction::Provide {
                    key: port(2),
                    value: 99,
                    next: Some(1),
                },
                Instruction::Child {
                    blueprint: 0,
                    next: None,
                },
            ],
        ),
    ]
}

#[test]
fn deleted_child_shifts_real_insert_parent_and_later_child_choices() {
    use Command::*;
    let source = run_script(
        bank(),
        &[
            Insert {
                parent: None,
                blueprint: 2,
            },
            Insert {
                parent: None,
                blueprint: 3,
            },
            Begin { actor: 0 },
            Step { actor: 0 },
            Begin { actor: 1 },
            Step { actor: 1 },
            Step { actor: 0 },
            Begin { actor: 2 },
            Step { actor: 2 },
            Insert {
                parent: None,
                blueprint: 4,
            },
            Begin { actor: 3 },
            Step { actor: 3 },
            Retire { actor: 0 },
            Depart { actor: 0 },
            Depart { actor: 2 },
            Unload { actor: 2 },
            Depart { actor: 3 },
            Unload { actor: 3 },
            Unload { actor: 0 },
            Retire { actor: 1 },
            Depart { actor: 1 },
            Unload { actor: 1 },
            Remove { actor: 2 },
            Insert {
                parent: None,
                blueprint: 5,
            },
            Begin { actor: 4 },
            Step { actor: 4 },
            Step { actor: 4 },
            Insert {
                parent: Some(5),
                blueprint: 0,
            },
            Retire { actor: 4 },
            Depart { actor: 4 },
            Unload { actor: 4 },
            Retire { actor: 6 },
            Remove { actor: 6 },
            Remove { actor: 5 },
            Remove { actor: 4 },
            Insert {
                parent: None,
                blueprint: 5,
            },
            Begin { actor: 7 },
            Step { actor: 7 },
            Step { actor: 7 },
            Unload { actor: 7 }, // Checked error: the Active plugin cannot unload.
        ],
    );
    assert_eq!(source.transitions.len(), 39);
    assert!(source.error.is_some());
    assert_eq!(source.machine.allocation_bound(), 9);
    let keep: Vec<bool> = source
        .transitions
        .iter()
        .map(|t| match t.actor() {
            2 => false,
            0 | 3 => matches!(
                t,
                Transition::Insert { .. } | Transition::Retire { .. } | Transition::Remove { .. }
            ),
            _ => true,
        })
        .collect();
    let plan = source.compact(&keep).unwrap();
    assert_eq!(plan.transitions.len(), 25);
    assert_eq!(plan.allocated, 8);
    assert_eq!(plan.names.name(3), 2);
    assert_eq!(plan.names.name(7), 6);
    assert_eq!(plan.names.name(usize::MAX), usize::MAX);
    assert!(plan.transitions.contains(&Transition::Insert {
        parent: Some(4),
        blueprint: 0,
        actor: 5
    }));
    assert!(plan.transitions.contains(&Transition::Step {
        actor: 3,
        outcome: Outcome::Child {
            child: 4,
            finished: true
        }
    }));
    assert!(plan.transitions.contains(&Transition::Step {
        actor: 6,
        outcome: Outcome::Child {
            child: 7,
            finished: true
        }
    }));

    // Use the same public executor and installed blueprints, with actual IDs.
    let replay = run_script(bank(), &plan.commands());
    assert_eq!(replay.error, None);
    assert_eq!(replay.transitions, plan.transitions);
    assert_eq!(replay.machine.allocation_bound(), plan.allocated);
    assert_eq!(source.machine.read(7, port(2)), Some(99));
    assert_eq!(replay.machine.read(6, port(2)), Some(99));
    assert_eq!(replay.machine.phase(6), Some(Phase::Active));
    assert_eq!(replay.machine.phase(4), None); // A removed retained name stays consumed.
    assert_eq!(replay.machine.read(0, port(0)), None);
    assert_eq!(replay.machine.read(1, port(1)), None);
}

#[test]
fn omitted_origins_and_forged_births_are_rejected_without_touching_source() {
    let source = run_script(
        bank(),
        &[
            Command::Insert {
                parent: None,
                blueprint: 0,
            },
            Command::Begin { actor: 0 },
            Command::Step { actor: 0 },
        ],
    );
    assert!(matches!(
        source.compact(&[false, true, true]),
        Err(CompactError::MissingOrigin { index: 1 })
    ));
    assert!(matches!(
        source.compact(&[true]),
        Err(CompactError::MaskLength)
    ));
    assert_eq!(source.machine.phase(0), Some(Phase::Active));
    assert_eq!(source.machine.allocation_bound(), 1);
    let birth = Transition::Insert {
        parent: None,
        blueprint: 0,
        actor: 0,
    };
    assert!(matches!(
        compaction::compact(&[birth, birth], &[true, true], 1),
        Err(CompactError::RepeatedBirth { index: 1 })
    ));
    assert!(matches!(
        compaction::compact(&[birth], &[true], 0),
        Err(CompactError::UnknownBirth { index: 0 })
    ));
    let empty = source.compact(&[false, false, false]).unwrap();
    assert!(empty.commands().is_empty());
    assert_eq!(empty.allocated, 0);
}

#[test]
fn retained_loading_departure_and_reactivation_survive_child_compaction() {
    use Command::*;
    fn installed() -> Vec<Blueprint> {
        vec![
            Blueprint::new(vec![], vec![], vec![Instruction::Unit]),
            Blueprint::new(
                vec![],
                vec![],
                vec![Instruction::Child {
                    blueprint: 0,
                    next: None,
                }],
            ),
            Blueprint::new(
                vec![],
                vec![port(0)],
                vec![Instruction::Provide {
                    key: port(0),
                    value: 11,
                    next: None,
                }],
            ),
            Blueprint::new(
                vec![port(0)],
                vec![],
                vec![
                    Instruction::Xor {
                        key: port(0),
                        mask: 3,
                        next: Some(1),
                    },
                    Instruction::Unit,
                ],
            ),
        ]
    }
    let source = run_script(
        installed(),
        &[
            Insert {
                parent: None,
                blueprint: 1,
            },
            Begin { actor: 0 },
            Step { actor: 0 },
            Retire { actor: 0 },
            Depart { actor: 0 },
            Unload { actor: 0 },
            Remove { actor: 1 },
            Remove { actor: 0 },
            Insert {
                parent: None,
                blueprint: 2,
            },
            Begin { actor: 2 },
            Step { actor: 2 },
            Insert {
                parent: None,
                blueprint: 3,
            },
            Begin { actor: 3 },
            Step { actor: 3 },
            Retire { actor: 2 },
            Depart { actor: 2 },
            Depart { actor: 3 }, // Loading -> Unloading, with no extra landing.
            Unload { actor: 3 },
            Unload { actor: 2 },
            Remove { actor: 2 },
            Insert {
                parent: None,
                blueprint: 2,
            },
            Begin { actor: 4 },
            Step { actor: 4 },
            Begin { actor: 3 }, // Same consumer, new generation and provider.
            Step { actor: 3 },
            Step { actor: 3 },
        ],
    );
    assert_eq!(source.error, None);
    let keep: Vec<bool> = source
        .transitions
        .iter()
        .map(|t| match t.actor() {
            1 => false,
            0 => matches!(
                t,
                Transition::Insert { .. } | Transition::Retire { .. } | Transition::Remove { .. }
            ),
            _ => true,
        })
        .collect();
    let plan = source.compact(&keep).unwrap();
    let replay = run_script(installed(), &plan.commands());
    assert_eq!(replay.error, None);
    assert_eq!(replay.transitions, plan.transitions);
    assert_eq!(source.transitions.len(), 26);
    assert_eq!(replay.transitions.len(), 21);
    assert!(replay.transitions.contains(&Transition::Depart {
        actor: 2,
        departure: cordis_kernel::mixed_driver::Departure::Divert,
    }));
    assert_eq!(source.machine.allocation_bound(), 5);
    assert_eq!(replay.machine.allocation_bound(), 4);
    assert_eq!(source.machine.read(4, port(0)), Some(8));
    assert_eq!(replay.machine.read(3, port(0)), Some(8));
    assert_eq!(replay.machine.phase(2), Some(Phase::Active));
    assert_eq!(replay.machine.phase(1), None); // The old provider was removed.
    assert_eq!(replay.machine.inverse_count(2), Some(2)); // XOR + Unit in the new episode.
}
