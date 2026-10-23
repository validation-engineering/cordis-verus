//! Reachable checkpoints for R3's all-episode contract. Expected values come
//! from the foreign XOR/provision calculation, not a fabricated lifecycle.
use cordis_kernel::mixed_driver::fresh::{self, Blueprint, Instruction as I};
use cordis_kernel::mixed_driver::{Command, Command::*, DriverError, Inverse, Receipt, Transition};
use cordis_kernel::{Error, Phase, Port};

const SERVICE: Port = Port { key: 7, realm: 3 };
const OWN: Port = Port { key: 8, realm: 3 };
const FOREIGN: Port = Port { key: 9, realm: 3 };

fn bank() -> Vec<Blueprint> {
    let provider = |value| {
        Blueprint::new(
            vec![],
            vec![SERVICE],
            vec![I::Provide {
                key: SERVICE,
                value,
                next: None,
            }],
        )
    };
    vec![
        Blueprint::new(
            vec![SERVICE],
            vec![FOREIGN],
            vec![
                I::Xor {
                    key: SERVICE,
                    mask: 0x40,
                    next: Some(1),
                },
                I::Provide {
                    key: FOREIGN,
                    value: 77,
                    next: None,
                },
            ],
        ),
        provider(0xa1),
        Blueprint::new(
            vec![SERVICE],
            vec![OWN],
            vec![
                I::Provide {
                    key: OWN,
                    value: 31,
                    next: Some(1),
                },
                I::Xor {
                    key: SERVICE,
                    mask: 0x0f,
                    next: Some(2),
                },
                I::Child {
                    blueprint: 0,
                    next: Some(3),
                },
                I::Unit,
            ],
        ),
        Blueprint::new(
            vec![OWN, SERVICE],
            vec![],
            vec![
                I::Xor {
                    key: OWN,
                    mask: 3,
                    next: Some(1),
                },
                I::Xor {
                    key: SERVICE,
                    mask: 0x30,
                    next: None,
                },
            ],
        ),
        provider(0xb2),
    ]
}

fn before_consumer_cleanup() -> Vec<Command> {
    vec![
        Insert {
            parent: None,
            blueprint: 1,
        },
        Begin { actor: 0 },
        Step { actor: 0 },
        Insert {
            parent: None,
            blueprint: 2,
        },
        Begin { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 },
        Begin { actor: 2 },
        Step { actor: 2 },
        Step { actor: 2 },
        Insert {
            parent: None,
            blueprint: 3,
        },
        Begin { actor: 3 },
        Step { actor: 3 },
        Step { actor: 3 },
        Retire { actor: 0 },
        Depart { actor: 0 },
        Depart { actor: 1 },
    ]
}

fn first_close() -> Vec<Command> {
    let mut commands = before_consumer_cleanup();
    commands.extend([
        Depart { actor: 3 },
        Unload { actor: 3 },
        Unload { actor: 1 },
    ]);
    commands
}

#[test]
fn open_episode_failure_keeps_the_actual_receipts_and_blocks_provider_cleanup() {
    let mut commands = before_consumer_cleanup();
    let successful = commands.len();
    commands.extend([Unload { actor: 1 }, Unload { actor: 0 }]);
    let report = fresh::run_inspected(bank(), &commands, 1, OWN, 2);
    assert_eq!(report.run.error, Some(DriverError::Kernel(Error::Relied)));
    assert_eq!(report.run.transitions.len(), successful);
    assert_eq!(report.value, Some(31 ^ 3));
    assert_eq!(
        report.inverse,
        Some(Receipt {
            actor: 1,
            inverse: Inverse::Child { child: 2 }
        })
    );
    assert_eq!(report.run.machine.inverse_count(1), Some(4));
    assert_eq!(report.run.machine.phase(1), Some(Phase::Unloading));
    assert_eq!(
        report.run.machine.read(0, SERVICE),
        Some(0xa1 ^ 0x0f ^ 0x40 ^ 0x30)
    );
    assert_eq!(report.run.machine.read(2, FOREIGN), Some(77));
    assert_eq!(report.run.machine.inverse_count(0), Some(1));
    assert!(!report.run.machine.retired(2));
}

#[test]
fn two_interior_unloads_use_distinct_begin_snapshots_and_actual_child_choices() {
    let mut commands = first_close();
    let first_end = commands.len();
    let first = fresh::run_script(bank(), &commands);
    assert_eq!(first.error, None);
    // The consumer's forward and inverse cancel; the child's effects survive.
    assert_eq!(first.machine.read(0, SERVICE), Some(0xa1 ^ 0x40));
    assert_eq!(first.machine.read(1, OWN), None);
    assert_eq!(first.machine.read(2, FOREIGN), Some(77));
    assert!(first.machine.retired(2));

    commands.extend([
        Depart { actor: 2 },
        Unload { actor: 2 },
        Unload { actor: 0 },
        Remove { actor: 0 },
        Remove { actor: 2 },
        Insert {
            parent: None,
            blueprint: 4,
        }, // Replacement provider is 4.
        Begin { actor: 4 },
        Step { actor: 4 },
        Begin { actor: 1 }, // Second snapshot uses 0xb2, not 0xa1.
        Step { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 }, // Same Child PC now allocates 5.
        Step { actor: 1 },
        Begin { actor: 5 },
        Step { actor: 5 },
        Step { actor: 5 },
        Begin { actor: 3 },
        Step { actor: 3 },
        Step { actor: 3 },
        Retire { actor: 4 },
        Depart { actor: 4 },
        Depart { actor: 1 },
        Depart { actor: 3 },
        Unload { actor: 3 },
        Unload { actor: 1 },
        Depart { actor: 5 }, // Owner Unload is not the terminal transition.
        Begin { actor: 999 },
        Unload { actor: 5 }, // Must not run after the failure.
    ]);
    let report = fresh::run_inspected(bank(), &commands, 5, FOREIGN, 0);
    assert_eq!(report.run.error, Some(DriverError::Unknown));
    assert_eq!(report.run.transitions.len(), commands.len() - 2);
    assert_eq!(
        report.run.transitions[first_end - 1],
        Transition::Unload { actor: 1 }
    );
    assert!(matches!(
        report.run.transitions.last(),
        Some(Transition::Depart { actor: 5, .. })
    ));
    assert_eq!(report.value, Some(77));
    assert_eq!(
        report.inverse,
        Some(Receipt {
            actor: 5,
            inverse: Inverse::Xor {
                provider: 4,
                key: SERVICE,
                mask: 0x40
            },
        })
    );
    let machine = report.run.machine;
    assert_eq!(machine.read(4, SERVICE), Some(0xb2 ^ 0x40));
    assert_eq!(machine.read(1, OWN), None);
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(1), Some(0));
    assert_eq!(machine.phase(0), None);
    assert_eq!(machine.phase(2), None);
    assert!(machine.retired(5));
    assert_eq!(machine.phase(5), Some(Phase::Unloading));
    assert_eq!(machine.inverse_count(5), Some(2));
}
