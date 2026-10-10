//! Concrete terminal value observations compared with foreign-only value algebra.
//!
//! These are public execution histories, not a second executable lifecycle
//! replay: erasing an owner's effects can make foreign Begin/Step calls invalid.
use cordis_kernel::mixed_driver::{self as mixed, Blueprint, Command::*, Instruction};
use cordis_kernel::{Phase, Port};

const SERVICE: Port = Port { key: 7, realm: 3 };
const OWN: Port = Port { key: 8, realm: 3 };
const FOREIGN: Port = Port { key: 9, realm: 3 };

fn provider(value: u64) -> Blueprint {
    Blueprint::new(
        vec![],
        vec![SERVICE],
        vec![Instruction::Provide {
            key: SERVICE,
            value,
            next: None,
        }],
    )
}

#[test]
fn terminal_owner_unload_absorbs_consumers_of_its_new_service_but_keeps_child_values() {
    let child = Blueprint::new(
        vec![SERVICE],
        vec![FOREIGN],
        vec![
            Instruction::Xor {
                key: SERVICE,
                mask: 0x40,
                next: Some(1),
            },
            Instruction::Provide {
                key: FOREIGN,
                value: 77,
                next: None,
            },
        ],
    );
    let owner = Blueprint::new(
        vec![SERVICE],
        vec![OWN],
        vec![
            Instruction::Provide {
                key: OWN,
                value: 31,
                next: Some(1),
            },
            Instruction::Xor {
                key: SERVICE,
                mask: 0x0f,
                next: Some(2),
            },
            Instruction::Child {
                expected: 2,
                blueprint: 0,
                next: Some(3),
            },
            Instruction::Unit,
        ],
    );
    let consumer = Blueprint::new(
        vec![OWN, SERVICE],
        vec![],
        vec![
            Instruction::Xor {
                key: OWN,
                mask: 3,
                next: Some(1),
            },
            Instruction::Xor {
                key: SERVICE,
                mask: 0x30,
                next: None,
            },
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
            parent: None,
            blueprint: 2,
        },
        Begin { actor: 1 }, // Episode-start value snapshot: only SERVICE = 0xa1.
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
        Retire { actor: 1 },
        Depart { actor: 1 },
        Depart { actor: 3 },
        Unload { actor: 3 },
        Unload { actor: 1 },
    ];
    let report = mixed::run_script(vec![child, provider(0xa1), owner, consumer], &commands);
    assert_eq!(report.error, None);
    assert_eq!(report.transitions.len(), commands.len());
    assert_eq!(
        report.transitions.last(),
        Some(&mixed::Transition::Unload { actor: 1 })
    );
    let machine = report.machine;

    // Omit the owner's Provide/Xor/Child/Unit and terminal inverse journal.
    // Foreign value effects on SERVICE are child Xor, consumer Xor and its
    // inverse; the child's provision survives. Compute those independently.
    let foreign_service = 0xa1_u64 ^ 0x40 ^ 0x30 ^ 0x30;
    let foreign_child_value = 77;
    // OWN is absent at Begin. In the value algebra, consumer Xor and its
    // inverse are identity there. Actually replaying consumer Begin would fail
    // without the owner's published OWN; this is not a lifecycle trace claim.
    let absent_own_at_begin = None::<u64>;
    let foreign_owner = absent_own_at_begin.map(|v| v ^ 3).map(|v| v ^ 3);
    assert_eq!(machine.read(0, SERVICE), Some(foreign_service));
    assert_eq!(machine.read(1, OWN), foreign_owner);
    assert_eq!(machine.read(2, FOREIGN), Some(foreign_child_value));
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(1), Some(0));
    assert_eq!(machine.phase(3), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(3), Some(0));
    // Parent recovery retires its captured child; the child's own table and
    // two inverse receipts remain until that child performs its own cleanup.
    assert!(machine.retired(2));
    assert_eq!(machine.phase(2), Some(Phase::Active));
    assert_eq!(machine.inverse_count(2), Some(2));
}

#[test]
fn failed_command_after_terminal_unload_keeps_foreign_replay_of_the_successful_prefix() {
    let owner = Blueprint::new(
        vec![SERVICE],
        vec![OWN],
        vec![
            Instruction::Provide {
                key: OWN,
                value: 31,
                next: Some(1),
            },
            Instruction::Xor {
                key: SERVICE,
                mask: 0x0f,
                next: Some(2),
            },
            Instruction::Unit,
        ],
    );
    let transient = Blueprint::new(
        vec![SERVICE],
        vec![FOREIGN],
        vec![
            Instruction::Provide {
                key: FOREIGN,
                value: 99,
                next: Some(1),
            },
            Instruction::Xor {
                key: SERVICE,
                mask: 0x30,
                next: None,
            },
        ],
    );
    let survivor = Blueprint::new(
        vec![SERVICE],
        vec![],
        vec![Instruction::Xor {
            key: SERVICE,
            mask: 0x80,
            next: None,
        }],
    );
    let commands = [
        Insert {
            parent: None,
            blueprint: 0,
        },
        Begin { actor: 0 },
        Step { actor: 0 },
        Insert {
            parent: None,
            blueprint: 1,
        },
        Begin { actor: 1 },
        Step { actor: 1 },
        Insert {
            parent: None,
            blueprint: 2,
        },
        Begin { actor: 2 },
        Step { actor: 2 },
        Step { actor: 2 },
        Step { actor: 1 },
        Retire { actor: 2 },
        Depart { actor: 2 },
        Unload { actor: 2 }, // A real foreign cleanup inside the owner episode.
        Insert {
            parent: None,
            blueprint: 3,
        },
        Begin { actor: 3 },
        Step { actor: 3 },
        Step { actor: 1 },
        Retire { actor: 1 },
        Depart { actor: 1 },
        Unload { actor: 1 },
        Begin { actor: 999 }, // Fails after the terminal successful transition.
        Retire { actor: 3 },  // Must not run.
    ];
    let report = mixed::run_script(vec![provider(0xa1), owner, transient, survivor], &commands);
    assert_eq!(report.error, Some(mixed::DriverError::Unknown));
    assert_eq!(report.transitions.len(), commands.len() - 2);
    assert_eq!(
        report.transitions.last(),
        Some(&mixed::Transition::Unload { actor: 1 })
    );
    let machine = report.machine;

    // The foreign transient writes FOREIGN, Xors SERVICE, then recovers both.
    // The survivor's Xor remains. Neither the owner's Xor nor its provision is
    // included in this independent calculation from the post-Begin snapshot.
    let foreign_service = 0xa1_u64 ^ 0x30 ^ 0x30 ^ 0x80;
    assert_eq!(machine.read(0, SERVICE), Some(foreign_service));
    assert_eq!(machine.read(1, OWN), None);
    assert_eq!(machine.read(2, FOREIGN), None);
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(1), Some(0));
    assert_eq!(machine.phase(2), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(2), Some(0));
    assert!(!machine.retired(3));
    assert_eq!(machine.phase(3), Some(Phase::Active));
    assert_eq!(machine.inverse_count(3), Some(1));
}
