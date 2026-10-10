//! Compare real Fresh results with independent foreign-only value calculations.
//! The counterfactual is not a second executable lifecycle trace.
use cordis_kernel::mixed_driver::fresh::{self as fresh, Blueprint, Instruction as I};
use cordis_kernel::mixed_driver::{Command::*, DriverError, Outcome, Transition};
use cordis_kernel::{Phase, Port};

const SERVICE: Port = Port { key: 7, realm: 3 };
const OWN: Port = Port { key: 8, realm: 3 };
const FOREIGN: Port = Port { key: 9, realm: 3 };
const SECOND: Port = Port { key: 10, realm: 3 };

fn provider(key: Port, value: u64) -> Blueprint {
    Blueprint::new(
        vec![],
        vec![key],
        vec![I::Provide {
            key,
            value,
            next: None,
        }],
    )
}

fn children(transitions: &[Transition], owner: usize) -> Vec<usize> {
    transitions
        .iter()
        .filter_map(|t| match t {
            Transition::Step {
                actor,
                outcome: Outcome::Child { child, .. },
            } if *actor == owner => Some(*child),
            _ => None,
        })
        .collect()
}

#[test]
fn fresh_terminal_recovery_keeps_allocated_child_values_and_foreign_cleanup() {
    let child = Blueprint::new(
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
    );
    let owner = Blueprint::new(
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
    );
    let consumer = Blueprint::new(
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
    );
    let padding = Blueprint::new(vec![], vec![], vec![I::Unit]);
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
        Begin { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 },
        // Another real insertion shifts the choice at the later Child landing.
        Insert {
            parent: None,
            blueprint: 4,
        },
        Step { actor: 1 },
        Step { actor: 1 },
        Begin { actor: 3 },
        Step { actor: 3 },
        Step { actor: 3 },
        Insert {
            parent: None,
            blueprint: 3,
        },
        Begin { actor: 4 },
        Step { actor: 4 },
        Step { actor: 4 },
        Retire { actor: 1 },
        Depart { actor: 1 },
        Depart { actor: 4 },
        Unload { actor: 4 },
        Unload { actor: 1 },
    ];
    let report = fresh::run_script(
        vec![child, provider(SERVICE, 0xa1), owner, consumer, padding],
        &commands,
    );
    assert_eq!(report.error, None);
    assert_eq!(report.transitions.len(), commands.len());
    assert_eq!(children(&report.transitions, 1), [3]);
    assert_eq!(
        report.transitions.last(),
        Some(&Transition::Unload { actor: 1 })
    );
    let machine = report.machine;
    // The child's Xor remains. The foreign consumer's forward Xor and its
    // actual captured inverse cancel, while the owner's own Xor is omitted.
    let foreign_service = 0xa1_u64 ^ 0x40 ^ 0x30 ^ 0x30;
    assert_eq!(machine.read(0, SERVICE), Some(foreign_service));
    // OWN was absent at Begin, so the foreign consumer's Xors on OWN act as
    // identity in value replay. Its Begin would not be legal without the owner.
    let absent = None::<u64>;
    assert_eq!(machine.read(1, OWN), absent.map(|v| v ^ 3).map(|v| v ^ 3));
    assert_eq!(machine.read(3, FOREIGN), Some(77));
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(1), Some(0));
    assert_eq!(machine.phase(4), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(4), Some(0));
    assert!(machine.retired(3));
    assert_eq!(machine.phase(3), Some(Phase::Active));
    assert_eq!(machine.inverse_count(3), Some(2));
}

#[test]
fn fresh_reactivated_episode_replays_new_choices_and_cross_provider_effects() {
    let child = Blueprint::new(vec![], vec![], vec![I::Unit]);
    let owner = Blueprint::new(
        vec![SERVICE, SECOND],
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
            I::Xor {
                key: SECOND,
                mask: 0xf0,
                next: Some(3),
            },
            I::Child {
                blueprint: 0,
                next: Some(4),
            },
            I::Unit,
        ],
    );
    let foreign = Blueprint::new(
        vec![SECOND],
        vec![],
        vec![I::Xor {
            key: SECOND,
            mask: 0x40,
            next: None,
        }],
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
        Begin { actor: 1 },
        Step { actor: 1 },
        Insert {
            parent: None,
            blueprint: 3,
        },
        Begin { actor: 2 },
        Step { actor: 2 },
        Step { actor: 2 },
        Step { actor: 2 },
        Insert {
            parent: None,
            blueprint: 4,
        },
        Begin { actor: 3 },
        Step { actor: 3 },
        Step { actor: 2 },
        Step { actor: 2 }, // First actual child is 4.
        Retire { actor: 0 },
        Depart { actor: 0 }, // Withdraw publication before the consumer reacts.
        Depart { actor: 2 },
        Unload { actor: 2 },
        Unload { actor: 0 },
        Remove { actor: 0 },
        Insert {
            parent: None,
            blueprint: 5,
        },
        Begin { actor: 5 },
        Step { actor: 5 },
        Begin { actor: 2 }, // New snapshot: SERVICE=0xb2; SECOND=0xd4 ^ 0x40.
        Step { actor: 2 },
        Step { actor: 2 },
        Step { actor: 2 },
        Step { actor: 2 },
        Step { actor: 2 }, // Same Child PC now allocates 6.
        Retire { actor: 3 },
        Depart { actor: 3 },
        Unload { actor: 3 },
        Retire { actor: 5 },
        Depart { actor: 5 },
        Depart { actor: 2 },
        Unload { actor: 2 },
        Begin { actor: 999 }, // Rejected after the terminal successful Unload.
        Retire { actor: 1 },  // Must not run.
    ];
    let report = fresh::run_script(
        vec![
            child,
            provider(SERVICE, 0xa1),
            provider(SECOND, 0xd4),
            owner,
            foreign,
            provider(SERVICE, 0xb2),
        ],
        &commands,
    );
    assert_eq!(
        report.error,
        Some(DriverError::Unknown),
        "stopped before {:?}",
        commands.get(report.transitions.len())
    );
    assert_eq!(report.transitions.len(), commands.len() - 2);
    assert_eq!(children(&report.transitions, 2), [4, 6]);
    assert_eq!(
        report.transitions.last(),
        Some(&Transition::Unload { actor: 2 })
    );
    let machine = report.machine;
    // Replay only the foreign cleanup from the second Begin snapshot. Its
    // inverse predates this episode, but is still the real captured 0x40 mask.
    let snapshot_second = 0xd4_u64 ^ 0x40;
    let foreign_second = snapshot_second ^ 0x40;
    assert_eq!(machine.read(5, SERVICE), Some(0xb2));
    assert_eq!(machine.read(1, SECOND), Some(foreign_second));
    assert_eq!(machine.read(2, OWN), None);
    assert_eq!(machine.phase(2), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(2), Some(0));
    assert_eq!(machine.phase(3), Some(Phase::Inactive));
    assert!(machine.retired(4));
    assert!(machine.retired(6));
    assert!(!machine.retired(1));
    assert_eq!(machine.phase(0), None);
}
