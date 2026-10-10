//! Public histories that observe owner-table recovery across a new episode.
//!
//! A second successful Provide on the same registration detects residual
//! values that a phase transition or an empty journal alone would not detect.
use cordis_kernel::mixed_driver as mixed;
use cordis_kernel::mixed_driver::fresh;
use cordis_kernel::{Phase, Port};

const SERVICE: Port = Port { key: 7, realm: 3 };
const OWN: Port = Port { key: 8, realm: 3 };
const OTHER_REALM: Port = Port { key: 8, realm: 4 };
const UNFILLED: Port = Port { key: 9, realm: 3 };
const CHILD_VALUE: Port = Port { key: 10, realm: 3 };

#[test]
fn failed_bootstrap_clears_all_owner_values_before_reprovide_without_clearing_child() {
    use fresh::{Blueprint, Command::*, Instruction};
    let leaf = Blueprint::new(
        vec![],
        vec![CHILD_VALUE],
        vec![Instruction::Provide {
            key: CHILD_VALUE,
            value: 99,
            next: None,
        }],
    );
    let provider = Blueprint::new(
        vec![],
        vec![SERVICE],
        vec![Instruction::Provide {
            key: SERVICE,
            value: 0x81,
            next: None,
        }],
    );
    let owner = Blueprint::new(
        vec![SERVICE],
        vec![OWN, OTHER_REALM, UNFILLED],
        vec![
            Instruction::Provide {
                key: OWN,
                value: 11,
                next: Some(1),
            },
            Instruction::Xor {
                key: SERVICE,
                mask: 5,
                next: Some(2),
            },
            Instruction::Provide {
                key: OTHER_REALM,
                value: 22,
                next: Some(3),
            },
            Instruction::Child {
                blueprint: 0,
                next: Some(4),
            },
            Instruction::Xor {
                key: OWN,
                mask: 3,
                next: Some(5),
            },
        ],
    );
    let setup = [
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
    ];
    let report = fresh::run_from_empty(vec![leaf, provider, owner], &setup, 1);
    assert_eq!(
        report.status,
        fresh::FromEmptyStatus::Blocked(fresh::DriverError::IncompleteProvision)
    );
    assert_eq!(report.steps, 1);
    assert_eq!(report.setup.len(), setup.len());
    let mut machine = report.machine;
    assert_eq!(machine.phase(1), Some(Phase::Loading));
    assert_eq!(machine.inverse_count(1), Some(5));
    assert_eq!(machine.read(1, OWN), Some(11 ^ 3));
    assert_eq!(machine.read(1, OTHER_REALM), Some(22));
    assert_eq!(machine.read(1, UNFILLED), None);
    assert_eq!(machine.read(0, SERVICE), Some(0x81 ^ 5));
    assert_eq!(machine.read(2, CHILD_VALUE), Some(99));

    // Lose the provider instead of retiring the owner: the same owner remains
    // eligible to start a fresh episode once its dependency is replaced.
    machine.retire(0).unwrap();
    machine.depart(0).unwrap();
    machine.depart(1).unwrap();
    machine.unload(1).unwrap();
    assert!(!machine.retired(1));
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(1), Some(0));
    for key in [OWN, OTHER_REALM, UNFILLED] {
        assert_eq!(machine.read(1, key), None);
    }
    assert_eq!(machine.read(0, SERVICE), Some(0x81));
    // The Child inverse retires identity 2, without emptying its separate table.
    assert!(machine.retired(2));
    assert_eq!(machine.phase(2), Some(Phase::Active));
    assert_eq!(machine.read(2, CHILD_VALUE), Some(99));
    assert_eq!(machine.inverse_count(2), Some(1));
    machine.unload(0).unwrap();
    machine.remove(0).unwrap();

    let replacement = machine.insert(None, 1).unwrap();
    assert_eq!(replacement, 3);
    machine.begin(replacement).unwrap();
    machine.step(replacement).unwrap();
    machine.begin(1).unwrap();
    // This would fail AlreadyProvided if either old owner value survived.
    machine.step(1).unwrap();
    assert_eq!(machine.read(1, OWN), Some(11));
    machine.step(1).unwrap();
    machine.step(1).unwrap();
    assert_eq!(machine.read(1, OTHER_REALM), Some(22));
    assert_eq!(machine.read(replacement, SERVICE), Some(0x81 ^ 5));
    // Leave this second episode at a different successful prefix, before Child.
    machine.retire(1).unwrap();
    machine.depart(1).unwrap();
    machine.unload(1).unwrap();
    for key in [OWN, OTHER_REALM, UNFILLED] {
        assert_eq!(machine.read(1, key), None);
    }
    assert_eq!(machine.read(replacement, SERVICE), Some(0x81));
    assert_eq!(machine.read(2, CHILD_VALUE), Some(99));
    assert_eq!(machine.phase(3), Some(Phase::Active));
    assert_eq!(machine.phase(4), None);
}

#[test]
fn mixed_script_republishes_same_registration_after_dispatcher_unload() {
    use mixed::{Blueprint, Command::*, Instruction};
    let provider = Blueprint::new(
        vec![],
        vec![SERVICE],
        vec![Instruction::Provide {
            key: SERVICE,
            value: 0x81,
            next: None,
        }],
    );
    let owner = Blueprint::new(
        vec![SERVICE],
        vec![OWN, OTHER_REALM],
        vec![
            Instruction::Provide {
                key: OWN,
                value: 11,
                next: Some(1),
            },
            Instruction::Xor {
                key: SERVICE,
                mask: 5,
                next: Some(2),
            },
            Instruction::Provide {
                key: OTHER_REALM,
                value: 22,
                next: Some(3),
            },
            Instruction::Xor {
                key: OWN,
                mask: 3,
                next: None,
            },
        ],
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
        Step { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 },
        Retire { actor: 0 },
        Depart { actor: 0 },
        Depart { actor: 1 },
        Unload { actor: 1 },
        Unload { actor: 0 },
        Remove { actor: 0 },
        Insert {
            parent: None,
            blueprint: 0,
        },
        Begin { actor: 2 },
        Step { actor: 2 },
        Begin { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 },
        Step { actor: 1 },
    ];
    let report = mixed::run_script(vec![provider, owner], &commands);
    assert_eq!(report.error, None);
    assert_eq!(report.transitions.len(), commands.len());
    let mut machine = report.machine;
    assert_eq!(machine.phase(0), None);
    assert_eq!(machine.phase(1), Some(Phase::Active));
    assert_eq!(machine.inverse_count(1), Some(4));
    assert_eq!(machine.read(1, OWN), Some(11 ^ 3));
    assert_eq!(machine.read(1, OTHER_REALM), Some(22));
    assert_eq!(machine.read(2, SERVICE), Some(0x81 ^ 5));

    machine.retire(1).unwrap();
    machine.depart(1).unwrap();
    assert_eq!(
        machine.apply(Unload { actor: 1 }),
        Ok(mixed::Transition::Unload { actor: 1 })
    );
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(1), Some(0));
    assert_eq!(machine.read(1, OWN), None);
    assert_eq!(machine.read(1, OTHER_REALM), None);
    assert_eq!(machine.read(2, SERVICE), Some(0x81));
}
