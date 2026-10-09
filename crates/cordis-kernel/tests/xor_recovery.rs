//! Recovery from actual public histories containing all four inverse kinds.
//!
//! Xor receipts retain the provider selected during the episode. These cases
//! exercise executable recovery without injecting journals or private state.
use cordis_kernel::mixed_driver as mixed;
use cordis_kernel::mixed_driver::fresh;
use cordis_kernel::{Error, Phase, Port};

const SERVICE: Port = Port { key: 7, realm: 3 };
const OWN: Port = Port { key: 8, realm: 3 };
const OTHER_REALM: Port = Port { key: 8, realm: 4 };

fn provider(value: u64) -> fresh::Blueprint {
    fresh::Blueprint::new(
        vec![],
        vec![SERVICE],
        vec![fresh::Instruction::Provide {
            key: SERVICE,
            value,
            next: None,
        }],
    )
}

#[test]
fn mixed_script_recovers_self_xors_before_removing_their_provisions() {
    use mixed::Command::*;
    use mixed::Instruction;
    let leaf = mixed::Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let owner = mixed::Blueprint::new(
        vec![],
        vec![OWN, OTHER_REALM],
        vec![
            Instruction::Provide {
                key: OWN,
                value: 0x91,
                next: Some(1),
            },
            Instruction::Xor {
                key: OWN,
                mask: 0x06,
                next: Some(2),
            },
            Instruction::Child {
                expected: 1,
                blueprint: 0,
                next: Some(3),
            },
            Instruction::Provide {
                key: OTHER_REALM,
                value: 0x37,
                next: Some(4),
            },
            Instruction::Xor {
                key: OWN,
                mask: 0x60,
                next: Some(5),
            },
            Instruction::Xor {
                key: OTHER_REALM,
                mask: 0x11,
                next: Some(6),
            },
            Instruction::Unit,
        ],
    );
    let commands = [
        Insert {
            parent: None,
            blueprint: 1,
        },
        Begin { actor: 0 },
        Step { actor: 0 },
        Step { actor: 0 },
        Step { actor: 0 },
        Step { actor: 0 },
        Step { actor: 0 },
        Step { actor: 0 },
        Step { actor: 0 },
        Begin { actor: 1 },
        Step { actor: 1 },
        Retire { actor: 0 },
        Depart { actor: 0 },
    ];
    let report = mixed::run_script(vec![leaf, owner], &commands);
    assert_eq!(report.error, None);
    assert_eq!(report.transitions.len(), commands.len());
    let mut machine = report.machine;
    assert_eq!(machine.read(0, OWN), Some(0x91 ^ 0x06 ^ 0x60));
    assert_eq!(machine.read(0, OTHER_REALM), Some(0x37 ^ 0x11));
    assert_eq!(machine.inverse_count(0), Some(7));

    // Both Xors of OWN must run before its earlier Provision is undone. A
    // forward-order rollback would remove the value needed by those inverses.
    machine.unload(0).unwrap();
    assert_eq!(machine.phase(0), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(0), Some(0));
    assert_eq!(machine.read(0, OWN), None);
    assert_eq!(machine.read(0, OTHER_REALM), None);
    assert!(machine.retired(1));
    assert_eq!(machine.phase(1), Some(Phase::Active));
    assert_eq!(machine.inverse_count(1), Some(1));
    machine.depart(1).unwrap();
    machine.unload(1).unwrap();
    machine.remove(1).unwrap();
    machine.remove(0).unwrap();
}

#[test]
fn retired_provider_stays_available_to_the_consumers_captured_xor_inverses() {
    use fresh::Command::*;
    let consumer = fresh::Blueprint::new(
        vec![SERVICE],
        vec![],
        vec![
            fresh::Instruction::Xor {
                key: SERVICE,
                mask: 0x05,
                next: Some(1),
            },
            fresh::Instruction::Xor {
                key: SERVICE,
                mask: 0x30,
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
        Retire { actor: 0 },
        Depart { actor: 0 },
        Unload { actor: 0 }, // Stops the script; this dependency is still pinned.
        Unload { actor: 1 },
    ];
    let report = fresh::run_script(vec![provider(0x92), consumer], &commands);
    assert_eq!(
        report.error,
        Some(fresh::DriverError::Kernel(Error::Relied))
    );
    assert_eq!(report.transitions.len(), 9);
    let mut machine = report.machine;
    assert_eq!(machine.phase(0), Some(Phase::Unloading));
    assert_eq!(machine.phase(1), Some(Phase::Active));
    assert_eq!(machine.read(0, SERVICE), Some(0x92 ^ 0x05 ^ 0x30));
    assert_eq!(machine.inverse_count(0), Some(1));
    assert_eq!(machine.inverse_count(1), Some(2));

    // The provider no longer qualifies as a current target, but its captured
    // identity remains valid for recovery. No new provider lookup is needed.
    machine.depart(1).unwrap();
    machine.unload(1).unwrap();
    assert_eq!(machine.read(0, SERVICE), Some(0x92));
    assert_eq!(machine.inverse_count(1), Some(0));
    machine.unload(0).unwrap();
    assert_eq!(machine.read(0, SERVICE), None);
    assert_eq!(machine.inverse_count(0), Some(0));
}

#[test]
fn interleaved_consumers_recover_only_their_xors_and_keep_the_provider_value() {
    use fresh::Command::*;
    let consumer = |a, b| {
        fresh::Blueprint::new(
            vec![SERVICE],
            vec![],
            vec![
                fresh::Instruction::Xor {
                    key: SERVICE,
                    mask: a,
                    next: Some(1),
                },
                fresh::Instruction::Xor {
                    key: SERVICE,
                    mask: b,
                    next: None,
                },
            ],
        )
    };
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
        Insert {
            parent: None,
            blueprint: 2,
        },
        Begin { actor: 2 },
        Step { actor: 1 },
        Step { actor: 2 },
        Step { actor: 1 },
        Step { actor: 2 },
        Retire { actor: 0 },
        Depart { actor: 0 },
    ];
    let report = fresh::run_script(
        vec![provider(0xb1), consumer(0x03, 0x30), consumer(0x05, 0x50)],
        &commands,
    );
    assert_eq!(report.error, None);
    let mut machine = report.machine;
    assert_eq!(
        machine.read(0, SERVICE),
        Some(0xb1 ^ 0x03 ^ 0x30 ^ 0x05 ^ 0x50)
    );

    // Consumer 1 finishes recovery first, despite consumer 2 owning the most
    // recent Xor. Its rollback must preserve consumer 2's still-live effects.
    machine.depart(1).unwrap();
    machine.unload(1).unwrap();
    assert_eq!(machine.read(0, SERVICE), Some(0xb1 ^ 0x05 ^ 0x50));
    assert_eq!(machine.inverse_count(1), Some(0));
    assert_eq!(machine.inverse_count(2), Some(2));
    assert_eq!(
        machine.unload(0),
        Err(fresh::DriverError::Kernel(Error::Relied))
    );
    assert_eq!(machine.read(0, SERVICE), Some(0xb1 ^ 0x05 ^ 0x50));
    machine.depart(2).unwrap();
    machine.unload(2).unwrap();
    assert_eq!(machine.read(0, SERVICE), Some(0xb1));
    assert_eq!(machine.inverse_count(2), Some(0));
    machine.unload(0).unwrap();
    assert_eq!(machine.read(0, SERVICE), None);
}

#[test]
fn bootstrap_failure_recovers_its_self_and_foreign_xors_from_the_real_prefix() {
    let leaf = fresh::Blueprint::new(vec![], vec![], vec![]);
    let consumer = fresh::Blueprint::new(
        vec![SERVICE],
        vec![OWN, OTHER_REALM],
        vec![
            fresh::Instruction::Provide {
                key: OWN,
                value: 0x41,
                next: Some(1),
            },
            fresh::Instruction::Xor {
                key: SERVICE,
                mask: 0x0f,
                next: Some(2),
            },
            fresh::Instruction::Child {
                blueprint: 0,
                next: Some(3),
            },
            fresh::Instruction::Xor {
                key: OWN,
                mask: 0x30,
                next: Some(4),
            },
            fresh::Instruction::Xor {
                key: SERVICE,
                mask: 0xa0,
                next: Some(5),
            },
        ],
    );
    let setup = [
        fresh::Command::Insert {
            parent: None,
            blueprint: 1,
        },
        fresh::Command::Begin { actor: 0 },
        fresh::Command::Step { actor: 0 },
        fresh::Command::Insert {
            parent: None,
            blueprint: 2,
        },
        fresh::Command::Begin { actor: 1 },
    ];
    let report = fresh::run_from_empty(vec![leaf, provider(0x92), consumer], &setup, 1);
    assert_eq!(
        report.status,
        fresh::FromEmptyStatus::Blocked(fresh::DriverError::IncompleteProvision)
    );
    assert_eq!(report.setup.len(), setup.len());
    assert_eq!(report.steps, 5);
    let mut machine = report.machine;
    assert_eq!(machine.phase(1), Some(Phase::Loading));
    assert_eq!(machine.inverse_count(1), Some(5));
    assert_eq!(machine.read(0, SERVICE), Some(0x92 ^ 0x0f ^ 0xa0));
    assert_eq!(machine.read(1, OWN), Some(0x41 ^ 0x30));
    assert_eq!(machine.read(1, OTHER_REALM), None);
    assert!(!machine.retired(2));

    // The implicit Unit failed its publication check and added no receipt.
    // The successfully committed Xors, Provision and Child remain recoverable.
    machine.retire(1).unwrap();
    machine.depart(1).unwrap();
    machine.unload(1).unwrap();
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert_eq!(machine.inverse_count(1), Some(0));
    assert_eq!(machine.read(0, SERVICE), Some(0x92));
    assert_eq!(machine.phase(0), Some(Phase::Active));
    assert_eq!(machine.inverse_count(0), Some(1));
    assert_eq!(machine.read(1, OWN), None);
    assert_eq!(machine.read(1, OTHER_REALM), None);
    assert!(machine.retired(2));
    machine.remove(2).unwrap();
    machine.remove(1).unwrap();
}
