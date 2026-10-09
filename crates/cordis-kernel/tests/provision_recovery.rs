//! Actual public API histories for the Unit/Child/Provision recovery profile.
//!
//! Foreign Xor steps can change a provision's current value. They do not make
//! the provider's journal an Xor journal or bypass dependency cleanup guards.
use cordis_kernel::mixed_driver as mixed;
use cordis_kernel::mixed_driver::fresh;
use cordis_kernel::{Error, Phase, Port};

fn first() -> Port {
    Port { key: 7, realm: 3 }
}

fn second() -> Port {
    // Port identity includes the realm, not just the numeric key.
    Port { key: 7, realm: 4 }
}

#[test]
fn mixed_history_recovers_distinct_provisions_and_only_its_captured_child() {
    use mixed::Command::*;
    let leaf = mixed::Blueprint::new(vec![], vec![], vec![mixed::Instruction::Unit]);
    let owner = mixed::Blueprint::new(
        vec![],
        vec![first(), second()],
        vec![
            mixed::Instruction::Provide {
                key: first(),
                value: 11,
                next: Some(1),
            },
            mixed::Instruction::Child {
                expected: 1,
                blueprint: 0,
                next: Some(2),
            },
            mixed::Instruction::Provide {
                key: second(),
                value: 22,
                next: Some(3),
            },
            mixed::Instruction::Unit,
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
        Insert {
            parent: Some(0),
            blueprint: 0,
        }, // An externally inserted child is not captured by the owner's journal.
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
    assert_eq!(machine.phase(0), Some(Phase::Unloading));
    assert_eq!(machine.read(0, first()), Some(11));
    assert_eq!(machine.read(0, second()), Some(22));
    assert_eq!(machine.inverse_count(0), Some(4));

    machine.unload(0).unwrap();
    assert_eq!(machine.phase(0), Some(Phase::Inactive));
    assert_eq!(machine.read(0, first()), None);
    assert_eq!(machine.read(0, second()), None);
    assert_eq!(machine.inverse_count(0), Some(0));
    assert!(machine.retired(1));
    // Parent recovery retires the captured child; it does not run that child's
    // separate journal or remove its registration.
    assert_eq!(machine.phase(1), Some(Phase::Active));
    assert_eq!(machine.inverse_count(1), Some(1));
    assert!(!machine.retired(2));
    assert_eq!(machine.phase(2), Some(Phase::Inactive));
    machine.depart(1).unwrap();
    machine.unload(1).unwrap();
    machine.remove(1).unwrap();
    assert_eq!(
        machine.remove(0),
        Err(mixed::DriverError::Kernel(Error::Children))
    );
    assert_eq!(machine.phase(2), Some(Phase::Inactive));
    assert!(!machine.retired(2));
}

#[test]
fn foreign_xor_preserves_a_real_provision_until_dependency_cleanup_allows_recovery() {
    use fresh::Command::*;
    let owner = fresh::Blueprint::new(
        vec![],
        vec![first()],
        vec![fresh::Instruction::Provide {
            key: first(),
            value: 11,
            next: None,
        }],
    );
    let consumer = fresh::Blueprint::new(
        vec![first()],
        vec![],
        vec![fresh::Instruction::Xor {
            key: first(),
            mask: 5,
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
        Retire { actor: 0 },
        Depart { actor: 0 },
    ];
    let report = fresh::run_script(vec![owner, consumer], &commands);
    assert_eq!(report.error, None);
    assert_eq!(report.transitions.len(), commands.len());
    let mut machine = report.machine;
    assert_eq!(machine.read(0, first()), Some(11 ^ 5));
    assert_eq!(machine.inverse_count(0), Some(1));
    assert_eq!(machine.inverse_count(1), Some(1));
    assert_eq!(
        machine.unload(0),
        Err(fresh::DriverError::Kernel(Error::Relied))
    );
    assert_eq!(machine.phase(0), Some(Phase::Unloading));
    assert_eq!(machine.phase(1), Some(Phase::Active));
    assert_eq!(machine.read(0, first()), Some(11 ^ 5));
    assert_eq!(machine.inverse_count(0), Some(1));
    assert_eq!(machine.inverse_count(1), Some(1));

    // This concrete consumer restores its Xor before releasing its dependency.
    // The provider's inverse needs a present value, not the originally written
    // value; the runtime still enforces the separate dependency guard.
    machine.depart(1).unwrap();
    machine.unload(1).unwrap();
    assert_eq!(machine.read(0, first()), Some(11));
    machine.unload(0).unwrap();
    assert_eq!(machine.phase(0), Some(Phase::Inactive));
    assert_eq!(machine.read(0, first()), None);
    assert_eq!(machine.inverse_count(0), Some(0));
    assert_eq!(machine.inverse_count(1), Some(0));
}

#[test]
fn duplicate_provide_failure_keeps_the_actual_provision_and_child_prefix_recoverable() {
    use fresh::Command::*;
    let leaf = fresh::Blueprint::new(vec![], vec![], vec![fresh::Instruction::Unit]);
    let owner = fresh::Blueprint::new(
        vec![],
        vec![first()],
        vec![
            fresh::Instruction::Provide {
                key: first(),
                value: 11,
                next: Some(1),
            },
            fresh::Instruction::Child {
                blueprint: 0,
                next: Some(2),
            },
            fresh::Instruction::Provide {
                key: first(),
                value: 99,
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
        Step { actor: 0 },
        Step { actor: 0 }, // Rejected: the earlier successful Provide is retained.
        Retire { actor: 0 }, // Commands after the first error do not execute.
    ];
    let report = fresh::run_script(vec![leaf, owner], &commands);
    assert_eq!(report.error, Some(fresh::DriverError::AlreadyProvided));
    assert_eq!(report.transitions.len(), 4);
    let mut machine = report.machine;
    assert_eq!(machine.phase(0), Some(Phase::Loading));
    assert!(!machine.retired(0));
    assert_eq!(machine.read(0, first()), Some(11));
    assert_eq!(machine.inverse_count(0), Some(2));
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert!(!machine.retired(1));
    // A retry also contributes no receipt and does not replace the old value.
    assert_eq!(machine.step(0), Err(fresh::DriverError::AlreadyProvided));
    assert_eq!(machine.read(0, first()), Some(11));
    assert_eq!(machine.inverse_count(0), Some(2));

    machine.retire(0).unwrap();
    machine.depart(0).unwrap();
    machine.unload(0).unwrap();
    assert_eq!(machine.phase(0), Some(Phase::Inactive));
    assert_eq!(machine.read(0, first()), None);
    assert_eq!(machine.inverse_count(0), Some(0));
    assert!(machine.retired(1));
    machine.remove(1).unwrap();
    machine.remove(0).unwrap();
}

#[test]
fn bootstrap_missing_publication_still_recovers_committed_provision_and_child() {
    let leaf = fresh::Blueprint::new(vec![], vec![], vec![fresh::Instruction::Unit]);
    let owner = fresh::Blueprint::new(
        vec![],
        vec![first(), second()],
        vec![
            fresh::Instruction::Child {
                blueprint: 0,
                next: Some(1),
            },
            fresh::Instruction::Provide {
                key: first(),
                value: 11,
                next: Some(2),
            },
        ],
    );
    let setup = [
        fresh::Command::Insert {
            parent: None,
            blueprint: 1,
        },
        fresh::Command::Begin { actor: 0 },
    ];
    let report = fresh::run_from_empty(vec![leaf, owner], &setup, 0);
    assert_eq!(report.actor, 0);
    assert_eq!(
        report.status,
        fresh::FromEmptyStatus::Blocked(fresh::DriverError::IncompleteProvision)
    );
    assert_eq!(report.steps, 2);
    assert_eq!(report.setup.len(), setup.len());
    let mut machine = report.machine;
    assert_eq!(machine.phase(0), Some(Phase::Loading));
    assert_eq!(machine.read(0, first()), Some(11));
    assert_eq!(machine.read(0, second()), None);
    // The terminal Unit failed: only the earlier Child and Provide committed.
    assert_eq!(machine.inverse_count(0), Some(2));
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    assert!(!machine.retired(1));
    assert_eq!(machine.phase(2), None);

    machine.retire(0).unwrap();
    machine.depart(0).unwrap();
    machine.unload(0).unwrap();
    assert_eq!(machine.phase(0), Some(Phase::Inactive));
    assert_eq!(machine.read(0, first()), None);
    assert_eq!(machine.read(0, second()), None);
    assert_eq!(machine.inverse_count(0), Some(0));
    assert!(machine.retired(1));
    assert_eq!(machine.phase(1), Some(Phase::Inactive));
    machine.remove(1).unwrap();
    machine.remove(0).unwrap();
}
