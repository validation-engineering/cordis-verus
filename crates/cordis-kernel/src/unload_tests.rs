//! Private-state regressions for the transaction boundary of MixedDriver unload.
//!
//! Ordinary Rust regressions in the `mixed_driver` module, outside `verus!`.
//! Each fixture starts through public calls, then changes private state. These
//! are not claimed to be reachable through public Mixed/Fresh API histories.
//! The intended representation argument is that an Unloading actor need not
//! have a complete table, and `wf` checks receipt ownership but not every inverse
//! domain. Removing an unused empty child through the private Kernel preserves
//! Kernel constraints while deliberately bypassing MixedDriver's retained check.
//! These runtime tests do not constitute machine-checked proofs of `wf`.

use super::{Blueprint, DriverError, Instruction, MixedDriver, Outcome, Receipt};
use crate::{Binding, Error, Phase, Port};

const SERVICE: Port = Port { key: 7, realm: 3 };
const OWN: Port = Port { key: 8, realm: 3 };

type NodeSnapshot = (bool, bool, Phase, bool, Option<usize>, u64);
type BlueprintSnapshot = (Vec<Port>, Vec<Port>, Vec<Instruction>);

#[derive(Debug, PartialEq, Eq)]
struct Snapshot {
    nodes: Vec<NodeSnapshot>,
    declarations: Vec<(usize, Port, bool)>,
    links: Vec<(usize, Binding, bool)>,
    blueprints: Vec<BlueprintSnapshot>,
    rows: Vec<(usize, Option<usize>, Vec<Receipt>)>,
    tables: Vec<Vec<(Port, Option<u64>)>>,
}

fn snapshot(driver: &MixedDriver) -> Snapshot {
    Snapshot {
        nodes: driver
            .kernel
            .nodes
            .iter()
            .map(|n| {
                (
                    n.present,
                    n.retired,
                    n.phase,
                    n.restoring,
                    n.parent,
                    n.generation,
                )
            })
            .collect(),
        declarations: driver
            .kernel
            .declarations
            .iter()
            .map(|d| (d.owner, d.port, d.provides))
            .collect(),
        links: driver
            .kernel
            .links
            .iter()
            .map(|l| (l.consumer, l.binding, l.live))
            .collect(),
        blueprints: driver
            .blueprints
            .iter()
            .map(|b| (b.dependencies.clone(), b.provisions.clone(), b.code.clone()))
            .collect(),
        rows: driver
            .rows
            .iter()
            .map(|r| (r.blueprint, r.current, r.journal.clone()))
            .collect(),
        tables: driver
            .tables
            .iter()
            .map(|t| t.slots.iter().map(|s| (s.key, s.value)).collect())
            .collect(),
    }
}

fn unloading_fixture() -> (MixedDriver, usize, usize, usize) {
    let leaf = Blueprint::new(vec![], vec![], vec![]);
    let provider = Blueprint::new(
        vec![],
        vec![SERVICE],
        vec![Instruction::Provide {
            key: SERVICE,
            value: 7,
            next: None,
        }],
    );
    let owner = Blueprint::new(
        vec![SERVICE],
        vec![OWN],
        vec![
            Instruction::Provide {
                key: OWN,
                value: 13,
                next: Some(1),
            },
            Instruction::Child {
                expected: 2,
                blueprint: 0,
                next: Some(2),
            },
            Instruction::Xor {
                key: SERVICE,
                mask: 5,
                next: Some(3),
            },
        ],
    );
    let mut driver = MixedDriver::new(vec![leaf, provider, owner]);
    let provider = driver.insert(None, 1).unwrap();
    driver.begin(provider).unwrap();
    driver.step(provider).unwrap();
    let actor = driver.insert(None, 2).unwrap();
    driver.begin(actor).unwrap();
    assert_eq!(driver.step(actor), Ok(Outcome::Advanced));
    assert_eq!(
        driver.step(actor),
        Ok(Outcome::Child {
            child: 2,
            finished: false
        })
    );
    assert_eq!(driver.step(actor), Ok(Outcome::Advanced));
    assert_eq!(driver.step(actor), Ok(Outcome::Finished));
    driver.retire(actor).unwrap();
    driver.depart(actor).unwrap();
    assert_eq!(driver.inverse_count(actor), Some(4));
    (driver, provider, actor, 2)
}

#[test]
fn missing_value_after_successful_inverses_rolls_back_every_private_buffer() {
    let (mut driver, provider, actor, child) = unloading_fixture();
    let slot = driver.tables[actor]
        .slots
        .iter()
        .position(|s| s.key == OWN)
        .unwrap();
    // Only the payload changes: slot keys/length/uniqueness, Kernel state,
    // rows and journals remain intact. The actor is already Unloading.
    driver.tables[actor].slots[slot].value = None;
    let before = snapshot(&driver);
    for _ in 0..2 {
        // Reverse order first handles Unit, Xor and Child, then this absent
        // provision fails. None of those earlier draft mutations may escape.
        assert_eq!(driver.unload(actor), Err(DriverError::MissingValue));
        assert_eq!(snapshot(&driver), before);
        assert_eq!(driver.read(provider, SERVICE), Some(7 ^ 5));
        assert!(!driver.retired(child));
        assert!(!driver.kernel.nodes[actor].restoring);
    }
    // Repair the private fixture, then retry the same public transaction.
    driver.tables[actor].slots[slot].value = Some(13);
    driver.unload(actor).unwrap();
    assert_eq!(driver.phase(actor), Some(Phase::Inactive));
    assert_eq!(driver.inverse_count(actor), Some(0));
    assert_eq!(driver.read(provider, SERVICE), Some(7));
    assert_eq!(driver.read(actor, OWN), None);
    assert!(driver.retired(child));
    assert!(!driver.kernel.nodes[actor].restoring);
}

#[test]
fn missing_captured_child_rejects_without_redirecting_or_leaking_prior_inverse_writes() {
    let (mut driver, provider, actor, child) = unloading_fixture();
    let registered_child = driver.kernel.nodes[child];
    // Bypass only the driver's retained-journal guard. This child is Inactive,
    // has no declarations/links/children, and the ordinary Kernel calls succeed.
    driver.kernel.retire(child).unwrap();
    driver.kernel.remove(child).unwrap();
    let before = snapshot(&driver);
    assert_eq!(
        driver.unload(actor),
        Err(DriverError::Kernel(Error::Unknown))
    );
    assert_eq!(snapshot(&driver), before);
    assert_eq!(driver.read(provider, SERVICE), Some(7 ^ 5));
    assert_eq!(driver.inverse_count(actor), Some(4));

    let replacement = driver.insert(Some(actor), 0).unwrap();
    assert_eq!(replacement, 3);
    let with_replacement = snapshot(&driver);
    assert_eq!(
        driver.unload(actor),
        Err(DriverError::Kernel(Error::Unknown))
    );
    assert_eq!(snapshot(&driver), with_replacement);
    assert!(!driver.retired(replacement));

    // Restoring this private fixture's original identity repairs the actual
    // inverse domain. A newly allocated child was not an acceptable substitute.
    driver.kernel.nodes[child] = registered_child;
    driver.unload(actor).unwrap();
    assert_eq!(driver.read(provider, SERVICE), Some(7));
    assert_eq!(driver.read(actor, OWN), None);
    assert_eq!(driver.inverse_count(actor), Some(0));
    assert!(driver.retired(child));
    assert!(!driver.retired(replacement));
    assert_eq!(driver.phase(replacement), Some(Phase::Inactive));
}
