use cordis_kernel::program::{Instruction, LandOutcome, ProgramDriver, ProgramDriverError};
use cordis_kernel::{Error, Phase, Port};

fn provider(driver: &mut ProgramDriver, port: Port) -> usize {
    driver
        .insert(
            None,
            vec![],
            vec![port],
            vec![Instruction::Set {
                index: 0,
                value: 17,
                next: 1,
            }],
            vec![0],
            1,
        )
        .unwrap()
}

fn activate(driver: &mut ProgramDriver, id: usize) {
    driver.begin(id).unwrap();
    loop {
        assert!(driver.admit(id).unwrap());
        if driver.land(id).unwrap() == LandOutcome::Terminal {
            break;
        }
    }
    driver.finish(id).unwrap();
}

#[test]
fn atomic_landing_executes_real_code_and_recovers_across_lifetimes() {
    let mut driver = ProgramDriver::new();
    let id = driver
        .insert(
            None,
            vec![],
            vec![Port { key: 1, realm: 0 }, Port { key: 2, realm: 0 }],
            vec![
                Instruction::Set {
                    index: 0,
                    value: 23,
                    next: 1,
                },
                Instruction::Copy {
                    source: 0,
                    index: 1,
                    next: 2,
                },
            ],
            vec![3, 5],
            7,
        )
        .unwrap();
    activate(&mut driver, id);
    assert_eq!(driver.read(id, 0), Some(23));
    assert_eq!(driver.read(id, 1), Some(23));
    driver.retire(id).unwrap();
    driver.depart(id).unwrap();
    driver.unload(id).unwrap();
    assert_eq!(driver.read(id, 0), Some(3));
    assert_eq!(driver.read(id, 1), Some(5));
    driver.remove(id).unwrap();
    let replacement = provider(&mut driver, Port { key: 1, realm: 0 });
    assert!(replacement > id);
    activate(&mut driver, replacement);
    assert_eq!(driver.read(replacement, 0), Some(17));
    assert_eq!(driver.read(id, 0), None);
}

#[test]
fn admitted_write_and_diversion_return_as_one_transition() {
    let mut driver = ProgramDriver::new();
    let id = provider(&mut driver, Port { key: 9, realm: 0 });
    driver.begin(id).unwrap();
    assert!(driver.admit(id).unwrap());
    driver.retire(id).unwrap();
    assert_eq!(driver.land(id), Ok(LandOutcome::Diverted));
    assert_eq!(driver.phase(id), Some(Phase::Unloading));
    assert_eq!(driver.read(id, 0), Some(17));
    assert_eq!(
        driver.land(id),
        Err(ProgramDriverError::Kernel(Error::InvalidState))
    );
    driver.unload(id).unwrap();
    assert_eq!(driver.read(id, 0), Some(0));
}

#[test]
fn provider_drift_lands_consumer_before_releasing_committed_provider() {
    let mut driver = ProgramDriver::new();
    let port = Port { key: 1, realm: 4 };
    let p = provider(&mut driver, port);
    activate(&mut driver, p);
    let c = driver
        .insert(
            None,
            vec![port],
            vec![Port { key: 2, realm: 4 }],
            vec![Instruction::Set {
                index: 0,
                value: 31,
                next: 1,
            }],
            vec![6],
            2,
        )
        .unwrap();
    driver.begin(c).unwrap();
    assert!(driver.admit(c).unwrap());
    driver.retire(p).unwrap();
    driver.depart(p).unwrap();
    assert_eq!(
        driver.unload(p),
        Err(ProgramDriverError::Kernel(Error::Relied))
    );
    assert_eq!(driver.land(c), Ok(LandOutcome::Diverted));
    assert_eq!(driver.read(c, 0), Some(31));
    driver.unload(c).unwrap();
    assert_eq!(driver.read(c, 0), Some(6));
    driver.unload(p).unwrap();
    assert_eq!(driver.read(p, 0), Some(0));
}

#[test]
fn terminal_landing_after_drift_uses_divert_and_can_recover_empty_journal() {
    let mut driver = ProgramDriver::new();
    let id = driver
        .insert(None, vec![], vec![], vec![], vec![], 0)
        .unwrap();
    driver.begin(id).unwrap();
    assert!(driver.admit(id).unwrap());
    driver.retire(id).unwrap();
    assert_eq!(driver.land(id), Ok(LandOutcome::Diverted));
    assert_eq!(driver.phase(id), Some(Phase::Unloading));
    driver.unload(id).unwrap();
    assert_eq!(driver.phase(id), Some(Phase::Inactive));
}

#[test]
fn terminal_landing_does_not_bypass_total_provision_gate() {
    let mut driver = ProgramDriver::new();
    let id = driver
        .insert(
            None,
            vec![],
            vec![Port { key: 1, realm: 0 }],
            vec![],
            vec![9],
            0,
        )
        .unwrap();
    driver.begin(id).unwrap();
    assert!(driver.admit(id).unwrap());
    assert_eq!(driver.land(id), Ok(LandOutcome::Terminal));
    assert_eq!(
        driver.finish(id),
        Err(ProgramDriverError::IncompleteProvision)
    );
    assert_eq!(driver.phase(id), Some(Phase::Loading));
    driver.retire(id).unwrap();
    driver.depart(id).unwrap();
    driver.unload(id).unwrap();
    assert_eq!(driver.read(id, 0), Some(9));
}
