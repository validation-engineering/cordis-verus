use cordis_kernel::program::{Instruction, LandOutcome, ProgramDriver};
use cordis_kernel::{Phase, Port};

fn land(driver: &mut ProgramDriver, id: usize) -> LandOutcome {
    assert!(driver.admit(id).unwrap());
    driver.land(id).unwrap()
}

fn activate(driver: &mut ProgramDriver, id: usize) {
    driver.begin(id).unwrap();
    while land(driver, id) != LandOutcome::Terminal {}
    driver.finish(id).unwrap();
}

// Both histories use exactly the same external Insert/Retire/Remove sequence.
// One consumer reaches Active before provider retirement; the other has an
// admitted branch land after drift. Unrelated work is interleaved differently.
fn replacement_history(in_flight: bool) -> Vec<(Option<Phase>, Option<u64>)> {
    let mut driver = ProgramDriver::new();
    let dependency = Port { key: 10, realm: 2 };
    let old = driver
        .insert(
            None,
            vec![],
            vec![dependency],
            vec![Instruction::Set {
                index: 0,
                value: 11,
                next: 1,
            }],
            vec![0],
            10,
        )
        .unwrap();
    let consumer = driver
        .insert(
            None,
            vec![dependency],
            vec![Port { key: 20, realm: 2 }],
            vec![
                Instruction::BranchWrite {
                    test: 0,
                    expected: 7,
                    index: 0,
                    equal_value: 42,
                    unequal_value: 37,
                    equal_next: 3,
                    unequal_next: 2,
                },
                Instruction::Set {
                    index: 0,
                    value: 99,
                    next: 3,
                },
                Instruction::Set {
                    index: 0,
                    value: 100,
                    next: 3,
                },
            ],
            vec![7],
            20,
        )
        .unwrap();
    let other = driver
        .insert(
            None,
            vec![],
            vec![Port { key: 30, realm: 2 }],
            vec![
                Instruction::Set {
                    index: 0,
                    value: 4,
                    next: 1,
                },
                Instruction::Set {
                    index: 0,
                    value: 9,
                    next: 2,
                },
            ],
            vec![3],
            30,
        )
        .unwrap();
    if in_flight {
        driver.begin(other).unwrap();
        assert_eq!(land(&mut driver, other), LandOutcome::Advanced);
    }
    activate(&mut driver, old);
    if in_flight {
        driver.begin(consumer).unwrap();
        assert!(driver.admit(consumer).unwrap());
    } else {
        activate(&mut driver, consumer);
        activate(&mut driver, other);
    }
    driver.retire(old).unwrap();
    driver.depart(old).unwrap();
    if in_flight {
        assert_eq!(driver.land(consumer).unwrap(), LandOutcome::Diverted);
        assert_eq!(land(&mut driver, other), LandOutcome::Advanced);
        assert_eq!(land(&mut driver, other), LandOutcome::Terminal);
        driver.finish(other).unwrap();
    } else {
        driver.depart(consumer).unwrap();
    }
    assert_eq!(driver.read(consumer, 0), Some(42));
    driver.unload(consumer).unwrap();
    assert_eq!(driver.read(consumer, 0), Some(7));
    driver.unload(old).unwrap();
    driver.remove(old).unwrap();
    let replacement = driver
        .insert(
            None,
            vec![],
            vec![dependency],
            vec![Instruction::Set {
                index: 0,
                value: 55,
                next: 1,
            }],
            vec![1],
            40,
        )
        .unwrap();
    assert!(replacement > other);
    activate(&mut driver, replacement);
    activate(&mut driver, consumer);
    (0..=replacement)
        .map(|id| (driver.phase(id), driver.read(id, 0)))
        .collect()
}

#[test]
fn quiet_values_agree_after_different_schedules_and_provider_replacement() {
    let completed = replacement_history(false);
    let interrupted = replacement_history(true);
    assert_eq!(completed, interrupted);
    assert_eq!(
        completed,
        vec![
            (None, None),
            (Some(Phase::Active), Some(42)),
            (Some(Phase::Active), Some(9)),
            (Some(Phase::Active), Some(55)),
        ]
    );
}
