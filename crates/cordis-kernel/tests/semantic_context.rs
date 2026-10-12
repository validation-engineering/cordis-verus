#[path = "../examples/support/semantic_context.rs"]
mod scenario;

use cordis_kernel::mixed_driver::fresh::{run_inspected, DriverError};
use cordis_kernel::mixed_driver::{Inverse, Receipt};
use cordis_kernel::{Error, Phase};

#[test]
fn interpreted_values_and_actual_captured_child_agree_with_execution() {
    let report = run_inspected(
        scenario::bank(),
        &scenario::setup(),
        1,
        scenario::own_service(),
        1,
    );
    assert_eq!(report.run.error, None);
    assert_eq!(report.value, Some(42));
    assert_eq!(
        report.inverse,
        Some(Receipt {
            actor: 1,
            inverse: Inverse::Child { child: 2 }
        })
    );
    assert_eq!(report.run.machine.read(0, scenario::service()), Some(7 ^ 5));
    assert_eq!(
        report.run.machine.inverse_at(1, 0),
        Some(Receipt {
            actor: 1,
            inverse: Inverse::Xor {
                provider: 0,
                key: scenario::service(),
                mask: 5
            },
        })
    );
    assert_eq!(report.run.machine.phase(1), Some(Phase::Active));
    assert_eq!(report.run.machine.inverse_at(1, 3), None);
    assert_eq!(report.run.machine.inverse_at(999, 0), None);
    assert_eq!(report.run.machine.read(999, scenario::service()), None);
}

#[test]
fn service_recovery_does_not_remove_the_retired_child_reservation() {
    let restored = run_inspected(
        scenario::bank(),
        &scenario::cleanup(),
        0,
        scenario::service(),
        0,
    );
    assert_eq!(restored.run.error, None);
    assert_eq!(restored.value, Some(7));
    assert!(restored.run.machine.retired(2));
    assert_eq!(restored.run.machine.phase(2), Some(Phase::Inactive));
    assert_eq!(restored.run.machine.read(1, scenario::own_service()), None);
    assert_eq!(restored.run.machine.inverse_at(1, 0), None);

    let failed = run_inspected(
        scenario::bank(),
        &scenario::conflicting_retry(),
        3,
        scenario::own_service(),
        1,
    );
    assert_eq!(failed.run.error, Some(DriverError::Kernel(Error::Conflict)));
    assert_eq!(
        failed.run.transitions.len() + 1,
        scenario::conflicting_retry().len()
    );
    assert_eq!(failed.run.machine.phase(3), Some(Phase::Loading));
    assert_eq!(failed.value, None);
    assert_eq!(failed.inverse, None);
    assert_eq!(failed.run.machine.inverse_count(3), Some(1));
    // The earlier successful XOR is retained; the failed Child adds no receipt.
    assert_eq!(failed.run.machine.read(0, scenario::service()), Some(7 ^ 5));
    assert!(failed.run.machine.retired(2));
}
