#[path = "support/semantic_context.rs"]
mod scenario;

use cordis_kernel::mixed_driver::fresh::{run_inspected, DriverError};
use cordis_kernel::mixed_driver::{Inverse, Receipt};
use cordis_kernel::Error;

fn main() {
    let loaded = run_inspected(
        scenario::bank(),
        &scenario::setup(),
        1,
        scenario::own_service(),
        1,
    );
    assert_eq!(loaded.run.error, None);
    assert_eq!(loaded.value, Some(42));
    assert_eq!(
        loaded.inverse,
        Some(Receipt {
            actor: 1,
            inverse: Inverse::Child { child: 2 }
        })
    );
    println!(
        "loaded: own service = {:?}, captured inverse = {:?}",
        loaded.value, loaded.inverse
    );

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
    println!(
        "recovered: provider value = {:?}; child 2 is retired and still registered",
        restored.value
    );

    let failed = run_inspected(
        scenario::bank(),
        &scenario::conflicting_retry(),
        3,
        scenario::own_service(),
        1,
    );
    assert_eq!(failed.run.error, Some(DriverError::Kernel(Error::Conflict)));
    assert_eq!(failed.inverse, None);
    println!(
        "new parent: Child rejected with {:?}; no fabricated success or inverse",
        failed.run.error
    );
}
