#[path = "../examples/support/update_recovery.rs"]
mod scenario;
#[test]
fn provider_update_waits_for_failed_child_and_restores_real_values() {
    let report = scenario::run();
    assert_eq!(report["status"], "passed");
}
