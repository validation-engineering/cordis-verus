#[path = "../examples/support/update_recovery.rs"]
mod scenario;
#[test]
fn real_child_failure_preserves_dependencies_rejects_forged_restore_and_updates() {
    let r = scenario::run();
    assert!(r.retry.action > r.initial.action);
    assert_ne!(r.old_child, r.new_child);
    assert_eq!(r.final_value, 20);
}
