#[path = "support/update_recovery.rs"]
mod scenario;
fn main() {
    let r = scenario::run();
    println!("{{\"schema\":\"cordis-verus.update-recovery-native/v1\",\"status\":\"passed\",\"initialAction\":{},\"retryAction\":{},\"oldChild\":{},\"newChild\":{},\"finalValue\":{}}}",r.initial.action,r.retry.action,r.old_child,r.new_child,r.final_value);
}
