//! Run: cargo run -p cordis-verus --example update_recovery --offline
#[path = "support/update_recovery.rs"]
mod scenario;
fn main() {
    println!(
        "{}",
        serde_json::to_string_pretty(&scenario::run()).unwrap()
    );
}
