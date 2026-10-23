//! Machine-readable execution of real lifecycle scenarios. This is a behavioral
//! adapter, not a substitute implementation or a claim of whole-host verification.
#[path = "support/lifecycle_scenarios/native.rs"]
mod native;
use serde_json::{json, Value};
use std::io::{self, BufRead, Write};

fn run(request: Value) -> Value {
    let cases = request
        .get("cases")
        .and_then(Value::as_array)
        .expect("request.cases must be an array");
    assert!(cases.len() <= 256, "bounded batch size");
    let results = cases.iter().map(|case| {
        if case.get("profile").and_then(Value::as_str) != Some("native-managed/v1") {
            json!({"id":case.get("id"),"status":"unsupported","reason":"native adapter supports native-managed/v1"})
        } else { native::run(case.clone()) }
    }).collect::<Vec<_>>();
    json!({"schema":"cordis-verus.lifecycle-execution/v1","backend":"native-managed",
        "runtime":{"crate":"cordis-kernel","version":env!("CARGO_PKG_VERSION")},"results":results})
}
fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    match args.as_slice() {
        [mode] if mode == "--stdio" => {
            for line in io::stdin().lock().lines() {
                let line = line.expect("read scenario request");
                assert!(line.len() <= 16 * 1024 * 1024, "bounded input size");
                let reply = run(serde_json::from_str(&line).expect("scenario JSON"));
                println!("{reply}");
                io::stdout().flush().unwrap();
            }
        }
        [flag, path] if flag == "--input" => {
            let input = std::fs::read_to_string(path).expect("read scenario file");
            assert!(input.len() <= 16 * 1024 * 1024, "bounded input size");
            println!(
                "{}",
                run(serde_json::from_str(&input).expect("scenario JSON"))
            );
        }
        [] => {
            let result = run(serde_json::from_str(include_str!(
                "support/lifecycle_scenarios/baseline.json"
            ))
            .unwrap());
            let case = &result["results"][0];
            assert_eq!(case["status"], "executed");
            let last = case["steps"].as_array().unwrap().last().unwrap();
            assert!(last["state"]["plugins"].as_array().unwrap().is_empty());
            assert_eq!(last["state"]["values"][0]["depth"], 0);
            println!("{result}");
        }
        _ => {
            eprintln!("Usage: lifecycle_scenario [--input FILE | --stdio]");
            std::process::exit(2);
        }
    }
}
