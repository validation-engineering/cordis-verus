//! Audited serde boundary for the checked structured configuration operations.
//! Encoded scalar values are preserved; incoming objects use serde_json key order.
use cordis_kernel::configuration_data as checked;
use serde_json::Value;

pub(crate) fn encode(value: &Value) -> checked::Value {
    match value {
        Value::Array(items) => checked::Value::Array(items.iter().map(encode).collect()),
        Value::Object(items) => checked::Value::Object(
            items
                .iter()
                .map(|(key, value)| (key.clone(), encode(value)))
                .collect(),
        ),
        scalar => {
            let class = match scalar {
                Value::Null => checked::Class::Null,
                Value::Bool(_) => checked::Class::Boolean,
                Value::String(_) => checked::Class::String,
                Value::Number(number) => checked::Class::Number {
                    signed: number.as_i64(),
                    rank: number_rank(number.as_f64().expect("finite JSON number")),
                },
                _ => unreachable!(),
            };
            checked::Value::Atom(
                serde_json::to_string(scalar).expect("JSON scalar serialization"),
                class,
            )
        }
    }
}

pub(crate) fn decode(value: checked::Value) -> Value {
    match value {
        checked::Value::Atom(text, _) => {
            serde_json::from_str(&text).expect("scalar originated in encode")
        }
        checked::Value::Array(items) => Value::Array(items.into_iter().map(decode).collect()),
        checked::Value::Object(items) => Value::Object(
            items
                .into_iter()
                .map(|(key, value)| (key, decode(value)))
                .collect(),
        ),
    }
}

pub(crate) fn overlay(base: &Value, patch: &Value) -> Value {
    decode(checked::apply(&encode(base), &encode(patch)))
}

pub(crate) fn merge(base: &Value, ours: &Value, theirs: &Value) -> Result<Value, Vec<String>> {
    let (base, ours, theirs) = (encode(base), encode(ours), encode(theirs));
    checked::merge(Some(&base), Some(&ours), Some(&theirs))
        .map(|merged| decode(merged.value.expect("three present root objects")))
}

// IEEE-754 order encoding. JSON parsing supplies finite numbers; schema bounds
// may include infinities. Both signed zeroes compare equally. NaN bounds are
// omitted by schema translation, matching Rust's original range comparisons.
pub(crate) fn number_rank(number: f64) -> u64 {
    let bits = if number == 0.0 { 0 } else { number.to_bits() };
    if bits >> 63 == 1 {
        !bits
    } else {
        bits | (1 << 63)
    }
}
