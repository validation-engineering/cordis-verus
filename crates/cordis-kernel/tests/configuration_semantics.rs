use cordis_kernel::configuration_binding::Modules;
use cordis_kernel::configuration_data::{self as data, Class, RoundTrip, Value};
use cordis_kernel::configuration_module::Definition;
use cordis_kernel::configuration_schema::{Field, Part, Reason, Schema};
use std::sync::Arc;

fn number(value: i64) -> Value {
    Value::Atom(
        value.to_string(),
        Class::Number {
            signed: Some(value),
            rank: 0,
        },
    )
}
fn object(items: Vec<(&str, Value)>) -> Value {
    Value::Object(
        items
            .into_iter()
            .map(|(key, value)| (key.into(), value))
            .collect(),
    )
}
fn field<'a>(value: &'a Value, name: &str) -> Option<&'a Value> {
    match value {
        Value::Object(items) => data::get(items, name),
        _ => None,
    }
}

#[test]
fn selected_module_interception_defaults_and_saved_recipe_share_one_binding() {
    let mut modules = Modules::new();
    let schema = Schema::Object {
        fields: vec![
            Field {
                name: "limit".into(),
                schema: Schema::Integer {
                    min: Some(1),
                    max: Some(10),
                },
                required: true,
                default: None,
            },
            Field {
                name: "retry".into(),
                schema: Schema::Integer {
                    min: Some(0),
                    max: Some(5),
                },
                required: false,
                default: Some(number(3)),
            },
        ],
        allow_unknown: false,
    };
    let original = Arc::new(Definition::new(1u32, Arc::new(schema)));
    modules.insert("worker".into(), original.clone());
    let patch = object(vec![("limit", number(4))]);
    let saved = modules
        .prepare(
            Some("worker"),
            object(vec![("limit", number(2))]),
            Some(&patch),
            "old realm",
        )
        .unwrap();
    assert!(Arc::ptr_eq(saved.selected().unwrap(), &original));
    assert!(field(saved.raw(), "limit").unwrap().equals(&number(2)));
    assert!(field(saved.config(), "limit").unwrap().equals(&number(4)));
    assert!(field(saved.config(), "retry").unwrap().equals(&number(3)));
    modules.insert(
        "worker".into(),
        Arc::new(Definition::new(2, Arc::new(Schema::Any))),
    );
    assert!(Arc::ptr_eq(saved.selected().unwrap(), &original));
    let derived = saved.with_scope("new realm");
    assert_eq!(*derived.scope(), "new realm");
    assert!(field(derived.config(), "limit").unwrap().equals(&number(4)));
    assert!(modules
        .prepare(Some("missing"), object(vec![]), None, ())
        .is_err());
    let group = modules
        .prepare(None, object(vec![("unused", number(8))]), None, ())
        .unwrap();
    assert!(group.selected().is_none());
    assert!(group.config().equals(group.raw()));
}

#[test]
fn complete_three_way_merge_preserves_external_edits_and_checks_deletions() {
    let base = object(vec![
        ("local", number(1)),
        ("disk", number(1)),
        ("removed", number(7)),
    ]);
    let ours = object(vec![("local", number(2)), ("disk", number(1))]);
    let theirs = object(vec![
        ("local", number(1)),
        ("disk", number(3)),
        ("removed", number(7)),
        ("new", number(4)),
    ]);
    let merged = data::merge(Some(&base), Some(&ours), Some(&theirs))
        .unwrap()
        .value
        .unwrap();
    for (key, expected) in [("local", 2), ("disk", 3), ("new", 4)] {
        assert!(field(&merged, key).unwrap().equals(&number(expected)));
    }
    assert!(field(&merged, "removed").is_none());
    assert!(data::merge(Some(&number(1)), Some(&number(2)), Some(&number(3))).is_err());
    assert!(data::merge(Some(&number(1)), None, Some(&number(2))).is_err());
}

#[test]
fn roundtrip_and_order_check_whole_content_and_do_not_drop_unlisted_members() {
    let wanted = object(vec![("nested", object(vec![("value", number(1))]))]);
    let wrong = object(vec![("nested", object(vec![("value", number(2))]))]);
    assert!(matches!(
        RoundTrip::check("documents", &wanted, &wrong),
        Err("documents")
    ));
    assert_eq!(
        RoundTrip::check("documents", &wanted, &wanted)
            .ok()
            .unwrap()
            .into_inner(),
        "documents"
    );
    let items = vec![("one".to_owned(), number(1)), ("two".to_owned(), number(2))];
    assert!(data::ordered(&items, &["one".into()]).is_err());
    assert!(data::ordered(&items, &["one".into(), "one".into()]).is_err());
    assert!(data::ordered(&items, &["one".into(), "absent".into()]).is_err());
    let ordered = data::ordered(&items, &["two".into(), "one".into()]).unwrap();
    assert!(ordered[0].equals(&number(2)));
}

#[test]
fn defaults_and_nested_array_failures_are_checked_before_acceptance() {
    let schema = Schema::Object {
        fields: vec![Field {
            name: "items".into(),
            schema: Schema::Array(Box::new(Schema::Integer {
                min: Some(1),
                max: Some(3),
            })),
            required: false,
            default: Some(Value::Array(vec![number(0)])),
        }],
        allow_unknown: false,
    };
    let error = schema.validate(&object(vec![])).unwrap_err();
    assert_eq!(error.reason, Reason::Range);
    assert!(matches!(&error.path[..], [Part::Field(name), Part::Index(0)] if name == "items"));
    let value = object(vec![("items", Value::Array(vec![number(1), number(3)]))]);
    assert!(schema.validate(&value).unwrap().equals(&value));
}
