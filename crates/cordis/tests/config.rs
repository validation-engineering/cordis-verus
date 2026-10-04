use cordis::config::{merge, ConfigScope, Field, Schema};
use cordis::loader::ConfigTree;
use cordis::{Context, ServiceKey};
use serde_json::json;

#[test]
fn schema_checks_nested_fields_defaults_ranges_and_unknown_keys() {
    let schema = Schema::object([
        ("name", Field::required(Schema::String)),
        ("attempts", Field::defaulted(Schema::integer(1, 10), 3)),
        (
            "options",
            Field::optional(Schema::Array(Box::new(Schema::object([(
                "enabled",
                Field::required(Schema::Boolean),
            )])))),
        ),
    ]);
    let input = json!({"name":"agent"});
    assert_eq!(
        schema.validate(&input).unwrap(),
        json!({"name":"agent","attempts":3})
    );
    assert_eq!(input, json!({"name":"agent"}));
    assert_eq!(schema.validate(&json!({})).unwrap_err().path, "$.name");
    assert_eq!(
        schema
            .validate(&json!({"name":"x","attempts":11}))
            .unwrap_err()
            .path,
        "$.attempts"
    );
    assert_eq!(
        schema
            .validate(&json!({"name":"x","attempts":2.5}))
            .unwrap_err()
            .path,
        "$.attempts"
    );
    assert_eq!(
        schema
            .validate(&json!({"name":"x","typo":true}))
            .unwrap_err()
            .path,
        "$.typo"
    );
    assert_eq!(
        schema
            .validate(&json!({"name":"x","options":[{"enabled":"yes"}]}))
            .unwrap_err()
            .path,
        "$.options[0].enabled"
    );
}

#[test]
fn defaults_are_validated_and_nullable_enum_values_are_explicit() {
    let invalid_default = Schema::object([("n", Field::defaulted(Schema::integer(1, 5), 0))]);
    assert!(invalid_default.validate(&json!({})).is_err());
    let enum_schema = Schema::Nullable(Box::new(Schema::Enum(vec![json!("fast"), json!("safe")])));
    assert!(enum_schema.validate(&json!(null)).is_ok());
    assert!(enum_schema.validate(&json!("fast")).is_ok());
    assert!(enum_schema.validate(&json!("other")).is_err());
}

#[test]
fn extension_and_interception_inherit_without_mutating_parent() {
    #[derive(Debug, PartialEq)]
    struct ScopeName(&'static str);
    let key = ServiceKey::<u32>::new("service");
    let root = ConfigScope::new(Context::new())
        .extend(ScopeName("parent"))
        .intercept(
            "llm",
            json!({"retry":3,"model":{"name":"base","temperature":0.2}}),
        );
    let child = root
        .extend(ScopeName("child"))
        .with_context(root.context().isolate(key))
        .intercept("llm", json!({"model":{"name":"child"}}));
    assert_eq!(*root.metadata::<ScopeName>().unwrap(), ScopeName("parent"));
    assert_eq!(*child.metadata::<ScopeName>().unwrap(), ScopeName("child"));
    assert_ne!(root.context().port(key), child.context().port(key));
    assert_eq!(
        child.resolve(
            "llm",
            &json!({"retry":0,"model":{"name":"local"},"stream":true})
        ),
        json!({"retry":3,"model":{"name":"child","temperature":0.2},"stream":true})
    );
    assert_eq!(root.resolve("llm", &json!({}))["model"]["name"], "base");
    assert_eq!(
        merge(&json!({"a":[1],"b":true}), &json!({"a":[2],"b":null})),
        json!({"a":[2],"b":null})
    );
}

#[test]
fn text_config_rejects_typos_and_roundtrips() {
    let tree = ConfigTree::from_json(r#"[{"id":"workspace","children":[{"id":"agent","name":"agent","config":{"model":"v4"}}]}]"#).unwrap();
    assert_eq!(
        ConfigTree::from_json(&tree.to_json().unwrap()).unwrap(),
        tree
    );
    assert!(ConfigTree::from_json(r#"[{"id":"workspace","enabeld":false}]"#).is_err());
    assert!(ConfigTree::from_json(r#"[{"id":"workspace","enabled":"false"}]"#).is_err());
}
