use cordis_driver::Driver;
use serde_json::{json, Value};
fn command(driver: &mut Driver, value: Value) -> Value {
    serde_json::from_str(&driver.command(&value.to_string()).unwrap()).unwrap()
}
fn reserve(driver: &mut Driver) -> Value {
    command(driver, json!({"op":"mount","sealed":false}))["id"].clone()
}
fn cleanup(driver: &mut Driver, id: &Value) -> Value {
    let response = command(driver, json!({"op":"drive"}));
    assert_eq!(response["actions"].as_array().unwrap().len(), 1);
    assert_eq!(response["actions"][0]["kind"], "cleanup");
    assert_eq!(response["actions"][0]["id"], *id);
    response["actions"][0]["ticket"].clone()
}
fn removed(driver: &mut Driver, id: &Value) {
    assert_eq!(
        command(driver, json!({"op":"drive"}))["actions"],
        json!([{"kind":"removed","id":id}])
    );
}
#[test]
fn reserved_effect_cleanup_is_owned_before_retired_node_removal() {
    let mut driver = Driver::new().unwrap();
    let id = reserve(&mut driver);
    assert_eq!(
        command(&mut driver, json!({"op":"prepare","id":id}))["generation"],
        "0"
    );
    assert_eq!(
        command(
            &mut driver,
            json!({"op":"validate","id":id,"generation":"0"})
        )["valid"],
        true
    );
    command(&mut driver, json!({"op":"retire","id":id}));
    let ticket = cleanup(&mut driver, &id);
    assert_eq!(ticket["generation"], "0");
    assert_eq!(
        command(&mut driver, json!({"op":"drive"}))["actions"],
        json!([])
    );
    let snapshot = command(&mut driver, json!({"op":"snapshot"}));
    assert_eq!(snapshot["plugins"][0]["state"], "Unloading");
    assert_eq!(snapshot["plugins"][0]["pendingAction"], ticket);
    let mut forged = ticket.clone();
    forged["kind"] = json!("setup");
    assert_eq!(
        driver
            .command(&json!({"op":"complete","ticket":forged,"success":true}).to_string())
            .unwrap_err()
            .code,
        "StaleAction"
    );
    command(
        &mut driver,
        json!({"op":"complete","ticket":ticket,"success":true}),
    );
    removed(&mut driver, &id);
}
#[test]
fn reservation_cleanup_failure_retains_ownership_until_successful_explicit_retry() {
    let mut driver = Driver::new().unwrap();
    let id = reserve(&mut driver);
    command(&mut driver, json!({"op":"prepare","id":id}));
    command(&mut driver, json!({"op":"retire","id":id}));
    let ticket = cleanup(&mut driver, &id);
    command(
        &mut driver,
        json!({"op":"complete","ticket":ticket,"success":false,"error":"inverse failed"}),
    );
    assert_eq!(
        command(&mut driver, json!({"op":"drive"}))["actions"],
        json!([])
    );
    let snapshot = command(&mut driver, json!({"op":"snapshot"}));
    assert_eq!(snapshot["plugins"][0]["state"], "Unloading");
    assert_eq!(snapshot["plugins"][0]["cleanupFailed"], true);
    let retry =
        command(&mut driver, json!({"op":"retry_cleanup","id":id}))["actions"][0]["ticket"].clone();
    assert_ne!(retry["action"], ticket["action"]);
    assert_eq!(retry["generation"], "0");
    assert_eq!(
        driver
            .command(&json!({"op":"complete","ticket":ticket,"success":true}).to_string())
            .unwrap_err()
            .code,
        "StaleAction"
    );
    command(
        &mut driver,
        json!({"op":"complete","ticket":retry,"success":true}),
    );
    removed(&mut driver, &id);
}
#[test]
fn first_activation_absorbs_prepared_journal_into_the_normal_episode() {
    let mut driver = Driver::new().unwrap();
    let id = reserve(&mut driver);
    command(&mut driver, json!({"op":"prepare","id":id}));
    command(&mut driver, json!({"op":"seal","id":id,"dependencies":[]}));
    let setup = command(&mut driver, json!({"op":"drive"}))["actions"][0]["ticket"].clone();
    assert_eq!(setup["kind"], "setup");
    assert_eq!(setup["generation"], "1");
    command(
        &mut driver,
        json!({"op":"complete","ticket":setup,"success":true}),
    );
    assert_eq!(
        driver
            .command(&json!({"op":"prepare","id":id}).to_string())
            .unwrap_err()
            .code,
        "AdmissionClosed"
    );
    command(&mut driver, json!({"op":"retire","id":id}));
    let ticket = cleanup(&mut driver, &id);
    assert_eq!(ticket["generation"], "1");
    command(
        &mut driver,
        json!({"op":"complete","ticket":ticket,"success":true}),
    );
    removed(&mut driver, &id);
}
#[test]
fn cancellation_closes_reservation_admission_before_cleanup_starts() {
    let mut driver = Driver::new().unwrap();
    let id = reserve(&mut driver);
    command(&mut driver, json!({"op":"prepare","id":id}));
    command(&mut driver, json!({"op":"retire","id":id}));
    for request in [
        json!({"op":"prepare","id":id}),
        json!({"op":"validate","id":id,"generation":"0"}),
    ] {
        assert_eq!(
            driver.command(&request.to_string()).unwrap_err().code,
            "AdmissionClosed"
        );
    }
    let ticket = cleanup(&mut driver, &id);
    command(
        &mut driver,
        json!({"op":"complete","ticket":ticket,"success":true}),
    );
    removed(&mut driver, &id);
}

fn publish(driver: &mut Driver, id: &Value, generation: &str, value: &str) -> Value {
    command(
        driver,
        json!({"op":"publish","id":id,"generation":generation,"key":"1","realm":"0","value":value}),
    )["publication"]
        .clone()
}
fn resolve(driver: &mut Driver, consumer: Value) -> Value {
    command(
        driver,
        json!({"op":"resolve","consumer":consumer,"key":"1","realm":"0"}),
    )
}
#[test]
fn canceled_reservation_publication_survives_failed_inverse_and_releases_after_retry() {
    let mut driver = Driver::new().unwrap();
    let id = reserve(&mut driver);
    assert_eq!(driver.command(&json!({"op":"publish","id":id,"generation":"0","key":"1","realm":"0","value":"10"}).to_string()).unwrap_err().code,"AdmissionClosed");
    command(&mut driver, json!({"op":"prepare","id":id}));
    let publication = publish(&mut driver, &id, "0", "10");
    let binding = resolve(&mut driver, id.clone());
    assert_eq!(binding["publication"], publication);
    assert_eq!(binding["value"], "10");
    assert_eq!(resolve(&mut driver, Value::Null), Value::Null);
    command(&mut driver, json!({"op":"retire","id":id}));
    let ticket = cleanup(&mut driver, &id);
    assert_eq!(resolve(&mut driver, id.clone()), binding);
    command(
        &mut driver,
        json!({"op":"complete","ticket":ticket,"success":false,"error":"inverse failed"}),
    );
    assert_eq!(resolve(&mut driver, id.clone()), binding);
    assert_eq!(
        command(&mut driver, json!({"op":"drive"}))["released"],
        json!([])
    );
    let retry =
        command(&mut driver, json!({"op":"retry_cleanup","id":id}))["actions"][0]["ticket"].clone();
    assert_eq!(resolve(&mut driver, id.clone()), binding);
    command(
        &mut driver,
        json!({"op":"complete","ticket":retry,"success":true}),
    );
    let drained = command(&mut driver, json!({"op":"drive"}));
    assert_eq!(drained["released"], json!(["10"]));
    assert_eq!(drained["actions"], json!([{"kind":"removed","id":id}]));
    assert_eq!(
        command(&mut driver, json!({"op":"drive"}))["released"],
        json!([])
    );
}
#[test]
fn first_begin_adopts_publication_without_replacing_its_identity_or_value() {
    let mut driver = Driver::new().unwrap();
    let id = reserve(&mut driver);
    command(&mut driver, json!({"op":"prepare","id":id}));
    let publication = publish(&mut driver, &id, "0", "10");
    let consumer = command(
        &mut driver,
        json!({"op":"mount","dependencies":[{"key":"1","realm":"0"}]}),
    )["id"]
        .clone();
    assert_eq!(
        command(&mut driver, json!({"op":"drive"}))["actions"],
        json!([])
    );
    command(&mut driver, json!({"op":"seal","id":id,"dependencies":[]}));
    let setup = command(&mut driver, json!({"op":"drive"}))["actions"][0]["ticket"].clone();
    assert_eq!(setup["generation"], "1");
    assert_eq!(resolve(&mut driver, id.clone())["publication"], publication);
    command(
        &mut driver,
        json!({"op":"set","id":id,"generation":"1","publication":publication,"value":"11"}),
    );
    assert_eq!(
        driver
            .command(
                &json!({"op":"revoke","id":id,"generation":"0","publication":publication})
                    .to_string()
            )
            .unwrap_err()
            .code,
        "StalePublication"
    );
    command(
        &mut driver,
        json!({"op":"complete","ticket":setup,"success":true}),
    );
    let response = command(&mut driver, json!({"op":"drive"}));
    assert_eq!(response["released"], json!(["10"]));
    assert_eq!(response["actions"][0]["id"], consumer);
    assert_eq!(resolve(&mut driver, consumer)["publication"], publication);
    assert_eq!(resolve(&mut driver, Value::Null)["value"], "11");
}

#[test]
fn dynamic_reservation_transfers_to_prepared_owner_after_old_consumer_drains() {
    let mut driver = Driver::new().unwrap();
    let old = command(&mut driver, json!({"op":"mount"}))["id"].clone();
    let setup = command(&mut driver, json!({"op":"drive"}))["actions"][0]["ticket"].clone();
    let old_publication = publish(&mut driver, &old, "1", "10");
    command(
        &mut driver,
        json!({"op":"complete","ticket":setup,"success":true}),
    );
    let consumer = command(
        &mut driver,
        json!({"op":"mount","dependencies":[{"key":"1","realm":"0"}]}),
    )["id"]
        .clone();
    let setup = command(&mut driver, json!({"op":"drive"}))["actions"][0]["ticket"].clone();
    command(
        &mut driver,
        json!({"op":"complete","ticket":setup,"success":true}),
    );
    command(
        &mut driver,
        json!({"op":"revoke","id":old,"generation":"1","publication":old_publication}),
    );
    let ticket = cleanup(&mut driver, &consumer);
    let next = reserve(&mut driver);
    command(&mut driver, json!({"op":"prepare","id":next}));
    let publication = publish(&mut driver, &next, "0", "20");
    assert_eq!(resolve(&mut driver, consumer.clone())["value"], "10");
    assert_eq!(resolve(&mut driver, Value::Null), Value::Null);
    command(
        &mut driver,
        json!({"op":"complete","ticket":ticket,"success":true}),
    );
    command(
        &mut driver,
        json!({"op":"seal","id":next,"dependencies":[]}),
    );
    let setup = command(&mut driver, json!({"op":"drive"}))["actions"][0]["ticket"].clone();
    assert_eq!(setup["id"], next);
    command(
        &mut driver,
        json!({"op":"complete","ticket":setup,"success":true}),
    );
    let consumer_setup =
        command(&mut driver, json!({"op":"drive"}))["actions"][0]["ticket"].clone();
    assert_eq!(consumer_setup["id"], consumer);
    let binding = resolve(&mut driver, consumer);
    assert_eq!(binding["publication"], publication);
    assert_eq!(binding["owner"], next);
    assert_eq!(binding["value"], "20");
}
