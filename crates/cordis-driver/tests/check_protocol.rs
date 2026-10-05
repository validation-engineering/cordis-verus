//! Exercise the real decimal-string JSON boundary used by the native adapter.
use cordis_driver::Driver;
use serde_json::{json, Value};

fn command(driver: &mut Driver, value: Value) -> Value {
    serde_json::from_str(&driver.command(&value.to_string()).unwrap()).unwrap()
}
fn rejected(driver: &mut Driver, value: Value) -> &'static str {
    driver.command(&value.to_string()).unwrap_err().code
}
fn port() -> Value {
    json!({"key":"1","realm":"0"})
}
fn mount(driver: &mut Driver, dependencies: Value) -> String {
    command(driver, json!({"op":"mount","dependencies":dependencies}))["id"]
        .as_str()
        .unwrap()
        .into()
}
fn action(driver: &mut Driver, id: &str, kind: &str) -> Value {
    let response = command(driver, json!({"op":"drive"}));
    let actions = response["actions"].as_array().unwrap();
    assert_eq!(actions.len(), 1, "unexpected action batch {actions:?}");
    assert_eq!(actions[0]["id"], id);
    assert_eq!(actions[0]["kind"], kind);
    actions[0]["ticket"].clone()
}
fn complete(driver: &mut Driver, ticket: Value) {
    command(
        driver,
        json!({"op":"complete","ticket":ticket,"success":true}),
    );
}
fn provider(driver: &mut Driver, checked: bool, value: &str) -> (String, String, String) {
    let id = mount(driver, json!([]));
    let ticket = action(driver, &id, "setup");
    let generation = ticket["generation"].as_str().unwrap().to_owned();
    let publication = command(driver,json!({"op":"publish","id":id,"generation":generation,"key":"1","realm":"0","value":value,"check":checked}))["publication"].as_str().unwrap().to_owned();
    complete(driver, ticket);
    (id, generation, publication)
}
struct Checked {
    driver: Driver,
    provider: String,
    generation: String,
    publication: String,
    consumer: String,
    ticket: Value,
}
impl Checked {
    fn new() -> Self {
        let mut driver = Driver::new().unwrap();
        let (provider, generation, publication) = provider(&mut driver, true, "10");
        let consumer = mount(&mut driver, json!([port()]));
        let ticket = command(&mut driver, json!({"op":"checks"}))["checks"][0]["ticket"].clone();
        Self {
            driver,
            provider,
            generation,
            publication,
            consumer,
            ticket,
        }
    }
}

#[test]
fn changed_value_rejects_check_result_and_requires_an_explicit_notification() {
    let mut test = Checked::new();
    command(
        &mut test.driver,
        json!({"op":"set","id":test.provider,"generation":test.generation,"publication":test.publication,"value":"11"}),
    );
    assert_eq!(
        command(
            &mut test.driver,
            json!({"op":"validate_check","ticket":test.ticket})
        )["current"],
        false
    );
    assert_eq!(
        command(
            &mut test.driver,
            json!({"op":"complete_check","ticket":test.ticket,"available":true})
        )["accepted"],
        false
    );
    assert_eq!(
        command(&mut test.driver, json!({"op":"checks"}))["checks"],
        json!([])
    );
    assert_eq!(
        command(&mut test.driver, json!({"op":"drive"}))["actions"],
        json!([])
    );
    let checks = command(&mut test.driver, json!({"op":"notify","ports":[port()]}));
    assert_eq!(checks["checks"][0]["value"], "11");
    let ticket = checks["checks"][0]["ticket"].clone();
    assert_eq!(ticket["value_revision"], "1");
    assert_eq!(
        command(
            &mut test.driver,
            json!({"op":"complete_check","ticket":ticket,"available":true})
        )["accepted"],
        true
    );
    action(&mut test.driver, &test.consumer, "setup");
}

#[test]
fn late_old_notification_cannot_overwrite_the_newer_accepted_result() {
    let mut test = Checked::new();
    let ticket = command(&mut test.driver, json!({"op":"notify","ports":[port()]}))["checks"][0]
        ["ticket"]
        .clone();
    assert_ne!(ticket["notification"], test.ticket["notification"]);
    assert_eq!(
        command(
            &mut test.driver,
            json!({"op":"complete_check","ticket":ticket,"available":true})
        )["accepted"],
        true
    );
    assert_eq!(
        command(
            &mut test.driver,
            json!({"op":"complete_check","ticket":test.ticket,"available":false})
        )["accepted"],
        false
    );
    action(&mut test.driver, &test.consumer, "setup");
    assert_eq!(
        command(&mut test.driver, json!({"op":"checks"}))["checks"],
        json!([])
    );
}

#[test]
fn forged_and_cross_domain_checks_do_not_consume_the_authentic_ticket() {
    let mut test = Checked::new();
    for field in [
        "consumer",
        "publication",
        "value_revision",
        "notification",
        "action",
    ] {
        let mut ticket = test.ticket.clone();
        ticket[field] = json!("999999");
        assert_eq!(
            rejected(
                &mut test.driver,
                json!({"op":"complete_check","ticket":ticket,"available":true})
            ),
            "StaleCheck"
        );
    }
    let mut other = Driver::new().unwrap();
    assert_eq!(
        rejected(
            &mut other,
            json!({"op":"complete_check","ticket":test.ticket,"available":true})
        ),
        "WrongDomain"
    );
    assert_eq!(
        command(
            &mut test.driver,
            json!({"op":"validate_check","ticket":test.ticket})
        )["current"],
        true
    );
    assert_eq!(
        command(
            &mut test.driver,
            json!({"op":"complete_check","ticket":test.ticket,"available":true})
        )["accepted"],
        true
    );
    assert_eq!(
        rejected(
            &mut test.driver,
            json!({"op":"complete_check","ticket":test.ticket,"available":true})
        ),
        "StaleCheck"
    );
}

#[test]
fn removed_consumer_acknowledges_outstanding_check_once_without_resurrection() {
    let mut test = Checked::new();
    command(&mut test.driver, json!({"op":"retire","id":test.consumer}));
    let actions = command(&mut test.driver, json!({"op":"drive"}));
    assert_eq!(
        actions["actions"],
        json!([{"kind":"removed","id":test.consumer}])
    );
    assert_eq!(
        command(
            &mut test.driver,
            json!({"op":"complete_check","ticket":test.ticket,"available":true})
        )["accepted"],
        false
    );
    assert_eq!(
        rejected(
            &mut test.driver,
            json!({"op":"complete_check","ticket":test.ticket,"available":true})
        ),
        "StaleCheck"
    );
    assert_eq!(
        command(&mut test.driver, json!({"op":"snapshot"}))["checkErrors"],
        json!([])
    );
}

#[test]
fn observer_cancellation_before_seal_cannot_start_the_reserved_child() {
    let mut driver = Driver::new().unwrap();
    let id = command(&mut driver, json!({"op":"mount","sealed":false}))["id"].clone();
    assert_eq!(
        command(&mut driver, json!({"op":"drive"}))["actions"],
        json!([])
    );
    command(&mut driver, json!({"op":"retire","id":id}));
    command(
        &mut driver,
        json!({"op":"seal","id":id,"dependencies":[port()]}),
    );
    assert_eq!(
        command(&mut driver, json!({"op":"drive"}))["actions"],
        json!([{"kind":"removed","id":id}])
    );
    assert_eq!(
        command(&mut driver, json!({"op":"snapshot"}))["plugins"],
        json!([])
    );
}

#[test]
fn seal_observes_final_dependency_declarations_before_setup_admission() {
    let mut driver = Driver::new().unwrap();
    let id = command(&mut driver, json!({"op":"mount","sealed":false}))["id"]
        .as_str()
        .unwrap()
        .to_owned();
    command(
        &mut driver,
        json!({"op":"seal","id":id,"dependencies":[port()]}),
    );
    assert_eq!(
        command(&mut driver, json!({"op":"drive"}))["actions"],
        json!([])
    );
    provider(&mut driver, false, "10");
    action(&mut driver, &id, "setup");
}

#[test]
fn replacement_root_lookup_changes_before_old_committed_lease_is_reclaimed() {
    let mut driver = Driver::new().unwrap();
    let (old, generation, publication) = provider(&mut driver, false, "10");
    let consumer = mount(&mut driver, json!([port()]));
    let setup = action(&mut driver, &consumer, "setup");
    complete(&mut driver, setup);
    command(
        &mut driver,
        json!({"op":"revoke","id":old,"generation":generation,"publication":publication}),
    );
    let cleanup = action(&mut driver, &consumer, "cleanup");
    let (new, _, _) = provider(&mut driver, false, "20");
    assert_eq!(
        command(&mut driver, json!({"op":"resolve","key":"1","realm":"0"}))["owner"],
        new
    );
    assert_eq!(
        command(
            &mut driver,
            json!({"op":"resolve","key":"1","realm":"0","consumer":consumer})
        )["value"],
        "10"
    );
    assert_eq!(
        command(
            &mut driver,
            json!({"op":"reclaim","id":old,"generation":generation,"publication":publication})
        )["drained"],
        false
    );
    complete(&mut driver, cleanup);
    assert_eq!(
        command(
            &mut driver,
            json!({"op":"reclaim","id":old,"generation":generation,"publication":publication})
        )["drained"],
        true
    );
    action(&mut driver, &consumer, "setup");
    assert_eq!(
        command(
            &mut driver,
            json!({"op":"resolve","key":"1","realm":"0","consumer":consumer})
        )["value"],
        "20"
    );
    assert_eq!(
        command(&mut driver, json!({"op":"snapshot"}))["plugins"]
            .as_array()
            .unwrap()
            .iter()
            .find(|p| p["id"] == old)
            .unwrap()["state"],
        "Active"
    );
}

#[test]
fn harness_failure_stays_latched_until_a_relevant_external_notification() {
    let mut driver = Driver::new().unwrap();
    command(&mut driver, json!({"op":"configure","profile":"harness"}));
    provider(&mut driver, false, "10");
    let consumer = mount(&mut driver, json!([port()]));
    let setup = action(&mut driver, &consumer, "setup");
    command(
        &mut driver,
        json!({"op":"complete","ticket":setup,"success":false,"error":"setup failed"}),
    );
    let cleanup = action(&mut driver, &consumer, "cleanup");
    complete(&mut driver, cleanup);
    for _ in 0..3 {
        assert_eq!(
            command(&mut driver, json!({"op":"drive"}))["actions"],
            json!([])
        );
    }
    command(
        &mut driver,
        json!({"op":"notify","ports":[{"key":"2","realm":"0"}]}),
    );
    assert_eq!(
        command(&mut driver, json!({"op":"drive"}))["actions"],
        json!([])
    );
    command(&mut driver, json!({"op":"notify","ports":[port()]}));
    action(&mut driver, &consumer, "setup");
}
