use cordis_kernel::lifecycle_state::cleanup::CleanupCommand as C;
use cordis_kernel::node_runtime::bridge::{Bridge, BridgeError};
use cordis_kernel::node_runtime::NodeRuntime;
use cordis_kernel::Port;
const PORT: Port = Port { key: 9, realm: 3 };

#[test]
fn callback_claims_retain_exact_fiber_and_recipe_until_real_completion() {
    let mut node = NodeRuntime::new(901);
    let mut host = Bridge::new(&node);
    let id = node.insert(None, vec![], vec![]).unwrap();
    let fiber = host.issue("actual Fiber").unwrap();
    let recipe = host.issue("revision A + arguments").unwrap();
    host.bind_fiber(&node, id, fiber).unwrap();
    let ticket = node.begin(id).unwrap();
    let call = host.begin_call(&node, ticket, fiber, recipe).unwrap();
    assert_eq!(
        host.begin_call(&node, ticket, fiber, recipe).err(),
        Some(BridgeError::Busy)
    );
    assert_eq!(host.get(call.recipe()), Some(&"revision A + arguments"));
    assert_eq!(host.remove(&node, recipe.id()), Err(BridgeError::Retained));
    assert_eq!(host.finish_call(&node, &call), Err(BridgeError::Busy));
    let mut wrong = ticket;
    wrong.generation += 1;
    assert!(node.complete(wrong, None).is_err());
    assert!(host.validate_call(&call));
    node.complete(ticket, None).unwrap();
    host.finish_call(&node, &call).unwrap();
    assert!(!host.validate_call(&call));
    assert_eq!(host.finish_call(&node, &call), Err(BridgeError::Stale));
    assert_eq!(
        host.remove(&node, recipe.id()),
        Ok(Some("revision A + arguments"))
    );
    let next = host.issue("revision B").unwrap();
    assert_ne!(next.id(), recipe.id());
    assert!(host.begin_call(&node, ticket, fiber, next).is_err());
    assert!(host.snapshot(&node).is_ok());
}

#[test]
fn retained_slots_and_aba_replacement_preserve_exact_foreign_reference() {
    let mut node = NodeRuntime::new(902);
    let mut host = Bridge::new(&node);
    let id = node.insert(None, vec![], vec![PORT]).unwrap();
    let fiber = host.issue("provider").unwrap();
    host.bind_fiber(&node, id, fiber).unwrap();
    let ticket = node.begin(id).unwrap();
    let a = host.issue("object A").unwrap();
    let b = host.issue("object B").unwrap();
    let publication = host.publish(&mut node, id, 1, PORT, a).unwrap().unwrap();
    node.complete(ticket, None).unwrap();
    node.finish(id).unwrap();
    let reader = node.insert(None, vec![PORT], vec![]).unwrap();
    let fiber = host.issue("consumer").unwrap();
    host.bind_fiber(&node, reader, fiber).unwrap();
    let ticket = node.begin(reader).unwrap();
    node.complete(ticket, None).unwrap();
    node.finish(reader).unwrap();
    host.replace(&mut node, id, 1, publication, b)
        .unwrap()
        .map_err(|e| e.error)
        .unwrap();
    host.replace(&mut node, id, 1, publication, a)
        .unwrap()
        .map_err(|e| e.error)
        .unwrap();
    let delivered = node.drain_released();
    assert!(!delivered.contains(&a.id()));
    assert_eq!(host.remove(&node, a.id()), Err(BridgeError::Retained));
    assert_eq!(host.remove(&node, b.id()), Ok(Some("object B")));
    node.withdraw_publications(id).unwrap();
    let (read, value) = host
        .resolve(&mut node, PORT, Some(reader), Some(1))
        .unwrap()
        .unwrap();
    assert_eq!(read.publication, publication);
    assert_eq!(*value, "object A");
    assert!(host.snapshot(&node).is_ok());
}

#[test]
fn wrong_domain_missing_projection_and_live_fiber_removal_reject() {
    let mut node = NodeRuntime::new(903);
    let mut foreign = NodeRuntime::new(904);
    let mut host = Bridge::new(&node);
    let mut other = Bridge::new(&foreign);
    let key = host.issue(10).unwrap();
    let foreign_key = other.issue(20).unwrap();
    assert_eq!(key.id(), foreign_key.id());
    assert_eq!(host.get(foreign_key), None);
    let id = node.insert(None, vec![], vec![]).unwrap();
    assert!(host.snapshot(&node).is_err());
    host.bind_fiber(&node, id, key).unwrap();
    assert_eq!(host.unbind_fiber(&node, id), Err(BridgeError::Retained));
    assert_eq!(host.bind_fiber(&node, id, key), Err(BridgeError::Bound));
    assert_eq!(host.bind_fiber(&foreign, id, key), Err(BridgeError::Domain));
    let foreign_id = foreign.insert(None, vec![], vec![PORT]).unwrap();
    foreign.begin(foreign_id).unwrap();
    assert_eq!(
        host.publish(&mut foreign, foreign_id, 1, PORT, key).err(),
        Some(BridgeError::Domain)
    );
    node.cleanup(C::Retire { id }).unwrap();
    node.cleanup(C::Remove { id }).unwrap();
    assert_eq!(host.unbind_fiber(&node, id), Ok(Some(key.id())));
    assert_eq!(host.remove(&node, key.id()), Ok(Some(10)));
}

#[test]
fn a_raw_numeric_write_cannot_pass_the_host_projection_check() {
    let mut node = NodeRuntime::new(905);
    let mut host = Bridge::new(&node);
    let id = node.insert(None, vec![], vec![PORT]).unwrap();
    let fiber = host.issue("provider").unwrap();
    host.bind_fiber(&node, id, fiber).unwrap();
    node.begin(id).unwrap();
    node.publish(id, 1, PORT, 500).map_err(|e| e.error).unwrap();
    assert!(host.snapshot(&node).is_err());
    assert_eq!(
        host.resolve(&mut node, PORT, Some(id), Some(1)).err(),
        Some(BridgeError::Unknown)
    );
}
