use cordis_kernel::cleanup_groups::CleanupGroups;
use cordis_kernel::lifecycle_state::registration::child::ChildSlot;
use cordis_kernel::lifecycle_state::registration::{PluginDefinition, RegisteredPlugin};
use cordis_kernel::lifecycle_state::LifecycleState;
use cordis_kernel::setup_work::SetupWork;
use cordis_kernel::{Error, Port};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

type Work = SetupWork<(), ()>;
type Groups = CleanupGroups<()>;
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn setup(domain: u64) -> (LifecycleState, usize, Work, Groups) {
    let mut state = LifecycleState::new(domain);
    let id = state.insert(None, vec![], vec![]).unwrap();
    let (mut work, groups): (Work, Groups) = state.begin_execution(id, domain + 1).unwrap();
    let receipt = work.issue_root(()).unwrap().run(|()| Ok::<(), ()>(()));
    assert!(work.complete_root(receipt).ok().unwrap().is_ok());
    (state, id, work, groups)
}
fn allocate<T>(
    state: &mut LifecycleState,
    slot: &mut ChildSlot<String>,
    key: u64,
    value: T,
) -> Result<RegisteredPlugin<T>, (Error, PluginDefinition<T>)> {
    state.register_child_slot(
        slot,
        &BTreeMap::new(),
        port(key),
        PluginDefinition::new(vec![], vec![], value),
    )
}

#[test]
fn native_assignment_is_once_and_retains_actual_recipe_and_inverse_identity() {
    assert!(ChildSlot::<String>::from_work(&Work::new(1)).is_none());
    let (mut state, parent, work, _) = setup(1100);
    let mut slot = ChildSlot::<String>::from_work(&work).unwrap();
    assert_eq!(slot.parent_id(), parent);
    assert!(slot.pending());
    let mut plugin = allocate(&mut state, &mut slot, 40, |value: String| {
        assert_eq!(value, "real request");
        Ok::<(), String>(())
    })
    .ok()
    .unwrap();
    assert_eq!(slot.identity().unwrap().id(), plugin.id());
    let children = state.kernel().children(parent);
    let error = allocate(&mut state, &mut slot, 41, Box::new(37u32))
        .err()
        .unwrap();
    assert_eq!(error.0, Error::InvalidState);
    assert_eq!(*error.1.into_payload(), 37);
    assert_eq!(state.kernel().children(parent), children);
    assert_eq!(
        slot.reject("late failure".to_owned()),
        Err("late failure".to_owned())
    );
    assert!(slot.error().is_none());
    let (mut child_work, child_groups): (Work, Groups) =
        state.begin_execution(plugin.id(), 1102).unwrap();
    let invocation = state
        .admit_registered_root(&plugin, &mut child_work, "real request".to_owned())
        .ok()
        .unwrap();
    let receipt = plugin.call(invocation).ok().unwrap();
    assert!(child_work.complete_root(receipt).ok().unwrap().is_ok());
    state
        .finish_execution(plugin.id(), &child_work, &child_groups)
        .unwrap();
    assert_eq!(
        state.retire_child_slot(&mut slot).unwrap().unwrap().id(),
        plugin.id()
    );
    assert!(state.kernel().retired(plugin.id()));
    assert!(!state.kernel().retired(parent));
}

#[test]
fn consumed_pending_inverse_blocks_late_allocation_through_the_same_shared_slot() {
    let (mut state, parent, work, _) = setup(1200);
    let request = Arc::new(Mutex::new(ChildSlot::<String>::from_work(&work).unwrap()));
    let inverse = Arc::clone(&request);
    // Mirror the two real handles; the inverse wins this ordering.
    assert_eq!(
        state.retire_child_slot(&mut inverse.lock().unwrap()),
        Ok(None)
    );
    assert!(!request.lock().unwrap().pending());
    let result = allocate(
        &mut state,
        &mut request.lock().unwrap(),
        50,
        "retained recipe".to_owned(),
    );
    let (error, definition) = result.err().unwrap();
    assert_eq!(error, Error::InvalidState);
    assert_eq!(definition.into_payload(), "retained recipe");
    assert_eq!(state.kernel().ids(), vec![parent]);
    assert_eq!(
        state.retire_child_slot(&mut inverse.lock().unwrap()),
        Ok(None)
    );
}

#[test]
fn allocation_failure_returns_recipe_and_failure_closes_only_the_actual_slot() {
    let (mut state, parent, work, _) = setup(1300);
    state.declare_provision(parent, port(60)).unwrap();
    let mut slot = ChildSlot::<String>::from_work(&work).unwrap();
    let definition = PluginDefinition::new(vec![], vec![60], Box::new(83u64));
    let (error, definition) = state
        .register_child_slot(&mut slot, &BTreeMap::new(), port(61), definition)
        .err()
        .unwrap();
    assert_eq!(error, Error::Conflict);
    assert_eq!(*definition.into_payload(), 83);
    assert!(slot.pending());
    assert_eq!(state.kernel().ids(), vec![parent]);
    slot.reject("real allocation failure".to_owned()).unwrap();
    assert!(allocate(&mut state, &mut slot, 62, ()).is_err());
    assert_eq!(
        slot.error().map(String::as_str),
        Some("real allocation failure")
    );
    assert_eq!(
        slot.reject("replacement".to_owned()),
        Err("replacement".to_owned())
    );
    assert_eq!(state.retire_child_slot(&mut slot), Ok(None));
    assert_eq!(
        slot.error().map(String::as_str),
        Some("real allocation failure")
    );
}

#[test]
fn foreign_runtime_cannot_allocate_or_cancel_an_equal_numeric_parent_request() {
    let (mut state, parent, work, _) = setup(1400);
    let (mut foreign, equal_parent, foreign_work, _) = setup(1500);
    assert_eq!(parent, equal_parent);
    let mut slot = ChildSlot::<String>::from_work(&work).unwrap();
    assert_eq!(
        allocate(&mut foreign, &mut slot, 70, ()).err().unwrap().0,
        Error::InvalidState
    );
    assert_eq!(
        foreign.retire_child_slot(&mut slot),
        Err(Error::InvalidState)
    );
    assert!(slot.pending());
    assert_eq!(foreign.kernel().ids(), vec![equal_parent]);
    let child = allocate(&mut state, &mut slot, 70, ()).ok().unwrap();
    let mut other_slot = ChildSlot::<String>::from_work(&foreign_work).unwrap();
    let other_child = allocate(&mut foreign, &mut other_slot, 70, ())
        .ok()
        .unwrap();
    assert_eq!(child.id(), other_child.id());
    assert_eq!(
        foreign.retire_child_slot(&mut slot),
        Err(Error::InvalidState)
    );
    assert!(!foreign.kernel().retired(other_child.id()));
}

#[test]
fn old_episode_slot_cannot_allocate_into_a_later_episode_of_the_same_parent() {
    let (mut state, parent, mut work, mut groups) = setup(1600);
    let mut old_slot = ChildSlot::<String>::from_work(&work).unwrap();
    state.finish_execution(parent, &work, &groups).unwrap();
    state.leave(parent).unwrap();
    work.withdraw();
    state.settle_execution(parent, &work, &groups).unwrap();
    state.begin_cleanup(parent).unwrap();
    state
        .release_execution(parent, &mut work, &mut groups)
        .unwrap();
    // Generation alone is not enough between Unload and the next Begin.
    assert_eq!(
        allocate(&mut state, &mut old_slot, 80, ()).err().unwrap().0,
        Error::InvalidState
    );
    assert!(old_slot.pending());
    assert_eq!(state.kernel().ids(), vec![parent]);
    let (new_work, _): (Work, Groups) = state.begin_execution(parent, 1602).unwrap();
    assert_eq!(
        allocate(&mut state, &mut old_slot, 80, ()).err().unwrap().0,
        Error::InvalidState
    );
    assert!(old_slot.pending());
    assert_eq!(state.kernel().ids(), vec![parent]);
    let mut new_slot = ChildSlot::<String>::from_work(&new_work).unwrap();
    assert!(allocate(&mut state, &mut new_slot, 80, ()).is_ok());
}

#[test]
fn completed_child_slot_never_targets_a_replacement_after_removal() {
    let (mut state, parent, work, _) = setup(1700);
    let mut slot = ChildSlot::<String>::from_work(&work).unwrap();
    let child = allocate(&mut state, &mut slot, 90, ()).ok().unwrap();
    state.retire_child_slot(&mut slot).unwrap();
    state.remove(child.id()).unwrap();
    let mut replacement_slot = ChildSlot::<String>::from_work(&work).unwrap();
    let replacement = allocate(&mut state, &mut replacement_slot, 90, ())
        .ok()
        .unwrap();
    assert_ne!(child.id(), replacement.id());
    assert_eq!(
        state.retire_child_slot(&mut slot).unwrap().unwrap().id(),
        child.id()
    );
    assert!(!state.kernel().retired(replacement.id()));
    assert!(!state.kernel().retired(parent));
    let mut owned = ChildSlot::<String>::from_identity(replacement.child_identity().unwrap());
    assert!(!owned.pending());
    assert_eq!(
        allocate(&mut state, &mut owned, 91, ()).err().unwrap().0,
        Error::InvalidState
    );
    assert!(state.retire_child_slot(&mut owned).unwrap().is_some());
}
