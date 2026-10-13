use cordis_kernel::cleanup_groups::CleanupGroups;
use cordis_kernel::lifecycle_state::registration::{PluginDefinition, RegisteredPlugin};
use cordis_kernel::lifecycle_state::LifecycleState;
use cordis_kernel::setup_work::{RootDispatch, RootOutput, RootStatus, SetupWork};
use cordis_kernel::{Error, Phase, Port};
use std::collections::BTreeMap;
use std::future::Future;
use std::pin::pin;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc, Mutex,
};
use std::task::{Context, Poll, Waker};

type Work = SetupWork<String, String>;
type Groups = CleanupGroups<String>;
fn port(key: u64, realm: u64) -> Port {
    Port { key, realm }
}
fn register<T>(state: &mut LifecycleState, anchor: u64, value: T) -> RegisteredPlugin<T> {
    state
        .register_plugin(
            None,
            &BTreeMap::new(),
            port(anchor, 0),
            PluginDefinition::new(vec![], vec![], value),
        )
        .ok()
        .unwrap()
}
fn begin<T>(
    state: &mut LifecycleState,
    plugin: &RegisteredPlugin<T>,
    domain: u64,
) -> (Work, Groups) {
    state.begin_execution(plugin.id(), domain).unwrap()
}

#[test]
fn registration_uses_real_parent_ports_and_child_realms_without_a_self_dependency() {
    let mut state = LifecycleState::new(1000);
    let parent = state
        .insert(None, vec![port(5, 7), port(6, 0), port(7, 9)], vec![])
        .unwrap();
    let realms = BTreeMap::from([(5, 11), (6, 3), (7, 9)]);
    let child = state
        .register_plugin(
            Some(parent),
            &realms,
            port(900, 0),
            PluginDefinition::new(vec![8, 5], vec![7], "actual child recipe".to_owned()),
        )
        .ok()
        .unwrap();
    assert_eq!(
        child.dependencies(),
        &[port(8, 0), port(5, 11), port(5, 7), port(6, 0), port(6, 3)]
    );
    assert_eq!(
        state.kernel().dependency_ports(child.id()),
        child.dependencies()
    );
    assert_eq!(child.provisions(), &[port(7, 9)]);
    assert!(state.kernel().provision_reserved(child.id(), port(900, 0)));
    assert!(state.kernel().provision_reserved(child.id(), port(7, 9)));
    assert_eq!(state.kernel().children(parent), vec![child.id()]);

    // Registration reads current authoritative declarations after a reconfigure.
    state
        .configure_pending_dependencies(parent, vec![port(12, 4)])
        .unwrap();
    let next = state
        .register_plugin(
            Some(parent),
            &BTreeMap::new(),
            port(901, 0),
            PluginDefinition::new(vec![], vec![], ()),
        )
        .ok()
        .unwrap();
    assert_eq!(next.dependencies(), &[port(12, 4), port(12, 0)]);
}

struct Payload {
    text: String,
    drops: Arc<AtomicUsize>,
}
impl Drop for Payload {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}
#[test]
fn rejected_registration_returns_actual_payload_and_reserves_no_node_or_anchor() {
    let mut state = LifecycleState::new(1001);
    let parent = state.insert(None, vec![], vec![port(5, 2)]).unwrap();
    let drops = Arc::new(AtomicUsize::new(0));
    let make = || Payload {
        text: "noncopy capture".into(),
        drops: drops.clone(),
    };
    let realms = BTreeMap::from([(5, 2)]);
    let (error, definition) = state
        .register_plugin(
            Some(parent),
            &realms,
            port(900, 0),
            PluginDefinition::new(vec![], vec![5], make()),
        )
        .err()
        .unwrap();
    assert_eq!(error, Error::Conflict);
    assert_eq!(state.kernel().ids(), vec![parent]);
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    let payload = definition.into_payload();
    assert_eq!(payload.text, "noncopy capture");
    drop(payload);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    // Duplicate declarations cannot be silently normalized into a different interface.
    let (error, _) = state
        .register_plugin(
            None,
            &realms,
            port(900, 0),
            PluginDefinition::new(vec![5, 5], vec![], make()),
        )
        .err()
        .unwrap();
    assert_eq!(error, Error::Conflict);
    assert_eq!(state.kernel().ids(), vec![parent]);
    state.retire(parent).unwrap();
    let (error, _) = state
        .register_plugin(
            Some(parent),
            &realms,
            port(900, 0),
            PluginDefinition::new(vec![], vec![], make()),
        )
        .err()
        .unwrap();
    assert_eq!(error, Error::Retired);
    assert_eq!(state.kernel().ids(), vec![parent]);
}

#[test]
fn registered_mutable_payload_and_real_argument_reach_root_completion() {
    let mut state = LifecycleState::new(1002);
    let observed = Arc::new(Mutex::new(String::new()));
    let capture = observed.clone();
    let mut text = Box::new(String::from("registered"));
    type Reply = RootOutput<Result<(), String>, std::future::Ready<Result<(), String>>>;
    let mut plugin = register(&mut state, 900, move |argument: String| -> Reply {
        text.push_str(&argument);
        *capture.lock().unwrap() = (*text).clone();
        RootOutput::Ready(Ok(()))
    });
    let (mut work, groups) = begin(&mut state, &plugin, 201);
    let invocation = state
        .admit_registered_root(&plugin, &mut work, String::from(" actual argument"))
        .ok()
        .unwrap();
    let reply = plugin.call(invocation).ok().unwrap();
    let RootDispatch::Ready(receipt) = reply.dispatch() else {
        panic!("actual sync output");
    };
    assert_eq!(work.complete_root(receipt).ok().unwrap(), Ok(()));
    state.finish_execution(plugin.id(), &work, &groups).unwrap();
    assert_eq!(state.kernel().phase(plugin.id()), Some(Phase::Active));
    assert_eq!(*observed.lock().unwrap(), "registered actual argument");
}

#[test]
fn root_admission_rejects_foreign_unbound_wrong_owner_and_consumed_setup() {
    let mut state = LifecycleState::new(1003);
    let mut plugin = register(&mut state, 900, |(): ()| Ok::<(), ()>(()));
    let other = register(&mut state, 901, 20);
    let (mut work, groups) = begin(&mut state, &plugin, 202);
    let (mut other_work, _) = begin(&mut state, &other, 203);
    let mut foreign = LifecycleState::new(2003);
    let foreign_plugin = register(&mut foreign, 900, 10);
    let (mut foreign_work, _) = begin(&mut foreign, &foreign_plugin, 202);
    assert!(state.admit_registered_root(&other, &mut work, ()).is_err());
    assert!(state
        .admit_registered_root(&plugin, &mut other_work, ())
        .is_err());
    assert!(state
        .admit_registered_root(&plugin, &mut foreign_work, ())
        .is_err());
    assert!(foreign
        .admit_registered_root(&plugin, &mut work, ())
        .is_err());
    let mut unbound = Work::new(202);
    assert!(state
        .admit_registered_root(&plugin, &mut unbound, ())
        .is_err());
    assert_eq!(work.root(), RootStatus::Unissued);
    let invocation = state
        .admit_registered_root(&plugin, &mut work, ())
        .ok()
        .unwrap();
    assert!(state.admit_registered_root(&plugin, &mut work, ()).is_err());
    let receipt = plugin.call(invocation).ok().unwrap();
    assert_eq!(work.complete_root(receipt).ok().unwrap(), Ok(()));
    state.finish_execution(plugin.id(), &work, &groups).unwrap();
    assert!(state.admit_registered_root(&plugin, &mut work, ()).is_err());
}

#[test]
fn hot_update_invalidates_old_admission_without_invoking_a_different_recipe() {
    type Callback = Box<dyn FnMut(()) -> Result<(), ()>>;
    let mut state = LifecycleState::new(1004);
    let calls = Arc::new(AtomicUsize::new(0));
    let old_calls = calls.clone();
    let callback: Callback = Box::new(move |()| {
        old_calls.fetch_add(1, Ordering::SeqCst);
        Ok(())
    });
    let mut plugin = register(&mut state, 900, callback);
    let (mut work, groups) = begin(&mut state, &plugin, 204);
    let invocation = state
        .admit_registered_root(&plugin, &mut work, ())
        .ok()
        .unwrap();
    let new_calls = calls.clone();
    let next: Callback = Box::new(move |()| {
        new_calls.fetch_add(100, Ordering::SeqCst);
        Ok(())
    });
    drop(plugin.replace(next).ok().unwrap());
    assert!(plugin.call(invocation).is_err());
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert_eq!(work.root(), RootStatus::Queued);
    assert_eq!(
        state.finish_execution(plugin.id(), &work, &groups),
        Err(Error::InvalidState)
    );
    assert!(plugin.can_replace_count(1));
    assert!(!plugin.can_replace_count(u64::MAX));
}

#[test]
fn rejected_invocation_returns_work_for_its_actual_registered_owner() {
    let mut state = LifecycleState::new(1005);
    let mut total = 1u64;
    let mut plugin = register(&mut state, 900, move |argument: u64| {
        total += argument;
        Err::<(), _>(total)
    });
    let mut other = register(&mut state, 901, |_: u64| -> Result<(), u64> {
        panic!("wrong recipe")
    });
    let (mut work, _) = begin(&mut state, &plugin, 205);
    let invocation = state
        .admit_registered_root(&plugin, &mut work, 37)
        .ok()
        .unwrap();
    let invocation = other.call(invocation).err().unwrap();
    let mut foreign = LifecycleState::new(2005);
    let mut same_numeric_id = register(&mut foreign, 900, |_: u64| -> Result<(), u64> {
        panic!("foreign domain")
    });
    assert_eq!(same_numeric_id.id(), plugin.id());
    let invocation = same_numeric_id.call(invocation).err().unwrap();
    let receipt = plugin.call(invocation).ok().unwrap();
    assert_eq!(work.complete_root(receipt).ok().unwrap(), Err(38));
}

#[test]
fn actual_async_output_from_registered_recipe_is_not_promoted_to_success() {
    let mut state = LifecycleState::new(1006);
    let calls = Arc::new(AtomicUsize::new(0));
    let capture = calls.clone();
    let mut total = 20u64;
    let mut plugin = register(&mut state, 900, move |argument: u64| {
        total += argument;
        capture.fetch_add(1, Ordering::SeqCst);
        let result = total;
        RootOutput::Pending(async move { Err::<(), _>(result) })
    });
    let (mut work, groups) = begin(&mut state, &plugin, 206);
    let invocation = state
        .admit_registered_root(&plugin, &mut work, 17u64)
        .ok()
        .unwrap();
    let reply = plugin.call(invocation).ok().unwrap();
    // The actual factory has run even though its Future has never been polled.
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    let RootDispatch::Pending(pending) = reply.dispatch() else {
        panic!("actual async output");
    };
    assert_eq!(work.root(), RootStatus::Queued);
    assert_eq!(
        state.finish_execution(plugin.id(), &work, &groups),
        Err(Error::InvalidState)
    );
    let mut future = pin!(pending.complete());
    let receipt = match future
        .as_mut()
        .poll(&mut Context::from_waker(Waker::noop()))
    {
        Poll::Ready(receipt) => receipt,
        Poll::Pending => panic!("ready future"),
    };
    assert_eq!(work.complete_root(receipt).ok().unwrap(), Err(37));
    assert_eq!(
        state.finish_execution(plugin.id(), &work, &groups),
        Err(Error::InvalidState)
    );
}

#[test]
fn child_inverse_rejects_another_runtime_and_does_not_retire_a_replacement() {
    let mut state = LifecycleState::new(1007);
    let parent = register(&mut state, 900, ());
    let child = state
        .register_plugin(
            Some(parent.id()),
            &BTreeMap::new(),
            port(901, 0),
            PluginDefinition::new(vec![], vec![], ()),
        )
        .ok()
        .unwrap();
    let identity = child.child_identity().unwrap();
    assert!(parent.child_identity().is_none());
    let mut foreign = LifecycleState::new(2007);
    let foreign_parent = register(&mut foreign, 900, ());
    let foreign_child = register(&mut foreign, 901, ());
    assert_eq!(child.id(), foreign_child.id());
    assert_eq!(state.retire_child(identity), Ok(()));
    assert!(!state.kernel().retired(parent.id()));
    assert_eq!(foreign.retire_child(identity), Err(Error::InvalidState));
    assert!(!foreign.kernel().retired(foreign_child.id()));
    assert!(!foreign.kernel().retired(foreign_parent.id()));
    state.remove(child.id()).unwrap();
    let replacement = register(&mut state, 901, ());
    assert_ne!(replacement.id(), child.id());
    assert_eq!(state.retire_child(identity), Ok(()));
    assert!(!state.kernel().retired(replacement.id()));
}

#[test]
fn panicking_registered_factory_cannot_manufacture_a_success_receipt() {
    let mut state = LifecycleState::new(1008);
    let mut plugin = register(&mut state, 900, |(): ()| -> Result<(), &str> {
        panic!("factory panic")
    });
    let (mut work, groups) = begin(&mut state, &plugin, 208);
    let invocation = state
        .admit_registered_root(&plugin, &mut work, ())
        .ok()
        .unwrap();
    let ticket = invocation.ticket();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| plugin.call(invocation)));
    assert!(result.is_err());
    assert_eq!(
        state.finish_execution(plugin.id(), &work, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(work.fail_root(ticket, "caught panic"), Ok("caught panic"));
    assert_eq!(work.root(), RootStatus::Settled);
    assert_eq!(
        state.finish_execution(plugin.id(), &work, &groups),
        Err(Error::InvalidState)
    );
}
