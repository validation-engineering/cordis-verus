use cordis_kernel::cleanup_groups::CleanupGroups;
use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
use cordis_kernel::lifecycle_actions::CleanupOutcome;
use cordis_kernel::lifecycle_state::native::NativeHost;
use cordis_kernel::lifecycle_state::registration::child::ChildSlot;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::lifecycle_state::services::{NativeEpisode, NativeServices};
use cordis_kernel::setup_work::SetupWork;
use cordis_kernel::{Error, Phase, Port};
use std::collections::BTreeMap;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc, Mutex,
};

type Recipe = Box<dyn FnMut(u64) -> Result<(), String>>;
type Host = NativeHost<Recipe, String>;
type Work = SetupWork<String, String>;
type Groups = CleanupGroups<String>;
type Calls = Arc<Mutex<Vec<(&'static str, u64)>>>;
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn recipe(calls: &Calls, label: &'static str) -> Recipe {
    let calls = calls.clone();
    Box::new(move |argument| {
        calls.lock().unwrap().push((label, argument));
        Ok(())
    })
}
fn register(host: &mut Host, calls: &Calls, label: &'static str) -> usize {
    let anchor = port(10_000 + host.kernel().identity_slots() as u64);
    host.register(
        None,
        &BTreeMap::new(),
        anchor,
        PluginDefinition::new(vec![], vec![], recipe(calls, label)),
        label.into(),
    )
    .ok()
    .unwrap()
}
fn begin(
    host: &mut Host,
    id: usize,
    store: &NativeServices<String>,
    domain: u64,
) -> (Work, Groups, NativeEpisode<String>) {
    host.begin_native_execution(id, store, domain).unwrap()
}
fn root(host: &mut Host, id: usize, work: &mut Work, argument: u64) {
    let invocation = host.admit_root(id, work, argument).ok().unwrap();
    let receipt = host.call(id, invocation).ok().unwrap();
    work.complete_root(receipt).ok().unwrap().unwrap();
}

struct DropCount {
    label: &'static str,
    drops: Arc<AtomicUsize>,
}
impl Drop for DropCount {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn failed_allocation_returns_both_actual_inputs_and_reserves_nothing() {
    let drops = Arc::new(AtomicUsize::new(0));
    let make = |label| DropCount {
        label,
        drops: drops.clone(),
    };
    let mut host = NativeHost::new(600);
    let parent = host
        .register(
            None,
            &BTreeMap::new(),
            port(1),
            PluginDefinition::new(vec![], vec![], make("recipe")),
            make("host"),
        )
        .ok()
        .unwrap();
    let rejected = host
        .register(
            None,
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![1], make("rejected recipe")),
            make("rejected host"),
        )
        .err()
        .unwrap();
    assert_eq!(host.ids(), vec![parent]);
    assert_eq!(host.kernel().identity_slots(), 1);
    assert!(!host.kernel().provision_reserved(parent, port(2)));
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    let (_, definition, metadata) = rejected;
    let callback = definition.into_payload();
    assert_eq!(callback.label, "rejected recipe");
    assert_eq!(metadata.label, "rejected host");
    drop((callback, metadata));
    assert_eq!(drops.load(Ordering::SeqCst), 2);
    assert!(host.remove(parent).is_err());
    assert_eq!(drops.load(Ordering::SeqCst), 2);
    host.retire(parent).unwrap();
    let removed = host.remove(parent).ok().unwrap();
    assert!(host.is_empty());
    assert_eq!(
        drops.load(Ordering::SeqCst),
        2,
        "Remove moves captures; it does not destroy them inside bookkeeping"
    );
    let (registration, metadata) = removed.into_parts();
    assert_eq!(registration.id(), parent);
    assert_eq!(metadata.label, "host");
    drop((registration, metadata));
    assert_eq!(drops.load(Ordering::SeqCst), 4);
}

#[test]
fn mutable_bookkeeping_and_recipe_update_preserve_other_plugins() {
    let calls = Calls::default();
    let mut host = Host::new(610);
    let first = register(&mut host, &calls, "first");
    let second = register(&mut host, &calls, "second");
    *host.host_mut(first).unwrap() = "edited host metadata".into();
    let previous = host.replace(first, recipe(&calls, "updated")).ok().unwrap();
    drop(previous);
    assert_eq!(host.host(second).unwrap(), "second");
    assert_eq!(host.registration(first).unwrap().id(), first);
    assert_eq!(host.registration(second).unwrap().id(), second);
    let store = NativeServices::<String>::new(610);
    let (mut fw, _, _) = begin(&mut host, first, &store, 611);
    let (mut sw, _, _) = begin(&mut host, second, &store, 612);
    root(&mut host, first, &mut fw, 31);
    root(&mut host, second, &mut sw, 47);
    assert_eq!(
        *calls.lock().unwrap(),
        vec![("updated", 31), ("second", 47)]
    );
    assert_eq!(host.ids(), vec![first, second]);
    assert!(host.host_mut(100).is_none());
    assert!(host.registration(100).is_none());
}

#[test]
fn wrong_owner_foreign_domain_and_replaced_recipe_cannot_execute_an_admitted_call() {
    let calls = Calls::default();
    let mut host = Host::new(620);
    let first = register(&mut host, &calls, "first");
    let second = register(&mut host, &calls, "second");
    let mut foreign = Host::new(621);
    let same_number = register(&mut foreign, &calls, "foreign");
    assert_eq!(first, same_number);
    let mut store = NativeServices::<String>::new(620);
    let (mut work, mut groups, mut values) = begin(&mut host, first, &store, 622);
    let invocation = host.admit_root(first, &mut work, 19).ok().unwrap();
    let invocation = host.call(second, invocation).err().unwrap();
    let invocation = foreign.call(same_number, invocation).err().unwrap();
    drop(
        host.replace(first, recipe(&calls, "new episode"))
            .ok()
            .unwrap(),
    );
    let invocation = host.call(first, invocation).err().unwrap();
    assert!(calls.lock().unwrap().is_empty());
    work.fail_root(invocation.ticket(), "obsolete recipe")
        .unwrap();
    host.leave(first).unwrap();
    work.withdraw();
    host.settle_execution(first, &work, &groups).unwrap();
    host.begin_cleanup(first).unwrap();
    host.release_native_execution(first, &mut store, &mut values, &mut work, &mut groups)
        .unwrap();
    let (mut next, _, _) = begin(&mut host, first, &store, 623);
    root(&mut host, first, &mut next, 23);
    assert_eq!(*calls.lock().unwrap(), vec![("new episode", 23)]);
}

#[test]
fn dynamic_child_slot_and_actual_entry_are_installed_and_removed_together() {
    let calls = Calls::default();
    let mut host = Host::new(630);
    let parent = register(&mut host, &calls, "parent");
    let store = NativeServices::<String>::new(630);
    let (work, _, _) = begin(&mut host, parent, &store, 631);
    let mut slot = ChildSlot::<String>::from_work(&work).unwrap();
    let child = host
        .register_child(
            &mut slot,
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![], recipe(&calls, "child")),
            "child metadata".into(),
        )
        .ok()
        .unwrap();
    assert_eq!(slot.identity().unwrap().id(), child);
    assert_eq!(host.registration(child).unwrap().parent(), Some(parent));
    assert_eq!(host.kernel().children(parent), vec![child]);
    assert_eq!(host.host(child).unwrap(), "child metadata");
    let rejected = host
        .register_child(
            &mut slot,
            &BTreeMap::new(),
            port(3),
            PluginDefinition::new(vec![], vec![], recipe(&calls, "duplicate")),
            "duplicate metadata".into(),
        )
        .err()
        .unwrap();
    assert_eq!(rejected.0, Error::InvalidState);
    assert_eq!(rejected.2, "duplicate metadata");
    assert_eq!(host.ids(), vec![parent, child]);
    host.retire_child_slot(&mut slot).unwrap();
    let removed = host.remove(child).ok().unwrap();
    assert_eq!(removed.into_parts().1, "child metadata");
    host.retire_child_slot(&mut slot).unwrap();
    assert_eq!(host.ids(), vec![parent]);
    assert!(!host.kernel().retired(parent));
    let mut cancelled = ChildSlot::<String>::from_work(&work).unwrap();
    host.retire_child_slot(&mut cancelled).unwrap();
    assert!(host
        .register_child(
            &mut cancelled,
            &BTreeMap::new(),
            port(4),
            PluginDefinition::new(vec![], vec![], recipe(&calls, "late")),
            "late metadata".into()
        )
        .is_err());
    assert_eq!(host.ids(), vec![parent]);
}

#[test]
fn failed_cleanup_retains_actual_host_and_services_until_retry_and_unload() {
    let calls = Calls::default();
    let mut host = Host::new(640);
    let id = host
        .register(
            None,
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![1], recipe(&calls, "provider")),
            "actual host".into(),
        )
        .ok()
        .unwrap();
    let mut store = NativeServices::new(640);
    let (mut work, mut groups, mut values) = begin(&mut host, id, &store, 641);
    root(&mut host, id, &mut work, 7);
    let actual = Arc::new("actual service".to_owned());
    values.provide(port(1), actual.clone()).unwrap();
    groups.register(0, "retryable inverse".into()).unwrap();
    host.finish_native_execution(id, &mut store, &values, &work, &groups)
        .unwrap();
    assert!(Arc::ptr_eq(
        host.native_value(&store, port(1)).unwrap(),
        &actual
    ));
    host.retire(id).unwrap();
    assert!(host.remove(id).is_err());
    host.leave(id).unwrap();
    work.withdraw();
    host.settle_execution(id, &work, &groups).unwrap();
    host.begin_cleanup(id).unwrap();
    let (old, inverse) = groups.pop(0).unwrap().unwrap();
    groups
        .complete_result(
            0,
            old,
            Err::<(), _>("busy"),
            Some(inverse),
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    host.fail_execution(id, &work, &groups).unwrap();
    assert!(host
        .release_native_execution(id, &mut store, &mut values, &mut work, &mut groups)
        .is_err());
    assert!(host.remove(id).is_err());
    assert_eq!(host.host(id).unwrap(), "actual host");
    assert!(Arc::ptr_eq(values.read(port(1)).unwrap().1, &actual));
    host.retry_execution(id, &work, &mut groups).unwrap();
    let (fresh, _) = groups.pop(0).unwrap().unwrap();
    assert_ne!(fresh, old);
    assert!(groups
        .complete_result(
            0,
            old,
            Ok::<(), &str>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
    groups
        .complete_result(
            0,
            fresh,
            Ok::<(), &str>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    let (outcome, released) = host
        .release_native_execution(id, &mut store, &mut values, &mut work, &mut groups)
        .unwrap();
    assert_eq!(outcome, CleanupOutcome::Succeeded);
    assert_eq!(host.kernel().phase(id), Some(Phase::Inactive));
    assert_eq!(
        host.host(id).unwrap(),
        "actual host",
        "Unload is not Remove"
    );
    assert_eq!(host.remove(id).ok().unwrap().into_parts().1, "actual host");
    assert!(!store.has_publications());
    drop(released);
    assert_eq!(Arc::strong_count(&actual), 1);
}

#[test]
fn compaction_and_churn_keep_live_entries_sorted_without_reusing_identity() {
    let calls = Calls::default();
    let mut host = Host::new(650);
    let survivor = register(&mut host, &calls, "survivor");
    let mut last = survivor;
    for _ in 0..40 {
        let id = register(&mut host, &calls, "temporary");
        assert!(id > last);
        host.retire(id).unwrap();
        drop(host.remove(id).ok().unwrap());
        last = id;
    }
    host.compact_bindings();
    host.compact_declarations();
    let final_id = register(&mut host, &calls, "final");
    assert!(final_id > last);
    assert_eq!(host.ids(), vec![survivor, final_id]);
    assert_eq!(host.kernel().ids(), host.ids());
    assert_eq!(host.len(), 2);
    assert_eq!(host.host(survivor).unwrap(), "survivor");
}

#[test]
fn admitted_root_is_revoked_before_invocation_and_stays_stale_after_restart() {
    let calls = Calls::default();
    let mut host = Host::new(680);
    let id = register(&mut host, &calls, "actual");
    let mut store = NativeServices::<String>::new(680);
    let (mut work, mut groups, mut values) = begin(&mut host, id, &store, 681);
    let invocation = host.admit_root(id, &mut work, 51).ok().unwrap();
    let origin = invocation.lifecycle_ticket();
    host.leave(id).unwrap();
    work.withdraw();
    let invocation = host.call(id, invocation).err().unwrap();
    assert!(calls.lock().unwrap().is_empty());
    assert!(work.cancel_queued_root(invocation.ticket()));
    host.settle_execution(id, &work, &groups).unwrap();
    host.begin_cleanup(id).unwrap();
    host.release_native_execution(id, &mut store, &mut values, &mut work, &mut groups)
        .unwrap();
    // Reuse the work domain deliberately: lifecycle generation/action still
    // rejects the old invocation even though the recipe revision is unchanged.
    let (mut next, _, _) = begin(&mut host, id, &store, 681);
    assert_ne!(next.lifecycle_ticket(), Some(origin));
    let invocation = host.call(id, invocation).err().unwrap();
    assert_eq!(invocation.lifecycle_ticket(), origin);
    assert!(calls.lock().unwrap().is_empty());
    root(&mut host, id, &mut next, 53);
    assert_eq!(*calls.lock().unwrap(), vec![("actual", 53)]);
}

#[test]
fn retirement_and_local_withdrawal_close_root_admission() {
    let calls = Calls::default();
    let mut host = Host::new(690);
    let id = register(&mut host, &calls, "retired");
    let other = register(&mut host, &calls, "withdrawn");
    let store = NativeServices::<String>::new(690);
    let (mut work, _, _) = begin(&mut host, id, &store, 691);
    let (mut withdrawn, _, _) = begin(&mut host, other, &store, 692);
    withdrawn.withdraw();
    assert_eq!(host.admit_root(other, &mut withdrawn, 60).err(), Some(60));
    let invocation = host.admit_root(id, &mut work, 61).ok().unwrap();
    host.retire(id).unwrap();
    assert_eq!(host.kernel().phase(id), Some(Phase::Loading));
    assert!(host.call(id, invocation).is_err());
    assert!(calls.lock().unwrap().is_empty());
}
