//! Deliberately colliding numeric selectors exercise the public Driver guards.
use super::test_support::Core;
use super::*;
use cordis_kernel::configuration_runtime::adoption::{Cause, Change};
use cordis_kernel::reversible_value::function::Body;
use std::sync::atomic::{AtomicUsize, Ordering};

type Recipe = Box<dyn FnMut(Arc<String>) -> Result<(), &'static str>>;
type World = NativeDriver<Recipe, String, ()>;

fn recipe(calls: &Arc<AtomicUsize>) -> Recipe {
    let calls = calls.clone();
    Box::new(move |_argument| {
        calls.fetch_add(1, Ordering::SeqCst);
        Ok(())
    })
}
fn world<R>(payload: R) -> (NativeDriver<R, String, ()>, usize) {
    let mut world = NativeDriver {
        state: NativeRuntime::new(7300),
    };
    let id = world
        .register_plugin(
            None,
            &BTreeMap::new(),
            Port { key: 1, realm: 0 },
            PluginDefinition::new(vec![], vec![], payload),
            "original".into(),
        )
        .ok()
        .unwrap();
    (world, id)
}
fn activate(world: &mut World, id: usize) -> Core<(), ()> {
    let mut run = world.begin_managed_execution(id, 7301).unwrap();
    let call = world
        .admit_managed_root(id, &mut run, Arc::new(String::new()))
        .unwrap();
    let receipt = world.call_root(id, call).ok().unwrap();
    run.complete_root(receipt).ok().unwrap().unwrap();
    world.finish_managed_execution(id, &mut run).unwrap();
    run
}
fn revisions(world: &World, ids: &[usize]) -> Vec<u64> {
    ids.iter()
        .map(|id| world.registration(*id).unwrap().revision())
        .collect()
}

#[test]
fn foreign_invocation_is_returned_before_callback_and_its_owner_can_still_use_it() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (mut a, aid) = world(recipe(&calls));
    let (mut b, bid) = world(recipe(&calls));
    let mut ar: Core<(), ()> = a.begin_managed_execution(aid, 7301).unwrap();
    let mut br: Core<(), ()> = b.begin_managed_execution(bid, 7301).unwrap();
    let argument = Arc::new("retained".to_owned());
    let call = a
        .admit_managed_root(aid, &mut ar, argument.clone())
        .unwrap();
    let other = b
        .admit_managed_root(bid, &mut br, argument.clone())
        .unwrap();
    assert_eq!(call.lifecycle_ticket(), other.lifecycle_ticket());
    assert_eq!(call.ticket(), other.ticket());
    assert!(!b.owns_invocation(&call));
    let call = b.call_root(bid, call).err().unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    // Moving the owner does not change authority; no address of the struct is used.
    let mut moved = a;
    assert!(moved.owns_invocation(&call));
    let receipt = moved.call_root(aid, call).ok().unwrap();
    ar.complete_root(receipt).ok().unwrap().unwrap();
    assert_eq!(Arc::strong_count(&argument), 2); // The other invocation still retains it.
    let receipt = b.call_root(bid, other).ok().unwrap();
    br.complete_root(receipt).ok().unwrap().unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 2);
}

#[test]
fn opaque_invocation_uses_the_same_provenance_guard() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (mut a, aid) = world(Body::<Recipe>::Callback(recipe(&calls)));
    let (mut b, bid) = world(Body::<Recipe>::Callback(recipe(&calls)));
    let mut ar: Core<(), ()> = a.begin_managed_execution(aid, 7301).unwrap();
    let _br: Core<(), ()> = b.begin_managed_execution(bid, 7301).unwrap();
    let call = a
        .admit_managed_root(aid, &mut ar, Arc::new("opaque".into()))
        .unwrap();
    let call = b.call_opaque_root(bid, call).err().unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    let receipt = a.call_opaque_root(aid, call).ok().unwrap();
    ar.complete_root(receipt).ok().unwrap().unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[test]
fn unbound_invocation_is_not_a_native_capability_even_with_matching_numbers() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (mut native, id) = world(recipe(&calls));
    let _run: Core<(), ()> = native.begin_managed_execution(id, 7301).unwrap();
    let mut raw = cordis_kernel::lifecycle_state::LifecycleState::new(7300);
    let mut plugin = raw
        .register_plugin(
            None,
            &BTreeMap::new(),
            Port { key: 1, realm: 0 },
            PluginDefinition::new(vec![], vec![], recipe(&calls)),
        )
        .ok()
        .unwrap();
    assert_eq!(plugin.id(), id);
    let (mut work, _) = raw.begin_execution::<(), (), ()>(id, 7301).unwrap();
    let call = raw
        .admit_registered_root(&plugin, &mut work, Arc::new("raw".into()))
        .unwrap();
    assert!(call.native_identity().is_none());
    let call = native.call_root(id, call).err().unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    // The standalone path keeps its original usable contract.
    assert!(plugin.call(call).is_ok());
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[test]
fn authentic_invocations_still_require_the_current_owner_recipe_and_loading_state() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (mut owner, id) = world(recipe(&calls));
    let mut run: Core<(), ()> = owner.begin_managed_execution(id, 7301).unwrap();
    let call = owner
        .admit_managed_root(id, &mut run, Arc::new("stale".into()))
        .unwrap();
    assert!(owner.owns_invocation(&call));
    let call = owner.call_root(id + 1, call).err().unwrap();
    drop(owner.replace(id, recipe(&calls)).ok().unwrap());
    let call = owner.call_root(id, call).err().unwrap();
    owner
        .withdraw_managed_execution(id, &mut run, false)
        .unwrap();
    assert!(owner.call_root(id, call).is_err());
    assert_eq!(calls.load(Ordering::SeqCst), 0);
}

#[test]
fn targets_bind_allocation_without_retaining_host_or_journal_payloads() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (mut a, aid) = world(recipe(&calls));
    let (mut b, bid) = world(recipe(&calls));
    let ar = activate(&mut a, aid);
    let _br = activate(&mut b, bid);
    let target = a.configuration_target(aid).unwrap();
    assert!(b.state.configuration_target_is_current(&target)); // Numeric collision is real.
    assert!(!b.configuration_target_is_current(&target));
    let retained = Arc::new(AtomicUsize::new(0));
    let replacement = b
        .replace_configuration(&target, recipe(&retained))
        .err()
        .unwrap()
        .1;
    assert_eq!(Arc::strong_count(&retained), 2);
    assert_eq!(b.registration(bid).unwrap().revision(), 0);
    let clone = target.clone();
    assert!(Arc::ptr_eq(
        target.native_identity(),
        clone.native_identity()
    ));
    let mut moved = a;
    assert!(moved.configuration_target_is_current(&clone));
    let old = moved
        .replace_configuration(&clone, replacement)
        .ok()
        .unwrap();
    assert!(!moved.configuration_target_is_current(&target));
    assert_eq!(moved.registration(aid).unwrap().revision(), 1);
    drop(old);
    let journal = moved.execution_journal();
    let weak = Arc::downgrade(journal.runtime_identity());
    drop(journal);
    drop(ar);
    drop(moved);
    assert!(weak.upgrade().is_none());
    assert_eq!(Arc::strong_count(&retained), 1);
    // The target is still usable for provenance inspection after the host is gone.
    assert!(Arc::ptr_eq(
        target.native_identity(),
        clone.native_identity()
    ));
}

#[test]
fn invocation_binding_does_not_retain_its_host_or_journal() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (mut owner, id) = world(recipe(&calls));
    let mut run: Core<(), ()> = owner.begin_managed_execution(id, 7301).unwrap();
    let argument = Arc::new("retained by invocation only".to_owned());
    let call = owner
        .admit_managed_root(id, &mut run, argument.clone())
        .unwrap();
    let journal = owner.execution_journal();
    let weak = Arc::downgrade(journal.runtime_identity());
    drop(journal);
    drop(run);
    drop(owner);
    assert!(weak.upgrade().is_none());
    assert_eq!(Arc::strong_count(&calls), 1);
    assert_eq!(Arc::strong_count(&argument), 2);
    assert!(call.native_identity().is_some());
    drop(call);
    assert_eq!(Arc::strong_count(&argument), 1);
}

#[test]
fn batch_preflight_merges_foreign_stale_and_duplicate_failures_before_any_swap() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (mut owner, a) = world(recipe(&calls));
    let b = owner
        .register_plugin(
            None,
            &BTreeMap::new(),
            Port { key: 2, realm: 0 },
            PluginDefinition::new(vec![], vec![], recipe(&calls)),
            "second".into(),
        )
        .ok()
        .unwrap();
    let _ar = activate(&mut owner, a);
    let _br = activate(&mut owner, b);
    let (mut foreign, fid) = world(recipe(&calls));
    let _fr = activate(&mut foreign, fid);
    let foreign_target = foreign.configuration_target(fid).unwrap();
    let stale = owner.configuration_target(b).unwrap();
    drop(
        owner
            .replace_configuration(&stale, recipe(&calls))
            .ok()
            .unwrap(),
    );
    let target = owner.configuration_target(a).unwrap();
    let other = owner.configuration_target(b).unwrap();
    let metadata_calls = AtomicUsize::new(0);
    for (targets, index, cause) in [
        (
            vec![other.clone(), foreign_target.clone()],
            1,
            Cause::Target,
        ),
        (
            vec![stale.clone(), foreign_target.clone()],
            0,
            Cause::Target,
        ),
        (vec![foreign_target.clone(), stale], 0, Cause::Target),
        (
            vec![target.clone(), target.clone(), foreign_target.clone()],
            1,
            Cause::Duplicate,
        ),
        (vec![target.clone(), foreign_target], 1, Cause::Target),
    ] {
        let rejected = owner
            .adopt_configurations(
                targets
                    .into_iter()
                    .enumerate()
                    .map(|(i, target)| Change {
                        target,
                        recipe: recipe(&calls),
                        metadata: format!("new {i}"),
                    })
                    .collect(),
                |host, value| {
                    metadata_calls.fetch_add(1, Ordering::SeqCst);
                    std::mem::replace(host, value)
                },
            )
            .err()
            .unwrap();
        assert_eq!(
            (rejected.failure.index, rejected.failure.cause),
            (index, cause)
        );
        assert_eq!(metadata_calls.load(Ordering::SeqCst), 0);
        assert_eq!(revisions(&owner, &[a, b]), [0, 1]);
        assert_eq!(owner.host(a).unwrap(), "original");
        assert_eq!(owner.host(b).unwrap(), "second");
        for (i, mut change) in rejected.changes.into_iter().enumerate() {
            assert_eq!(change.metadata, format!("new {i}"));
            let payload = Arc::new(format!("payload {i}"));
            assert_eq!((change.recipe)(payload.clone()), Ok(()));
            assert_eq!(Arc::strong_count(&payload), 1);
        }
    }
    let previous = owner
        .adopt_configurations(
            vec![
                Change {
                    target: other,
                    recipe: recipe(&calls),
                    metadata: "new second".into(),
                },
                Change {
                    target,
                    recipe: recipe(&calls),
                    metadata: "new first".into(),
                },
            ],
            |host, value| {
                metadata_calls.fetch_add(1, Ordering::SeqCst);
                std::mem::replace(host, value)
            },
        )
        .ok()
        .unwrap();
    assert_eq!(metadata_calls.load(Ordering::SeqCst), 2);
    assert_eq!(revisions(&owner, &[a, b]), [1, 2]);
    assert_eq!(
        previous.iter().map(|p| p.target.id()).collect::<Vec<_>>(),
        [b, a]
    );
    assert_eq!(
        previous
            .iter()
            .map(|p| p.metadata.as_str())
            .collect::<Vec<_>>(),
        ["second", "original"]
    );
    assert_eq!(owner.host(a).unwrap(), "new first");
    assert_eq!(owner.host(b).unwrap(), "new second");
}
