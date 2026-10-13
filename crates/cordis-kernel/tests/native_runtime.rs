use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
use cordis_kernel::execution::{Execution, ExecutionPhase};
use cordis_kernel::lifecycle_state::native::runtime::NativeRuntime;
use cordis_kernel::lifecycle_state::native::NativeHost;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::lifecycle_state::services::NativeServices;
use cordis_kernel::{Error, Phase, Port};
use std::collections::BTreeMap;
use std::sync::Arc;

type Callback = fn(usize) -> Result<(), String>;
type World = NativeRuntime<Callback, String, String>;
type Episode = Execution<String, String, String, String>;
fn setup(_: usize) -> Result<(), String> {
    Ok(())
}
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn register(world: &mut World, key: u64, dependencies: Vec<u64>) -> usize {
    world
        .register(
            None,
            &BTreeMap::new(),
            port(100 + key),
            PluginDefinition::new(dependencies, vec![key], setup as Callback),
            format!("host {key}"),
        )
        .ok()
        .unwrap()
}
fn complete(world: &mut World, id: usize, episode: &mut Episode) {
    let call = world.admit_managed_root(id, episode, id).unwrap();
    let reply = world.call(id, call).ok().unwrap();
    episode.complete_root(reply).ok().unwrap().unwrap();
}
fn activate(world: &mut World, id: usize, key: u64, domain: u64) -> (Episode, Arc<String>) {
    let mut episode = world.begin_managed_execution(id, domain).unwrap();
    complete(world, id, &mut episode);
    let value = Arc::new(format!("value {key}"));
    episode.provide(port(key), value.clone()).unwrap();
    world.finish_managed_execution(id, &mut episode).unwrap();
    (episode, value)
}
fn withdraw(world: &mut World, id: usize, episode: &mut Episode) {
    world
        .withdraw_managed_execution(id, episode, false)
        .unwrap();
    world.settle_managed_execution(id, episode).unwrap();
}

#[test]
fn complete_publication_uses_the_registered_interface_and_actual_slots() {
    let mut world = World::new(1700);
    let id = register(&mut world, 1, vec![]);
    let mut episode: Episode = world.begin_managed_execution(id, 1701).unwrap();
    complete(&mut world, id, &mut episode);
    assert_eq!(
        world.finish_managed_execution(id, &mut episode),
        Err(Error::InvalidState)
    );
    assert_eq!(world.kernel().phase(id), Some(Phase::Loading));
    assert_eq!(world.value_count(), 0);
    let value = Arc::new("actual shared slot".to_owned());
    episode.provide(port(1), value.clone()).unwrap();
    world.finish_managed_execution(id, &mut episode).unwrap();
    assert_eq!(world.kernel().phase(id), Some(Phase::Active));
    assert_eq!(episode.phase(), ExecutionPhase::Active);
    assert!(Arc::ptr_eq(world.native_value(port(1)).unwrap(), &value));
    assert!(world.native_value(port(101)).is_none()); // lifecycle anchor
    assert!(world.native_value(Port { key: 1, realm: 9 }).is_none());
}

#[test]
fn colliding_numeric_origin_cannot_publish_a_different_interface() {
    let mut world = World::new(1710);
    let id = register(&mut world, 1, vec![]);
    let mut actual: Episode = world.begin_managed_execution(id, 1711).unwrap();
    // Deliberately bypass the ordinary host's unique domain allocator. The
    // aggregate still checks the declarations of the supplied value owner.
    let mut other: NativeHost<Callback, String> = NativeHost::new(1710);
    let other_id = other
        .register(
            None,
            &BTreeMap::new(),
            port(101),
            PluginDefinition::new(vec![], vec![99], setup as Callback),
            "other".into(),
        )
        .ok()
        .unwrap();
    assert_eq!(id, other_id);
    let store = NativeServices::new(1710);
    let mut mismatched: Episode = other.begin_managed_execution(id, &store, 1711).unwrap();
    let call = other.admit_managed_root(id, &mut mismatched, id).unwrap();
    mismatched
        .complete_root(other.call(id, call).ok().unwrap())
        .ok()
        .unwrap()
        .unwrap();
    mismatched
        .provide(port(99), Arc::new("wrong declaration".into()))
        .unwrap();
    assert_eq!(
        world.finish_managed_execution(id, &mut mismatched),
        Err(Error::InvalidState)
    );
    assert_eq!(world.kernel().phase(id), Some(Phase::Loading));
    assert_eq!(world.value_count(), 0);
    complete(&mut world, id, &mut actual);
    actual.provide(port(1), Arc::new("correct".into())).unwrap();
    world.finish_managed_execution(id, &mut actual).unwrap();
    assert_eq!(world.native_value(port(1)).unwrap().as_str(), "correct");
}

#[test]
fn failure_retry_and_unload_preserve_other_publications_and_committed_aliases() {
    let mut world = World::new(1720);
    let provider = register(&mut world, 1, vec![]);
    let (mut upstream, value) = activate(&mut world, provider, 1, 1721);
    let consumer = register(&mut world, 2, vec![1]);
    let (mut downstream, _) = activate(&mut world, consumer, 2, 1722);
    let unrelated = register(&mut world, 3, vec![]);
    let (_unrelated, independent) = activate(&mut world, unrelated, 3, 1723);
    assert!(Arc::ptr_eq(downstream.read(port(1)).unwrap().1, &value));
    downstream.register(0, "retry this inverse".into()).unwrap();
    withdraw(&mut world, provider, &mut upstream);
    assert!(world.native_value(port(1)).is_none());
    assert_eq!(world.value_count(), 3); // hidden is not released
    assert!(world.begin_cleanup(provider).is_err());
    assert!(world
        .release_managed_execution(provider, &mut upstream)
        .is_err());
    withdraw(&mut world, consumer, &mut downstream);
    world.begin_cleanup(consumer).unwrap();
    let (obsolete, action) = downstream.pop(0).unwrap().unwrap();
    downstream
        .complete_result(
            0,
            obsolete,
            Err("transient"),
            Some(action),
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    world.fail_managed_execution(consumer, &downstream).unwrap();
    assert!(world
        .release_managed_execution(consumer, &mut downstream)
        .is_err());
    assert_eq!(world.value_count(), 3);
    assert!(Arc::ptr_eq(downstream.read(port(1)).unwrap().1, &value));
    world
        .retry_managed_execution(consumer, &mut downstream)
        .unwrap();
    let (current, _) = downstream.pop(0).unwrap().unwrap();
    assert_ne!(current, obsolete);
    assert!(downstream
        .complete_result(
            0,
            obsolete,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
    downstream
        .complete_result(
            0,
            current,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    let (_, released) = world
        .release_managed_execution(consumer, &mut downstream)
        .unwrap();
    assert!(Arc::ptr_eq(
        released.imports.get(&(provider, 1, 0)).unwrap(),
        &value
    ));
    assert_eq!(world.value_count(), 2);
    world.begin_cleanup(provider).unwrap();
    world
        .release_managed_execution(provider, &mut upstream)
        .unwrap();
    assert_eq!(world.value_count(), 1);
    assert!(Arc::ptr_eq(
        world.native_value(port(3)).unwrap(),
        &independent
    ));
}

#[test]
fn old_episode_cannot_release_or_replace_new_generation() {
    let mut world = World::new(1730);
    let id = register(&mut world, 1, vec![]);
    let (mut old, _) = activate(&mut world, id, 1, 1731);
    withdraw(&mut world, id, &mut old);
    world.begin_cleanup(id).unwrap();
    world.release_managed_execution(id, &mut old).unwrap();
    let (current, value) = activate(&mut world, id, 1, 1732);
    assert!(world.finish_managed_execution(id, &mut old).is_err());
    assert!(world.release_managed_execution(id, &mut old).is_err());
    assert!(world
        .withdraw_managed_execution(id, &mut old, true)
        .is_err());
    assert_eq!(current.phase(), ExecutionPhase::Active);
    assert!(!world.kernel().retired(id));
    assert!(Arc::ptr_eq(world.native_value(port(1)).unwrap(), &value));
}

#[test]
fn recipe_host_updates_and_compaction_preserve_published_values() {
    let mut world = World::new(1740);
    let id = register(&mut world, 1, vec![]);
    let (mut episode, value) = activate(&mut world, id, 1, 1741);
    *world.host_mut(id).unwrap() = "replaced host bookkeeping".into();
    world.replace(id, setup as Callback).unwrap();
    world.compact_bindings();
    world.compact_declarations();
    assert!(Arc::ptr_eq(world.native_value(port(1)).unwrap(), &value));
    world.retire(id).unwrap();
    assert!(world.remove(id).is_err());
    assert!(Arc::ptr_eq(world.native_value(port(1)).unwrap(), &value));
    withdraw(&mut world, id, &mut episode);
    world.begin_cleanup(id).unwrap();
    world.release_managed_execution(id, &mut episode).unwrap();
    let (_, host) = world.remove(id).unwrap().into_parts();
    assert_eq!(host, "replaced host bookkeeping");
    assert!(world.is_empty());
    assert_eq!(world.value_count(), 0);
}

#[test]
fn foreign_episode_rejection_is_atomic_for_both_owners() {
    let mut world = World::new(1750);
    let mut foreign = World::new(1760);
    let id = register(&mut world, 1, vec![]);
    let foreign_id = register(&mut foreign, 1, vec![]);
    let (_actual, value) = activate(&mut world, id, 1, 1751);
    let (mut other, other_value) = activate(&mut foreign, foreign_id, 1, 1761);
    assert!(world
        .withdraw_managed_execution(id, &mut other, true)
        .is_err());
    assert!(world.release_managed_execution(id, &mut other).is_err());
    assert_eq!(other.phase(), ExecutionPhase::Active);
    assert!(Arc::ptr_eq(world.native_value(port(1)).unwrap(), &value));
    assert!(Arc::ptr_eq(
        foreign.native_value(port(1)).unwrap(),
        &other_value
    ));
}

#[test]
fn shared_child_with_empty_publication_keeps_parent_values_until_its_inverse_drains() {
    use cordis_kernel::lifecycle_state::registration::shared_child::{ChildCleanup, ChildDispatch};
    type Parent = Execution<String, ChildDispatch<String, ()>, (), ChildCleanup<(), ()>>;
    let mut world = World::new(1770);
    let parent = register(&mut world, 1, vec![]);
    let mut episode: Parent = world.begin_managed_execution(parent, 1771).unwrap();
    let call = world
        .admit_managed_root(parent, &mut episode, parent)
        .unwrap();
    episode
        .complete_root(world.call(parent, call).ok().unwrap())
        .ok()
        .unwrap()
        .unwrap();
    let value = Arc::new("parent slot".to_owned());
    episode.provide(port(1), value.clone()).unwrap();
    world
        .finish_managed_execution(parent, &mut episode)
        .unwrap();
    let (handle, _) = episode
        .enqueue_native_child(0, "child recipe".into())
        .ok()
        .unwrap();
    let mut allocated = None;
    let reply = episode.take_child().unwrap().run(|request| {
        let ChildDispatch::Native(request) = request else {
            panic!("native child")
        };
        let (payload, child) = request.into_parts();
        assert_eq!(payload, "child recipe");
        allocated = Some(
            world
                .register_shared_child(
                    &child,
                    &BTreeMap::new(),
                    port(202),
                    PluginDefinition::new(vec![], vec![], setup as Callback),
                    "child host".into(),
                )
                .result
                .ok()
                .unwrap(),
        );
    });
    episode.complete_request(reply).ok().unwrap();
    let child = allocated.unwrap();
    assert_eq!(handle.snapshot().identity().unwrap().id(), child);
    let mut child_episode: Episode = world.begin_managed_execution(child, 1772).unwrap();
    complete(&mut world, child, &mut child_episode);
    world
        .finish_managed_execution(child, &mut child_episode)
        .unwrap();
    assert_eq!(world.kernel().phase(child), Some(Phase::Active));
    assert_eq!(world.value_count(), 1);
    world.retire_shared_child(&handle).result.unwrap();
    withdraw(&mut world, child, &mut child_episode);
    world.begin_cleanup(child).unwrap();
    world
        .release_managed_execution(child, &mut child_episode)
        .unwrap();
    world.remove(child).unwrap();
    assert!(Arc::ptr_eq(world.native_value(port(1)).unwrap(), &value));
    world
        .withdraw_managed_execution(parent, &mut episode, false)
        .unwrap();
    world.settle_managed_execution(parent, &episode).unwrap();
    world.begin_cleanup(parent).unwrap();
    let (ticket, action) = episode.pop(0).unwrap().unwrap();
    let ChildCleanup::Native(child) = action else {
        panic!("paired inverse")
    };
    world.retire_shared_child(&child).result.unwrap();
    episode
        .complete_result(
            0,
            ticket,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    world
        .release_managed_execution(parent, &mut episode)
        .unwrap();
    assert_eq!(world.value_count(), 0);
}

#[test]
fn escaped_episode_keeps_begin_slots_across_withdrawal_failure_retry_and_replacement() {
    use std::sync::Mutex;
    let mut world = World::new(1780);
    let original = register(&mut world, 1, vec![]);
    let (mut upstream, old_value) = activate(&mut world, original, 1, 1781);
    let unrelated = register(&mut world, 3, vec![]);
    let (_unrelated_episode, unrelated_value) = activate(&mut world, unrelated, 3, 1782);
    let consumer = register(&mut world, 2, vec![1]);
    let (downstream, _) = activate(&mut world, consumer, 2, 1783);
    let shared = Arc::new(Mutex::new(downstream));
    let escaped = shared.clone();
    world
        .withdraw_managed_execution(original, &mut upstream, true)
        .unwrap();
    world.leave(original).unwrap();
    world.settle_managed_execution(original, &upstream).unwrap();
    assert!(world.native_value(port(1)).is_none());
    assert_eq!(world.kernel().committed(consumer)[0].provider, original);
    assert!(world.kernel().target(consumer).is_none());
    // The ghost capture includes the whole source table, but contributes no
    // executable Arc owners. Only caller, owner, publication and import retain it.
    assert_eq!(Arc::strong_count(&old_value), 4);
    assert_eq!(Arc::strong_count(&unrelated_value), 3);
    let mut episode = shared.lock().unwrap();
    episode
        .register(0, "retained retryable inverse".into())
        .unwrap();
    withdraw(&mut world, consumer, &mut episode);
    world.begin_cleanup(consumer).unwrap();
    let (stale, inverse) = episode.pop(0).unwrap().unwrap();
    episode
        .complete_result(
            0,
            stale,
            Err("retry"),
            Some(inverse),
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    world.fail_managed_execution(consumer, &episode).unwrap();
    drop(episode);
    std::thread::scope(|scope| {
        let expected = &old_value;
        scope
            .spawn(move || {
                let episode = escaped.lock().unwrap();
                let (provider, value) = episode.read(port(1)).unwrap();
                assert_eq!(provider, original);
                assert!(Arc::ptr_eq(value, expected));
            })
            .join()
            .unwrap();
    });
    let mut episode = shared.lock().unwrap();
    assert!(world
        .release_managed_execution(consumer, &mut episode)
        .is_err());
    assert_eq!(Arc::strong_count(&old_value), 4);
    world
        .retry_managed_execution(consumer, &mut episode)
        .unwrap();
    let (current, _) = episode.pop(0).unwrap().unwrap();
    assert!(episode
        .complete_result(
            0,
            stale,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
    episode
        .complete_result(
            0,
            current,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    let (_, released) = world
        .release_managed_execution(consumer, &mut episode)
        .unwrap();
    assert!(Arc::ptr_eq(
        released.imports.get(&(original, 1, 0)).unwrap(),
        &old_value
    ));
    assert!(episode.read(port(1)).is_err());
    assert_eq!(Arc::strong_count(&old_value), 4);
    drop(released);
    assert_eq!(Arc::strong_count(&old_value), 3);
    assert_eq!(Arc::strong_count(&unrelated_value), 3);
    world.begin_cleanup(original).unwrap();
    drop(
        world
            .release_managed_execution(original, &mut upstream)
            .unwrap(),
    );
    assert_eq!(Arc::strong_count(&old_value), 1);
    world.remove(original).ok().unwrap();
    let replacement = register(&mut world, 1, vec![]);
    let (_new_upstream, new_value) = activate(&mut world, replacement, 1, 1784);
    let mut next: Episode = world.begin_managed_execution(consumer, 1785).unwrap();
    complete(&mut world, consumer, &mut next);
    next.provide(port(2), Arc::new("next generation".into()))
        .unwrap();
    world.finish_managed_execution(consumer, &mut next).unwrap();
    assert!(Arc::ptr_eq(next.read(port(1)).unwrap().1, &new_value));
    assert!(episode.read(port(1)).is_err());
    assert!(world
        .release_managed_execution(consumer, &mut episode)
        .is_err());
    assert!(Arc::ptr_eq(
        world.native_value(port(1)).unwrap(),
        &new_value
    ));
    assert_eq!(Arc::strong_count(&old_value), 1);
    assert_eq!(Arc::strong_count(&unrelated_value), 3);
}

#[test]
fn issued_work_domain_blocks_foreign_context_at_every_managed_boundary() {
    let mut world = World::new(1810);
    let mut foreign = World::new(1810);
    let id = register(&mut world, 1, vec![]);
    let other = register(&mut foreign, 1, vec![]);
    assert_eq!(id, other);
    let mut actual: Episode = world.begin_managed_execution(id, 1811).unwrap();
    let mut fake: Episode = foreign.begin_managed_execution(other, 1812).unwrap();
    assert_eq!(actual.lifecycle_ticket(), fake.lifecycle_ticket());
    assert!(world.matches_execution(id, &actual));
    assert!(!world.matches_execution(id, &fake));
    assert_eq!(
        world.admit_managed_root(id, &mut fake, 777).err(),
        Some(777)
    );
    let call = foreign.admit_managed_root(id, &mut fake, other).unwrap();
    let call = world.call(id, call).err().unwrap();
    let reply = foreign.call(other, call).ok().unwrap();
    fake.complete_root(reply).ok().unwrap().unwrap();
    fake.provide(port(1), Arc::new("foreign".into())).unwrap();
    assert_eq!(
        world.finish_managed_execution(id, &mut fake),
        Err(Error::InvalidState)
    );
    assert_eq!(
        world.withdraw_managed_execution(id, &mut fake, true),
        Err(Error::InvalidState)
    );
    assert_eq!(
        world.settle_managed_execution(id, &fake),
        Err(Error::InvalidState)
    );
    assert_eq!(
        world.fail_managed_execution(id, &fake),
        Err(Error::InvalidState)
    );
    assert_eq!(
        world.retry_managed_execution(id, &mut fake),
        Err(Error::InvalidState)
    );
    assert!(world.release_managed_execution(id, &mut fake).is_err());
    assert!(!world.kernel().retired(id));
    assert_eq!(world.kernel().phase(id), Some(Phase::Loading));
    assert_eq!(fake.phase(), ExecutionPhase::Loading);
    assert!(foreign.matches_execution(other, &fake));
    foreign.finish_managed_execution(other, &mut fake).unwrap();
    complete(&mut world, id, &mut actual);
    actual.provide(port(1), Arc::new("actual".into())).unwrap();
    world.finish_managed_execution(id, &mut actual).unwrap();
    assert_eq!(world.native_value(port(1)).unwrap().as_str(), "actual");
    assert_eq!(foreign.native_value(port(1)).unwrap().as_str(), "foreign");
    withdraw(&mut world, id, &mut actual);
    assert!(world.matches_execution(id, &actual));
    world.begin_cleanup(id).unwrap();
    world.release_managed_execution(id, &mut actual).unwrap();
    assert!(!world.matches_execution(id, &actual));
    let next: Episode = world.begin_managed_execution(id, 1811).unwrap();
    assert!(world.matches_execution(id, &next));
    assert!(!world.matches_execution(id, &actual));
}
