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
    let context = downstream.native_context().unwrap();
    assert!(Arc::ptr_eq(&context, &downstream.native_context().unwrap()));
    assert_eq!(context.owner(), consumer);
    assert_eq!(context.committed()[0].provider, original);
    let captured_ticket = context.ticket();
    let captured_provisions = context.provision_ports().to_vec();
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
    assert_eq!(context.ticket(), captured_ticket);
    assert_eq!(context.committed()[0].provider, original);
    assert_eq!(context.provision_ports(), captured_provisions);
    assert!(Arc::ptr_eq(&context, &episode.native_context().unwrap()));
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
    let next_context = next.native_context().unwrap();
    assert!(!Arc::ptr_eq(&context, &next_context));
    assert_ne!(next_context.ticket(), captured_ticket);
    assert_eq!(next_context.committed()[0].provider, replacement);
    assert_eq!(context.ticket(), captured_ticket);
    assert_eq!(context.committed()[0].provider, original);
    assert_eq!(context.provision_ports(), captured_provisions);
    assert!(Arc::ptr_eq(&context, &episode.native_context().unwrap()));
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

#[test]
fn joint_group_retirement_retains_failure_and_seals_after_retry() {
    use cordis_kernel::effect_work::EffectOutput;
    use cordis_kernel::lifecycle_actions::CleanupOutcome;

    for consumed in [false, true] {
        let mut world = World::new(1900);
        let id = register(&mut world, 1, vec![]);
        let (mut episode, value) = activate(&mut world, id, 1, 1901);
        let initial = episode.observe_execution().unwrap();
        let group = episode
            .enqueue_effect(0, 1902, vec![], "iterator".into())
            .unwrap();
        let item = episode.take_group().unwrap();
        let reply = item.run(|request| episode.activate_effect(request));
        assert!(episode.complete_request(reply).ok().unwrap().is_ok());
        let mut run = episode.take_effect(group).unwrap();
        assert!(episode.admit_effect(&mut run, Some(&[])));
        episode.cancel(group);
        let run = episode.retire_effect(run).err().unwrap();
        assert!(episode.contains(group)); // An admitted stage still owns its eventual inverse.
        let (mut run, reply) = run
            .call((), |payload, ()| {
                (
                    payload,
                    EffectOutput::<String, String>::Ready(Ok(Some("actual inverse".into()))),
                )
            })
            .ok()
            .unwrap();
        episode.land_effect(&mut run, reply).ok().unwrap();
        let admitted = episode.observe_execution_after(&initial);
        withdraw(&mut world, id, &mut episode);
        world.begin_cleanup(id).unwrap();
        let (old, inverse) = episode.pop(group).unwrap().unwrap();
        let run = episode.retire_effect(run).err().unwrap();
        episode
            .complete_result(
                group,
                old,
                Err("retry me"),
                Some(inverse),
                CleanupPolicy::RetainFailure,
            )
            .unwrap();
        let run = episode.retire_effect(run).err().unwrap();
        world.fail_managed_execution(id, &episode).unwrap();
        assert!(world.release_managed_execution(id, &mut episode).is_err());
        assert_eq!(world.value_count(), 1);
        assert!(Arc::ptr_eq(episode.read(port(1)).unwrap().1, &value));
        let failed = episode.observe_execution_after(&admitted);
        world.retry_managed_execution(id, &mut episode).unwrap();
        let (current, inverse) = episode.pop(group).unwrap().unwrap();
        assert_ne!(current, old);
        assert_eq!(inverse, "actual inverse");
        assert!(episode
            .complete_result(
                group,
                old,
                Ok::<_, &str>(()),
                None,
                CleanupPolicy::RetainFailure
            )
            .is_err());
        let result = if consumed {
            Err("consumed failure")
        } else {
            Ok(())
        };
        episode
            .complete_result(group, current, result, None, CleanupPolicy::DrainConsumed)
            .unwrap();
        assert_eq!(episode.retire_effect(run).ok().unwrap(), "iterator");
        assert!(!episode.contains(group));
        assert_eq!(episode.groups().has_consumed_failure(), consumed);
        let retired = episode.observe_execution_after(&failed);
        assert!(episode
            .complete_result(
                group,
                current,
                Ok::<_, &str>(()),
                None,
                CleanupPolicy::RetainFailure
            )
            .is_err());
        let (outcome, _) = world.release_managed_execution(id, &mut episode).unwrap();
        assert_eq!(
            outcome,
            if consumed {
                CleanupOutcome::Drained
            } else {
                CleanupOutcome::Succeeded
            }
        );
        assert_eq!(episode.phase(), ExecutionPhase::Closed);
        assert!(episode.groups().is_empty());
        assert_eq!(episode.groups().has_consumed_failure(), consumed);
        assert_eq!(world.value_count(), 0);
        let _closed = episode.observe_execution_after(&retired);
    }
}

#[test]
fn native_checkpoint_joins_actual_episode_without_retaining_values() {
    let mut world = World::new(1810);
    let id = register(&mut world, 1, vec![]);
    let before_begin = world.publication_snapshot();
    let mut episode: Episode = world.begin_managed_execution(id, 1811).unwrap();
    let loading = world.episode_snapshot(id, &episode).unwrap();
    assert!(world.episode_snapshot(id + 1, &episode).is_none());
    complete(&mut world, id, &mut episode);
    let value = Arc::new("actual publication".to_owned());
    let weak = Arc::downgrade(&value);
    episode.provide(port(1), value.clone()).unwrap();
    world.finish_managed_execution(id, &mut episode).unwrap();
    let references = Arc::strong_count(&value);
    let published = world.publication_snapshot();
    let joined = world.episode_snapshot(id, &episode).unwrap();
    assert_eq!(Arc::strong_count(&value), references);
    withdraw(&mut world, id, &mut episode);
    world.begin_cleanup(id).unwrap();
    let restoring = world.episode_snapshot(id, &episode).unwrap();
    let (_, released) = world.release_managed_execution(id, &mut episode).unwrap();
    assert!(world.episode_snapshot(id, &episode).is_none());
    assert_eq!(world.value_count(), 0);
    drop(released);
    drop(episode);
    drop(value);
    assert!(weak.upgrade().is_none());
    // All checkpoints are still alive. Their historical typed Arc references
    // are erased; keeping evidence cannot extend a service payload's lifetime.
    for snapshot in [before_begin, loading, published, joined, restoring] {
        let _ = snapshot.joint().refresh();
    }
}

#[test]
fn managed_slot_checkpoints_cover_aliases_foreign_values_and_failed_cleanup() {
    use cordis_kernel::reversible_value::{slot::ServiceSlot, ReversibleValue};
    type Slot = ServiceSlot<String, ()>;
    type SlotWorld = NativeRuntime<Callback, (), Slot>;
    type SlotEpisode = Execution<Slot, String, String, String>;
    fn finish_root(world: &mut SlotWorld, id: usize, episode: &mut SlotEpisode) {
        let invocation = world.admit_managed_root(id, episode, id).unwrap();
        let receipt = world.call(id, invocation).ok().unwrap();
        episode.complete_root(receipt).ok().unwrap().unwrap();
    }
    let mut world = SlotWorld::new(1820);
    let provider = world
        .register(
            None,
            &BTreeMap::new(),
            port(100),
            PluginDefinition::new(vec![], vec![1, 2, 3, 4], setup as Callback),
            (),
        )
        .ok()
        .unwrap();
    let mut upstream: SlotEpisode = world.begin_managed_execution(provider, 1821).unwrap();
    finish_root(&mut world, provider, &mut upstream);
    let original = Arc::new(ReversibleValue::new_in(&world.execution_journal(), 10));
    let local = Arc::new(Slot::new_reversible(original.clone(), ()));
    let foreign = Arc::new(Slot::new_reversible(
        Arc::new(ReversibleValue::new(100)),
        (),
    ));
    let opaque = Arc::new(Slot::new_opaque("opaque payload".into(), ()));
    let weak_opaque = Arc::downgrade(&opaque);
    for (key, value) in [
        (1, local.clone()),
        (2, local.clone()),
        (3, foreign.clone()),
        (4, opaque.clone()),
    ] {
        upstream.provide(port(key), value).ok().unwrap();
    }
    let mut checkpoints = vec![world.service_episode_snapshot(provider, &upstream).unwrap()];
    world
        .finish_managed_execution(provider, &mut upstream)
        .unwrap();
    let consumer = world
        .register(
            None,
            &BTreeMap::new(),
            port(101),
            PluginDefinition::new(vec![1, 2, 3, 4], vec![], setup as Callback),
            (),
        )
        .ok()
        .unwrap();
    let mut downstream: SlotEpisode = world.begin_managed_execution(consumer, 1822).unwrap();
    finish_root(&mut world, consumer, &mut downstream);
    world
        .finish_managed_execution(consumer, &mut downstream)
        .unwrap();
    let old = downstream
        .native()
        .unwrap()
        .read_reversible(port(1))
        .unwrap();
    assert_eq!(old.provider(), provider);
    assert!(Arc::ptr_eq(
        downstream.read(port(1)).unwrap().1,
        downstream.read(port(2)).unwrap().1
    ));
    // The shared slot stays in its original Journal even after selecting a
    // foreign object. A Begin import observes swaps through the actual alias.
    let replacement = Arc::new(ReversibleValue::new(300));
    local
        .reversible()
        .unwrap()
        .replace(replacement.clone())
        .ok()
        .unwrap();
    let current = downstream
        .native()
        .unwrap()
        .read_reversible(port(2))
        .unwrap();
    assert_eq!(current.capture().revision(), 1);
    assert!(Arc::ptr_eq(current.value(), &replacement));
    assert!(Arc::ptr_eq(old.value(), &original));
    let old_selection = old.capture().execution_snapshot();
    let current_selection = current.capture().execution_snapshot();
    let references = Arc::strong_count(&opaque);
    checkpoints.push(world.service_snapshot());
    checkpoints.push(
        world
            .service_episode_snapshot(consumer, &downstream)
            .unwrap(),
    );
    assert_eq!(Arc::strong_count(&opaque), references);
    world
        .withdraw_managed_execution(provider, &mut upstream, false)
        .unwrap();
    world.settle_managed_execution(provider, &upstream).unwrap();
    assert!(world.native_value(port(1)).is_none());
    assert!(world.begin_cleanup(provider).is_err());
    downstream.register(0, "retryable inverse".into()).unwrap();
    world
        .withdraw_managed_execution(consumer, &mut downstream, false)
        .unwrap();
    world
        .settle_managed_execution(consumer, &downstream)
        .unwrap();
    world.begin_cleanup(consumer).unwrap();
    let (stale, action) = downstream.pop(0).unwrap().unwrap();
    downstream
        .complete_result(
            0,
            stale,
            Err("transient"),
            Some(action),
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    world.fail_managed_execution(consumer, &downstream).unwrap();
    checkpoints.push(
        world
            .service_episode_snapshot(consumer, &downstream)
            .unwrap(),
    );
    assert!(world
        .release_managed_execution(consumer, &mut downstream)
        .is_err());
    assert_eq!(
        downstream.read(port(4)).unwrap().1.opaque().unwrap(),
        "opaque payload"
    );
    world
        .retry_managed_execution(consumer, &mut downstream)
        .unwrap();
    let (fresh, _) = downstream.pop(0).unwrap().unwrap();
    assert!(downstream
        .complete_result(
            0,
            stale,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
    downstream
        .complete_result(
            0,
            fresh,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    let (_, released) = world
        .release_managed_execution(consumer, &mut downstream)
        .unwrap();
    drop(released);
    assert!(world
        .service_episode_snapshot(consumer, &downstream)
        .is_none());
    world.begin_cleanup(provider).unwrap();
    let (_, released) = world
        .release_managed_execution(provider, &mut upstream)
        .unwrap();
    drop(released);
    drop(opaque);
    assert!(weak_opaque.upgrade().is_none());
    // Erased evidence does not keep executable service maps or payloads alive.
    for checkpoint in checkpoints {
        let _ = checkpoint.joint().refresh();
    }
    let _ = (old_selection.refresh(), current_selection.refresh());
}

#[test]
fn observed_effect_retirement_keeps_status_until_actual_retry_succeeds() {
    use cordis_kernel::host_status::HostStatus;
    let mut world = World::new(2100);
    let id = register(&mut world, 1, vec![]);
    let (mut episode, _) = activate(&mut world, id, 1, 2101);
    let group = episode
        .enqueue_effect(0, 2102, vec![], "iterator".into())
        .unwrap();
    let other = episode
        .enqueue_effect(0, 2103, vec![], "other iterator".into())
        .unwrap();
    let mut status: HostStatus<String> = episode.effect_status(group).unwrap();
    let wrong: HostStatus<String> = episode.effect_status(other).unwrap();
    assert!(!status.report_service_finished());
    assert!(!status.report_service_initialized());
    assert!(episode.initialize_effect_status(group).is_none());
    for _ in 0..2 {
        let item = episode.take_group().unwrap();
        let reply = item.run(|request| episode.activate_effect(request));
        assert!(episode.complete_request(reply).ok().unwrap().is_ok());
    }
    episode.register(group, "retained inverse".into()).unwrap();
    let run = episode.take_effect(group).unwrap();
    status.cancel();
    assert!(!status.observe().initialized());
    assert!(!status.observe().finished());
    episode.cancel(group);
    assert!(episode
        .initialize_effect_status(group)
        .unwrap()
        .initialized());
    let run = episode.retire_observed_effect(run).err().unwrap();
    assert!(!wrong.observe().initialized());
    assert!(!wrong.observe().finished());
    let run = episode.retire_observed_effect(run).err().unwrap();
    let (old, inverse) = episode.pop(group).unwrap().unwrap();
    episode
        .complete_result(
            group,
            old,
            Err("blocked"),
            Some(inverse),
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    status.push_error("blocked".into());
    let run = episode.retire_observed_effect(run).err().unwrap();
    assert!(episode.contains(group));
    assert!(!status.observe().finished());
    let failed = status.execution_snapshot();
    episode.retry(group).unwrap();
    let (current, _) = episode.pop(group).unwrap().unwrap();
    assert_ne!(current, old);
    assert!(episode
        .complete_result(
            group,
            old,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
    episode
        .complete_result(
            group,
            current,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    assert_eq!(
        episode.retire_observed_effect(run).ok().unwrap().0,
        "iterator"
    );
    assert!(status.observe().initialized());
    assert!(status.observe().finished());
    assert!(!episode.contains(group));
    assert_eq!(status.errors(), &vec!["blocked".to_owned()]);
    let _ = failed.refresh();
    let _ = status.execution_snapshot();
    status.cancel(); // A late cloned handle cannot reopen the retired group.
    assert!(status.observe().finished());
    assert!(!wrong.observe().finished());
}

#[test]
fn service_failure_is_a_terminal_join_report_and_never_effect_completion() {
    use cordis_kernel::host_status::HostStatus;
    let mut status = HostStatus::<String>::external_service();
    assert!(status.assign_child(7));
    assert!(!status.assign_child(8));
    assert!(status.report_service_initialized());
    status.push_error("first failure".into());
    assert!(status.report_terminal("first failure".into()).is_none());
    assert_eq!(
        status.report_terminal("later failure".into()),
        Some("later failure".into())
    );
    assert_eq!(status.terminal_error().unwrap(), "first failure");
    assert_eq!(status.external_child_id(), Some(7));
    assert!(status.observe().cancelled());
    assert!(!status.observe().finished());
    assert!(!status.report_service_finished());
    assert_eq!(status.errors().len(), 1);
    let _ = status.execution_snapshot();
}

#[test]
fn controlled_failure_restart_retry_and_release_keep_one_episode() {
    use cordis_kernel::poll_control::PollControl;
    let mut world = World::new(2200);
    let id = register(&mut world, 1, vec![]);
    let mut control: PollControl<String> = world.poll_control(id).unwrap();
    assert!(control.record_setup_failure("first".into()).is_none());
    assert_eq!(
        control.record_setup_failure("later".into()).as_deref(),
        Some("later")
    );
    assert_eq!(control.failed().map(String::as_str), Some("first"));
    assert!(world
        .begin_controlled_execution::<String, String, String, _>(id, 2201, &mut control)
        .is_err());
    assert_eq!(
        world.request_restart(&mut control).unwrap().as_deref(),
        Some("first")
    );
    assert!(!control.restart_requested()); // Inactive restart only clears setup failure.
    let (mut episode, discarded): (Episode, _) = world
        .begin_controlled_execution(id, 2201, &mut control)
        .unwrap();
    assert!(discarded.is_none());
    assert!(control.matches_execution(&episode));
    complete(&mut world, id, &mut episode);
    episode.provide(port(1), Arc::new("value".into())).unwrap();
    world.finish_managed_execution(id, &mut episode).unwrap();
    episode.register(0, "retryable".into()).unwrap();
    world.request_restart(&mut control).unwrap();
    assert!(control.restart_requested());
    withdraw(&mut world, id, &mut episode);
    let previous = world.begin_cleanup(id).unwrap();
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
    control.record_cleanup_failure("cleanup".into());
    let failed = control.execution_snapshot();
    assert!(world
        .retry_controlled_execution(id, &mut episode, &mut control)
        .is_err());
    assert_eq!(
        control.cleanup_failure().map(String::as_str),
        Some("cleanup")
    );
    control.record_setup_failure("setup".into());
    assert_eq!(
        world.request_restart(&mut control).unwrap().as_deref(),
        Some("setup")
    );
    assert_eq!(
        control.cleanup_failure().map(String::as_str),
        Some("cleanup")
    );
    assert!(control.poll_flags().failed);
    assert!(world
        .release_controlled_execution(id, &mut episode, &mut control)
        .is_err());
    assert!(control.restart_requested());
    world.fail_managed_execution(id, &episode).unwrap();
    let (retry, discarded) = world
        .retry_controlled_execution(id, &mut episode, &mut control)
        .unwrap();
    assert!(retry.action > previous.action);
    assert_eq!(discarded.as_deref(), Some("cleanup"));
    assert!(!control.poll_flags().failed);
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
    world
        .release_controlled_execution(id, &mut episode, &mut control)
        .unwrap();
    assert!(!control.restart_requested());
    assert!(!control.matches_execution(&episode));
    let _ = failed.refresh();
    let (new_episode, _): (Episode, _) = world
        .begin_controlled_execution(id, 2201, &mut control)
        .unwrap();
    assert!(control.matches_execution(&new_episode));
    assert!(!control.matches_execution(&episode)); // Domain reuse cannot replace Begin identity.
    assert!(world
        .release_controlled_execution(id, &mut episode, &mut control)
        .is_err());
    assert!(control.matches_execution(&new_episode));
}

#[test]
fn handle_origin_rejects_foreign_episode_before_initialization_or_retirement() {
    use cordis_kernel::host_status::HostStatus;
    let mut world = World::new(2210);
    let a = register(&mut world, 1, vec![]);
    let b = register(&mut world, 2, vec![]);
    let (mut first, _) = activate(&mut world, a, 1, 2211);
    let (mut second, _) = activate(&mut world, b, 2, 2211);
    let first_group = first
        .enqueue_effect(0, 2212, vec![], "first".into())
        .unwrap();
    let second_group = second
        .enqueue_effect(0, 2212, vec![], "second".into())
        .unwrap();
    assert_eq!(first_group, second_group);
    let foreign: HostStatus<String> = second.effect_status(second_group).unwrap();
    assert!(!foreign.matches_episode(&first));
    let item = first.take_group().unwrap();
    let reply = item.run(|request| first.activate_effect(request));
    assert!(first.complete_request(reply).ok().unwrap().is_ok());
    first.cancel(first_group);
    assert!(first.initialize_effect_status(first_group).is_none());
    let run = first.take_effect(first_group).unwrap();
    let run = first.retire_observed_effect(run).err().unwrap();
    assert!(first.contains(first_group));
    assert!(!foreign.observe().initialized());
    assert!(!foreign.observe().finished());
    assert!(!foreign.observe().cancelled());
    assert!(first.put_effect(run).is_ok());
}

#[test]
fn native_effects_use_begin_bindings_and_reject_external_or_closed_owners() {
    let mut external: Episode = Execution::new(2240);
    assert_eq!(
        external.enqueue_native_effect(0, 2241, "external".into()),
        Err("external".into())
    );
    assert!(external.native_context().is_none());
    assert!(external.take_group().is_none());

    let mut world = World::new(2250);
    let provider = register(&mut world, 1, vec![]);
    let (mut upstream, _) = activate(&mut world, provider, 1, 2251);
    let consumer = register(&mut world, 2, vec![1]);
    let (mut episode, _) = activate(&mut world, consumer, 2, 2252);
    let context = episode.native_context().unwrap();
    let first = episode
        .enqueue_native_effect(0, 2253, "parent".into())
        .unwrap();
    let nested = episode
        .enqueue_native_effect(first, 2254, "nested".into())
        .unwrap();
    for id in [first, nested] {
        let item = episode.take_group().unwrap();
        let reply = item.run(|request| episode.activate_effect(request));
        assert!(episode.complete_request(reply).ok().unwrap().is_ok());
        let mut run = episode.take_effect(id).unwrap();
        assert!(episode.admit_effect(&mut run, Some(context.committed())));
        assert!(episode.put_effect(run).is_ok());
    }
    // The target disappears but the already issued context keeps Begin's
    // providers. A later iterator cannot silently use an empty binding list.
    world
        .withdraw_managed_execution(provider, &mut upstream, true)
        .unwrap();
    world.leave(provider).unwrap();
    assert!(world.kernel().target(consumer).is_none());
    let late = episode
        .enqueue_native_effect(0, 2255, "late".into())
        .unwrap();
    let item = episode.take_group().unwrap();
    let reply = item.run(|request| episode.activate_effect(request));
    assert!(episode.complete_request(reply).ok().unwrap().is_ok());
    let mut run = episode.take_effect(late).unwrap();
    assert!(!episode.admit_effect(&mut run, Some(&[])));
    assert!(episode.put_effect(run).is_ok());
    assert_eq!(context.committed()[0].provider, provider);
    assert!(episode.observe_execution().is_some());
    episode.withdraw();
    assert_eq!(
        episode.enqueue_native_effect(0, 2256, "retained".into()),
        Err("retained".into())
    );
    assert!(Arc::ptr_eq(&context, &episode.native_context().unwrap()));
}

#[test]
fn registered_realm_and_anchor_survive_input_changes_and_episode_replacement() {
    use cordis_kernel::realm_context::RealmContext;
    let base = RealmContext::default();
    let isolated = base.with_realm(1, 27).with_realm(9, 81);
    let shared = base.share(1, &isolated);
    assert_eq!(base.resolve(1), port(1));
    assert_eq!(shared.resolve(1), isolated.resolve(1));
    assert_eq!(shared.resolve(9), port(9));
    let mut realms = isolated.as_map().clone();
    let mut world = World::new(2300);
    let anchor = Port {
        key: 101,
        realm: 55,
    };
    let id = world
        .register(
            None,
            &realms,
            anchor,
            PluginDefinition::new(vec![], vec![1], setup as Callback),
            "registered".into(),
        )
        .ok()
        .unwrap();
    // The caller's map and mutable host bookkeeping are not Begin's authority.
    realms.insert(1, 99);
    *world.host_mut(id).unwrap() = "new bookkeeping".into();
    let mut old: Episode = world.begin_managed_execution(id, 2301).unwrap();
    let context = old.native_context().unwrap();
    assert_eq!(context.realm_context().resolve(1), isolated.resolve(1));
    assert_eq!(context.realm_context().resolve(9), isolated.resolve(9));
    assert_eq!(context.anchor(), anchor);
    let old_scope = old.root_scope().unwrap();
    complete(&mut world, id, &mut old);
    old.provide(isolated.resolve(1), Arc::new("old".into()))
        .unwrap();
    world.finish_managed_execution(id, &mut old).unwrap();
    withdraw(&mut world, id, &mut old);
    world.begin_cleanup(id).unwrap();
    world.release_managed_execution(id, &mut old).unwrap();
    assert!(!old_scope.belongs(&old));
    let current: Episode = world.begin_managed_execution(id, 2302).unwrap();
    let next = current.native_context().unwrap();
    assert_ne!(context.ticket(), next.ticket());
    assert_eq!(
        context.realm_context().as_map(),
        next.realm_context().as_map()
    );
    assert_eq!(next.anchor(), anchor);
    assert!(!old_scope.belongs(&current));
    assert!(current.root_scope().unwrap().belongs(&current));
}

#[test]
fn scoped_dispatch_rejects_another_episode_and_revokes_retired_group() {
    use cordis_kernel::effect_work::EffectOutput;
    let mut world = World::new(2310);
    let first = register(&mut world, 1, vec![]);
    let second = register(&mut world, 2, vec![]);
    let (mut a, _) = activate(&mut world, first, 1, 2311);
    let (mut b, _) = activate(&mut world, second, 2, 2312);
    let aid = a.enqueue_native_effect(0, 2313, "first".into()).unwrap();
    let bid = b.enqueue_native_effect(0, 2314, "second".into()).unwrap();
    assert_eq!(aid, bid); // A group number alone cannot identify a callback scope.
    for episode in [&mut a, &mut b] {
        let item = episode.take_group().unwrap();
        let reply = item.run(|request| episode.activate_effect(request));
        assert!(episode.complete_request(reply).ok().unwrap().is_ok());
    }
    let mut arun = a.take_effect(aid).unwrap();
    let mut brun = b.take_effect(bid).unwrap();
    let ascope = a.admit_scoped_effect(&mut arun, Some(&[])).unwrap();
    let bscope = b.admit_scoped_effect(&mut brun, Some(&[])).unwrap();
    assert!(!ascope.belongs(&b));
    assert!(!bscope.belongs(&a));
    assert!(a.admit_scoped_effect(&mut arun, Some(&[])).is_none());
    let rejected = arun
        .call_scoped(
            (bscope, ()),
            |_, _| -> (String, EffectOutput<String, String>) {
                panic!("a foreign scope must not reach the iterator")
            },
        )
        .err()
        .unwrap();
    arun = rejected.0;
    assert_eq!(arun.get(), "first");
    let (mut arun, reply) = arun
        .call_scoped((ascope, "argument"), |payload, (scope, arg)| {
            assert_eq!(scope, ascope);
            assert_eq!(arg, "argument");
            (payload, EffectOutput::<String, String>::Ready(Ok(None)))
        })
        .ok()
        .unwrap();
    a.land_effect(&mut arun, reply).ok().unwrap();
    assert!(ascope.belongs(&a));
    assert_eq!(a.retire_effect(arun).ok().unwrap(), "first");
    assert!(!ascope.belongs(&a));
    // Its historical queue record is retained, but it is no longer live.
    assert!(a.observe_execution().is_some());
    assert!(a.root_scope().unwrap().belongs(&a));
    assert!(b.put_effect(brun).is_ok());
}

#[test]
fn configuration_targets_bind_domain_activation_and_recipe_revision() {
    let mut world = World::new(3900);
    let id = register(&mut world, 1, vec![]);
    assert!(world.configuration_target(id).is_none());
    let (mut episode, _) = activate(&mut world, id, 1, 3901);
    let target = world.configuration_target(id).unwrap();
    assert_eq!(target.id(), id);
    assert_eq!(target.revision(), 0);
    assert!(world.configuration_target_is_current(target));

    let mut foreign = World::new(3910);
    let other = register(&mut foreign, 1, vec![]);
    let (_other_episode, _) = activate(&mut foreign, other, 1, 3911);
    assert_eq!(other, id);
    assert_eq!(
        foreign.configuration_target(other).unwrap().generation(),
        target.generation()
    );
    assert!(!foreign.configuration_target_is_current(target));
    assert!(matches!(
        foreign.replace_configuration(target, setup as Callback),
        Err((Error::InvalidState, _))
    ));

    world
        .replace_configuration(target, setup as Callback)
        .ok()
        .unwrap();
    let revised = world.configuration_target(id).unwrap();
    assert_eq!(revised.revision(), 1);
    assert_eq!(revised.generation(), target.generation());
    assert!(!world.configuration_target_is_current(target));
    assert!(matches!(
        world.replace_configuration(target, setup as Callback),
        Err((Error::InvalidState, _))
    ));
    assert_eq!(world.registration(id).unwrap().revision(), 1);

    withdraw(&mut world, id, &mut episode);
    assert!(!world.configuration_target_is_current(revised));
    world.begin_cleanup(id).unwrap();
    world.release_managed_execution(id, &mut episode).unwrap();
    let (mut next, _) = activate(&mut world, id, 1, 3902);
    assert!(world.configuration_target(id).unwrap().generation() > revised.generation());
    assert!(!world.configuration_target_is_current(revised));
    let active = world.configuration_target(id).unwrap();
    world
        .withdraw_managed_execution(id, &mut next, true)
        .unwrap();
    assert!(!world.configuration_target_is_current(active));
}

#[test]
fn configuration_batch_rejects_late_stale_or_duplicate_targets_before_any_swap() {
    use cordis_kernel::configuration_runtime::adoption::{Cause, Change};
    use std::sync::atomic::{AtomicUsize, Ordering};
    let mut world = World::new(7800);
    let left = register(&mut world, 1, vec![]);
    let right = register(&mut world, 2, vec![1]);
    let (_left_episode, left_value) = activate(&mut world, left, 1, 7801);
    let (_right_episode, right_value) = activate(&mut world, right, 2, 7802);
    let a = world.configuration_target(left).unwrap();
    let stale = world.configuration_target(right).unwrap();
    world
        .replace_configuration(stale, setup as Callback)
        .ok()
        .unwrap();
    let b = world.configuration_target(right).unwrap();
    let calls = AtomicUsize::new(0);
    let update = |host: &mut String, next: String| {
        calls.fetch_add(1, Ordering::SeqCst);
        std::mem::replace(host, next)
    };
    for (targets, cause) in [([a, stale], Cause::Target), ([a, a], Cause::Duplicate)] {
        let changes = targets
            .iter()
            .enumerate()
            .map(|(i, target)| Change {
                target: *target,
                recipe: setup as Callback,
                metadata: format!("candidate {i}"),
            })
            .collect();
        let rejected = match world.adopt_configurations(changes, update) {
            Err(rejected) => rejected,
            Ok(_) => panic!("invalid late target must reject the entire batch"),
        };
        assert_eq!((rejected.failure.index, rejected.failure.cause), (1, cause));
        assert_eq!(rejected.changes.len(), 2);
        for (i, change) in rejected.changes.iter().enumerate() {
            assert_eq!(change.target, targets[i]);
            assert_eq!(change.metadata, format!("candidate {i}"));
            assert_eq!((change.recipe)(i), Ok(()));
        }
        assert_eq!(calls.load(Ordering::SeqCst), 0);
        assert_eq!(world.configuration_target(left), Some(a));
        assert_eq!(world.configuration_target(right), Some(b));
        assert_eq!(world.host(left).unwrap(), "host 1");
        assert_eq!(world.host(right).unwrap(), "host 2");
        assert!(Arc::ptr_eq(
            world.native_value(port(1)).unwrap(),
            &left_value
        ));
        assert!(Arc::ptr_eq(
            world.native_value(port(2)).unwrap(),
            &right_value
        ));
    }
}

#[test]
fn configuration_batch_adopts_exact_order_and_payloads_without_restarting_live_episodes() {
    use cordis_kernel::configuration_runtime::adoption::Change;
    fn first(_: usize) -> Result<(), String> {
        Err("first replacement".into())
    }
    fn second(_: usize) -> Result<(), String> {
        Err("second replacement".into())
    }
    let mut world = World::new(7810);
    let left = register(&mut world, 1, vec![]);
    let right = register(&mut world, 2, vec![1]);
    let (_left_episode, left_value) = activate(&mut world, left, 1, 7811);
    let (_right_episode, right_value) = activate(&mut world, right, 2, 7812);
    let a = world.configuration_target(left).unwrap();
    let b = world.configuration_target(right).unwrap();
    let previous = world
        .adopt_configurations(
            vec![
                Change {
                    target: b,
                    recipe: second as Callback,
                    metadata: "next right".to_owned(),
                },
                Change {
                    target: a,
                    recipe: first as Callback,
                    metadata: "next left".to_owned(),
                },
            ],
            std::mem::replace,
        )
        .ok()
        .unwrap();
    assert_eq!(previous.len(), 2);
    assert_eq!((previous[0].target, previous[1].target), (b, a));
    assert_eq!(
        (&*previous[0].metadata, &*previous[1].metadata),
        ("host 2", "host 1")
    );
    assert_eq!((previous[0].recipe)(0), Ok(()));
    assert_eq!((previous[1].recipe)(0), Ok(()));
    assert_eq!(
        (world.registration(left).unwrap().payload_ref())(0),
        Err("first replacement".into())
    );
    assert_eq!(
        (world.registration(right).unwrap().payload_ref())(0),
        Err("second replacement".into())
    );
    for (id, before) in [(left, a), (right, b)] {
        let after = world.configuration_target(id).unwrap();
        assert_eq!(after.generation(), before.generation());
        assert_eq!(after.revision(), before.revision() + 1);
        assert!(!world.configuration_target_is_current(before));
        assert_eq!(world.kernel().phase(id), Some(Phase::Active));
    }
    assert_eq!(world.host(left).unwrap(), "next left");
    assert_eq!(world.host(right).unwrap(), "next right");
    assert!(Arc::ptr_eq(
        world.native_value(port(1)).unwrap(),
        &left_value
    ));
    assert!(Arc::ptr_eq(
        world.native_value(port(2)).unwrap(),
        &right_value
    ));
}

#[test]
fn recipe_checkpoints_follow_replacement_and_calls_without_retaining_old_captures() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    type Captured = Box<dyn FnMut(usize) -> Result<(), String>>;
    let first = Arc::new(AtomicUsize::new(0));
    let second = Arc::new(AtomicUsize::new(0));
    let old_counter = first.clone();
    let old_body: Captured = Box::new(move |amount| {
        old_counter.fetch_add(amount, Ordering::SeqCst);
        Ok(())
    });
    let new_counter = second.clone();
    let new_body: Captured = Box::new(move |amount| {
        new_counter.fetch_add(amount, Ordering::SeqCst);
        Ok(())
    });
    let mut world: NativeRuntime<Captured, (), String> = NativeRuntime::new(2950);
    let id = world
        .register(
            None,
            &BTreeMap::new(),
            port(2950),
            PluginDefinition::new(vec![], vec![], old_body),
            (),
        )
        .ok()
        .unwrap();
    let initial = world.recipe_snapshot();
    let mut interrupted: Episode = world.begin_managed_execution(id, 2951).unwrap();
    let admitted = world.admit_managed_root(id, &mut interrupted, 3).unwrap();
    let displaced = world.replace(id, new_body).ok().unwrap();
    let replaced = world.recipe_snapshot();
    drop(displaced);
    assert_eq!(
        Arc::strong_count(&first),
        1,
        "erased snapshots must not retain old callback captures"
    );
    let rejected = world.call(id, admitted).err().unwrap();
    assert_eq!(first.load(Ordering::SeqCst), 0);
    assert_eq!(second.load(Ordering::SeqCst), 0);
    world
        .withdraw_managed_execution(id, &mut interrupted, false)
        .unwrap();
    assert!(interrupted.cancel_queued_root(rejected.ticket()));
    world.settle_managed_execution(id, &interrupted).unwrap();
    world.begin_cleanup(id).unwrap();
    world
        .release_managed_execution(id, &mut interrupted)
        .unwrap();
    let mut current: Episode = world.begin_managed_execution(id, 2952).unwrap();
    let admitted = world.admit_managed_root(id, &mut current, 7).unwrap();
    let receipt = world.call(id, admitted).ok().unwrap();
    current.complete_root(receipt).ok().unwrap().unwrap();
    world.finish_managed_execution(id, &mut current).unwrap();
    let invoked = world.recipe_snapshot();
    assert_eq!(second.load(Ordering::SeqCst), 7);
    world
        .withdraw_managed_execution(id, &mut current, true)
        .unwrap();
    world.leave(id).unwrap();
    world.settle_managed_execution(id, &current).unwrap();
    world.begin_cleanup(id).unwrap();
    world.release_managed_execution(id, &mut current).unwrap();
    drop(world.remove(id).ok().unwrap());
    let removed = world.recipe_snapshot();
    assert!(world.is_empty());
    assert_eq!(Arc::strong_count(&second), 1);
    drop((initial, replaced, invoked, removed));
}

#[test]
fn configuration_checkpoint_follows_actual_native_failure_and_recovery_interleaving() {
    use cordis_kernel::configuration_recorded::{Load, Recorded};
    use cordis_kernel::configuration_transaction::{Structure, StructureError, TransactionError};
    use std::task::Poll;

    let mut world = World::new(1870);
    let mut configuration: Recorded<&str, usize, (), (), String, String> =
        world.configuration("accepted");
    let id = register(&mut world, 1, vec![]);
    let (mut episode, value) = activate(&mut world, id, 1, 1871);
    configuration
        .load_sources(Load {
            root: "config.json".into(),
            contents: BTreeMap::from([("config.json".into(), "original bytes".into())]),
            checkpoints: vec![("config.json".into(), "accepted base".into())],
            resolutions: BTreeMap::new(),
        })
        .unwrap();
    let before = world.configuration_snapshot(&configuration);
    assert!(configuration
        .begin_structural("candidate", 0, vec![])
        .is_ok());
    assert_eq!(
        configuration.poll_structure::<&str, _>(|phase, accepted, pending| {
            assert_eq!((phase, *accepted), (Structure::Remove, "accepted"));
            pending.recovery += 1;
            // A real lifecycle transition inside the configuration callback uses
            // the same Journal. Holding its lock across this call would deadlock.
            withdraw(&mut world, id, &mut episode);
            Poll::Pending
        }),
        Poll::Pending
    );
    assert_eq!(world.kernel().phase(id), Some(Phase::Unloading));
    assert_eq!(
        configuration.clear_sources(),
        Err(TransactionError::Pending)
    );
    assert_eq!(world.value_count(), 1);
    assert!(Arc::ptr_eq(
        episode.native().unwrap().own(port(1)).unwrap(),
        &value
    ));
    let pending = world.configuration_snapshot(&configuration);
    assert_eq!(
        configuration.poll_structure(|_, _, _| Poll::Ready(Err("remove failed"))),
        Poll::Ready(Err(StructureError::Callback("remove failed")))
    );
    assert_eq!(
        configuration.poll_rollback::<(), _>(|_, _| panic!("empty batch")),
        Poll::Ready(Ok(true))
    );
    for phase in [
        Structure::RecoverRemove,
        Structure::RecoverSettleRemoved,
        Structure::RecoverMount,
        Structure::RecoverSettleMounted,
    ] {
        assert_eq!(configuration.structure(), Some(phase));
        assert!(configuration
            .poll_structure::<(), _>(|actual, _, _| {
                if actual == Structure::RecoverRemove {
                    world.begin_cleanup(id).unwrap();
                    world.release_managed_execution(id, &mut episode).unwrap();
                }
                Poll::Ready(Ok(()))
            })
            .is_ready());
    }
    assert!(configuration
        .recover_with(|attempts| {
            assert_eq!(*attempts, 1);
            "recovered"
        })
        .is_ok());
    assert_eq!(world.kernel().phase(id), Some(Phase::Inactive));
    assert_eq!(world.value_count(), 0);
    assert_eq!(configuration.revision(), 0);
    assert_eq!(configuration.current(), &"recovered");
    assert_eq!(
        configuration.sources().checkpoints()["config.json"].value,
        "accepted base"
    );
    let recovered = world.configuration_snapshot(&configuration);
    // These real read checkpoints retain erased, complete native/configuration/
    // source projections. Rust assertions above exercise the actual payloads.
    drop((
        before.into_joint(),
        pending.into_joint(),
        recovered.into_joint(),
    ));
}

#[test]
fn status_factory_is_single_owner_and_raw_retirement_notifies_escaped_handle() {
    use cordis_kernel::host_status::HostStatus;
    let mut world = World::new(2215);
    let id = register(&mut world, 1, vec![]);
    let (mut episode, _) = activate(&mut world, id, 1, 2216);
    let group = episode
        .enqueue_effect(0, 2217, vec![], "owned".into())
        .unwrap();
    let status: HostStatus<String> = episode.effect_status(group).unwrap();
    assert!(episode.effect_status::<String>(group).is_none());
    let item = episode.take_group().unwrap();
    let reply = item.run(|request| episode.activate_effect(request));
    assert!(episode.complete_request(reply).ok().unwrap().is_ok());
    episode.cancel(group);
    assert!(!episode.remove(group));
    let run = episode.take_effect(group).unwrap();
    // Even the API that returns only the payload advances the installed status.
    assert_eq!(episode.retire_effect(run).ok().unwrap(), "owned");
    assert!(status.observe().initialized());
    assert!(status.observe().finished());
    assert!(episode.effect_status::<String>(group).is_none());
    assert!(episode.initialize_effect_status(group).is_none());
    let _ = status.execution_snapshot();
}

#[test]
fn independent_journals_with_identical_numeric_origins_keep_their_own_status() {
    use cordis_kernel::host_status::HostStatus;
    let mut first_world = World::new(2220);
    let mut second_world = World::new(2220);
    let first_id = register(&mut first_world, 1, vec![]);
    let second_id = register(&mut second_world, 1, vec![]);
    assert_eq!(first_id, second_id);
    let (mut first, _) = activate(&mut first_world, first_id, 1, 2221);
    let (mut second, _) = activate(&mut second_world, second_id, 1, 2221);
    assert_eq!(first.lifecycle_ticket(), second.lifecycle_ticket());
    let a = first
        .enqueue_effect(0, 2222, vec![], "first".into())
        .unwrap();
    let b = second
        .enqueue_effect(0, 2222, vec![], "second".into())
        .unwrap();
    assert_eq!(a, b);
    let own: HostStatus<String> = first.effect_status(a).unwrap();
    let foreign: HostStatus<String> = second.effect_status(b).unwrap();
    // Numeric matching is intentionally insufficient to identify a Journal.
    assert!(foreign.matches_episode(&first));
    let item = first.take_group().unwrap();
    let reply = item.run(|request| first.activate_effect(request));
    assert!(first.complete_request(reply).ok().unwrap().is_ok());
    first.cancel(a);
    assert!(first.initialize_effect_status(a).unwrap().initialized());
    assert!(own.observe().initialized());
    assert!(!foreign.observe().initialized());
    let run = first.take_effect(a).unwrap();
    let (payload, observed) = first.retire_observed_effect(run).ok().unwrap();
    assert_eq!(payload, "first");
    assert!(observed.finished());
    assert!(own.observe().finished());
    assert!(!foreign.observe().finished());
    assert!(second.contains(b));
    let _ = (own.execution_snapshot(), foreign.execution_snapshot());
}

#[test]
fn retained_status_link_does_not_retain_the_observers_error_payloads() {
    use cordis_kernel::host_status::HostStatus;
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    struct ErrorPayload(Arc<AtomicUsize>);
    impl Drop for ErrorPayload {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    let dropped = Arc::new(AtomicUsize::new(0));
    let mut world = World::new(2225);
    let id = register(&mut world, 1, vec![]);
    let (mut episode, _) = activate(&mut world, id, 1, 2226);
    let group = episode
        .enqueue_effect(0, 2227, vec![], "owned".into())
        .unwrap();
    let mut status: HostStatus<ErrorPayload> = episode.effect_status(group).unwrap();
    status.push_error(ErrorPayload(dropped.clone()));
    drop(status);
    assert_eq!(dropped.load(Ordering::SeqCst), 1);
    // Execution still retains the checked link and can complete its protocol.
    let item = episode.take_group().unwrap();
    let reply = item.run(|request| episode.activate_effect(request));
    assert!(episode.complete_request(reply).ok().unwrap().is_ok());
    episode.cancel(group);
    let run = episode.take_effect(group).unwrap();
    let (_, observed) = episode.retire_observed_effect(run).ok().unwrap();
    assert!(observed.finished());
    assert_eq!(dropped.load(Ordering::SeqCst), 1);
}
