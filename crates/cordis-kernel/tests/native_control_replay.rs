use cordis_kernel::execution::Execution;
use cordis_kernel::kernel_replay::{names, Command};
use cordis_kernel::lifecycle_state::native::runtime::NativeRuntime;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::{Phase, Port};
use std::collections::BTreeMap;
use std::sync::Arc;
use vstd::prelude::Ghost;

type Callback = fn(usize) -> Result<(), String>;
type World = NativeRuntime<Callback, (), String>;
type Episode = Execution<String, (), (), ()>;
fn setup(_: usize) -> Result<(), String> {
    Ok(())
}
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn register(world: &mut World, parent: Option<usize>, key: u64, dependencies: Vec<u64>) -> usize {
    world
        .register(
            parent,
            &BTreeMap::new(),
            port(100 + key),
            PluginDefinition::new(dependencies, vec![key], setup as Callback),
            (),
        )
        .ok()
        .unwrap()
}
fn activate(world: &mut World, actor: usize, key: u64, domain: u64) -> Episode {
    let mut episode: Episode = world.begin_managed_execution(actor, domain).unwrap();
    let call = world
        .admit_managed_root(actor, &mut episode, actor)
        .unwrap();
    let result = world.call(actor, call).ok().unwrap();
    episode.complete_root(result).ok().unwrap().unwrap();
    episode
        .provide(port(key), Arc::new(format!("service {key}")))
        .unwrap();
    world.finish_managed_execution(actor, &mut episode).unwrap();
    episode
}
fn unload(world: &mut World, actor: usize, episode: &mut Episode) {
    world
        .withdraw_managed_execution(actor, episode, false)
        .unwrap();
    world.settle_managed_execution(actor, episode).unwrap();
    world.begin_cleanup(actor).unwrap();
    world.release_managed_execution(actor, episode).unwrap();
}
#[test]
fn actual_native_source_replays_with_compacted_ids_parents_bindings_and_generations() {
    let mut world = World::new_recorded(3100, 64);
    let owner = register(&mut world, None, 1, vec![]);
    let mut earlier = activate(&mut world, owner, 1, 3101);
    unload(&mut world, owner, &mut earlier);
    let start = world
        .control_source_snapshot()
        .unwrap()
        .source
        .commands()
        .len();
    let mut middle = activate(&mut world, owner, 1, 3102);
    let child = register(&mut world, Some(owner), 2, vec![]);
    let mut child_run = activate(&mut world, child, 2, 3103);
    unload(&mut world, child, &mut child_run);
    world.retire(child).unwrap();
    world.remove(child).ok().unwrap();
    unload(&mut world, owner, &mut middle);
    let end = world
        .control_source_snapshot()
        .unwrap()
        .source
        .commands()
        .len();
    let later = register(&mut world, None, 3, vec![]);
    let _owner_run = activate(&mut world, owner, 1, 3104);
    let _later_run = activate(&mut world, later, 3, 3105);
    let consumer = register(&mut world, Some(later), 4, vec![3]);
    let _consumer_run = activate(&mut world, consumer, 4, 3106);
    let snapshot = world.control_source_snapshot().unwrap();
    assert_eq!((start, end, snapshot.source.commands().len()), (5, 16, 24));
    let keep: Vec<_> = (0..snapshot.source.commands().len())
        .map(|i| i < start || i >= end)
        .collect();
    // The erased Window selects [5,16), episodes {owner, child}, born {child}.
    // The generic Verus theorem establishes execution from these source
    // conditions; this test exercises the actual adapters and allocations.
    let replay = snapshot
        .source
        .replay(&snapshot.cut, &keep, Ghost::assume_new())
        .unwrap();
    let kernel = replay.execution.kernel();
    assert_eq!(replay.plan.commands.len(), 13);
    assert_eq!(world.kernel().identity_slots(), 4);
    assert_eq!(kernel.identity_slots(), 3);
    assert_eq!(world.ids(), vec![owner, later, consumer]);
    assert_eq!(kernel.ids(), vec![0, 1, 2]);
    assert_eq!(replay.plan.names.name(later), 1);
    assert_eq!(replay.plan.names.name(consumer), 2);
    assert_eq!(kernel.children(1), vec![2]);
    assert_eq!(kernel.committed(2)[0].provider, 1);
    assert_eq!(world.kernel().committed(consumer)[0].provider, later);
    assert_eq!(world.kernel().episode_generation(owner), Some(3));
    assert_eq!(kernel.episode_generation(0), Some(2));
    assert_eq!(kernel.episode_generation(1), Some(1));
    for id in kernel.ids() {
        assert_eq!(kernel.phase(id), Some(Phase::Active));
    }
    // Replay owns a fresh Kernel. It cannot overwrite the source runtime.
    assert_eq!(world.kernel().episode_generation(owner), Some(3));
    assert_eq!(world.native_value(port(3)).unwrap().as_str(), "service 3");
}
#[test]
fn malformed_source_allocation_metadata_is_rejected() {
    let birth = |actor| Command::Insert {
        actor,
        parent: None,
        dependencies: vec![],
        provisions: vec![],
    };
    assert!(matches!(
        names::compact(&[birth(0)], &[], 1),
        Err(names::Error::MaskLength)
    ));
    assert!(matches!(
        names::compact(&[birth(2)], &[true], 2),
        Err(names::Error::BirthBound { index: 0 })
    ));
    assert!(matches!(
        names::compact(&[birth(0), birth(0)], &[true, false], 1),
        Err(names::Error::DuplicateBirth {
            first: 0,
            second: 1
        })
    ));
}

#[test]
fn recording_is_opt_in_bounded_and_never_turns_truncation_into_a_source() {
    use cordis_kernel::lifecycle_state::native::runtime::control_source::{Error, Status};
    let ordinary = World::new(3200);
    assert!(matches!(
        ordinary.control_source_snapshot(),
        Err(Error::Disabled)
    ));
    let mut world = World::new_recorded(3201, 1);
    let id = register(&mut world, None, 1, vec![]);
    let snapshot = world.control_source_snapshot().unwrap();
    assert_eq!(snapshot.source.commands().len(), 1);
    assert_eq!(snapshot.source.allocation_bound(), 1);
    // A rejected operation does not consume recorder capacity.
    assert!(world.remove(999).is_err());
    assert_eq!(world.control_recording_status(), Status::Recording);
    assert_eq!(
        world
            .control_source_snapshot()
            .unwrap()
            .source
            .commands()
            .len(),
        1
    );
    // The next successful operation still runs, but the truncated record cannot
    // be certified. The earlier detached snapshot remains unchanged.
    let _: Episode = world.begin_managed_execution(id, 3202).unwrap();
    assert_eq!(world.control_recording_status(), Status::Exhausted);
    assert!(matches!(
        world.control_source_snapshot(),
        Err(Error::Exhausted)
    ));
    assert_eq!(world.kernel().phase(id), Some(Phase::Loading));
    assert_eq!(snapshot.source.commands().len(), 1);
    let replay = snapshot
        .source
        .replay(&snapshot.cut, &[true], Ghost::assume_new())
        .unwrap();
    assert_eq!(replay.execution.kernel().phase(id), Some(Phase::Inactive));
    let mut zero = World::new_recorded(3203, 0);
    assert!(zero.control_source_snapshot().is_ok());
    register(&mut zero, None, 1, vec![]);
    assert!(matches!(
        zero.control_source_snapshot(),
        Err(Error::Exhausted)
    ));
}

#[test]
fn commands_use_resolved_inheritance_and_the_private_anchor() {
    let mut world = World::new_recorded(3300, 16);
    let provider = register(&mut world, None, 1, vec![]);
    let _service = activate(&mut world, provider, 1, 3301);
    let parent = register(&mut world, None, 2, vec![1]);
    let _parent_run = activate(&mut world, parent, 2, 3302);
    let child = register(&mut world, Some(parent), 3, vec![]);
    let captured = world.control_source_snapshot().unwrap();
    let Command::Insert {
        actor,
        parent: owner,
        dependencies,
        provisions,
    } = captured.source.commands().last().unwrap()
    else {
        panic!("successful child registration is recorded");
    };
    assert_eq!((*actor, *owner), (child, Some(parent)));
    assert!(dependencies.contains(&port(1)));
    assert!(provisions.contains(&port(3)));
    assert!(provisions.contains(&port(103)));
    assert_eq!(provisions.len(), 2);
}
