use super::*;
use cordis_kernel::cleanup_groups::payload::Dispatch;
use cordis_kernel::cleanup_queue::completion::{CleanupDispatch, CleanupPolicy};
use cordis_kernel::poll_control::PollControl;
use cordis_kernel::reversible_value::managed::Action;

pub(super) type Callback = fn(usize) -> Result<(), &'static str>;
pub(super) type World<V> = NativeDriver<Callback, (), V>;
pub(super) type Core<V, I> = Execution<V, (), (), I>;
pub(super) type Managed = RecordedExecution<(), (), (), (), u64, (), ()>;
pub(super) type ManagedCore = Core<Slot<u64, ()>, Action<(), (), u64, (), ()>>;

fn setup(_: usize) -> Result<(), &'static str> {
    Ok(())
}
pub(super) fn world<V>() -> (World<V>, usize) {
    // Deliberately reuse every numeric namespace. The public factory normally
    // allocates fresh domains; that must not be what makes these tests pass.
    let mut driver = NativeDriver {
        state: NativeRuntime::new(7300),
    };
    let id = driver
        .register_plugin(
            None,
            &BTreeMap::new(),
            Port { key: 1, realm: 0 },
            PluginDefinition::new(vec![], vec![], setup as Callback),
            (),
        )
        .ok()
        .unwrap();
    (driver, id)
}
pub(super) fn activate<V, I, E>(
    world: &mut World<V>,
    id: usize,
    control: &mut PollControl<E>,
) -> Core<V, I> {
    let (mut run, discarded) = world.begin_controlled_execution(id, 7301, control).unwrap();
    assert!(discarded.is_none());
    let call = world.admit_managed_root(id, &mut run, id).unwrap();
    let result = world.call_root(id, call).ok().unwrap();
    run.complete_root(result).ok().unwrap().unwrap();
    world.finish_managed_execution(id, &mut run).unwrap();
    run
}
pub(super) fn fail<V, I>(
    world: &mut World<V>,
    id: usize,
    run: &mut Core<V, I>,
    control: &mut PollControl<&'static str>,
    inverse: I,
) {
    run.register(0, inverse).ok().unwrap();
    world.withdraw_managed_execution(id, run, false).unwrap();
    world.settle_managed_execution(id, run).unwrap();
    world.begin_cleanup(id).unwrap();
    let (ticket, inverse) = run.pop(0).unwrap().unwrap();
    run.complete_result(
        0,
        ticket,
        Err("failed"),
        Some(inverse),
        CleanupPolicy::RetainFailure,
    )
    .ok()
    .unwrap();
    control.record_cleanup_failure("retained");
    world.fail_managed_execution(id, run).unwrap();
}

pub(super) fn complete_recorded(owner: &mut Managed) {
    let Dispatch::Other(CleanupDispatch::Host { ticket, action }) =
        owner.dispatch(0).ok().unwrap().unwrap()
    else {
        panic!("expected host cleanup")
    };
    drop(action);
    owner
        .complete_result(
            0,
            ticket,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
}
