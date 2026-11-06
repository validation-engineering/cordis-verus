//! Real request/cleanup objects, with deliberately colliding numeric selectors.
use super::test_support::{world, Callback, World};
use super::*;
use cordis_kernel::cleanup_queue::completion::{CleanupDispatch, CleanupPolicy};
use cordis_kernel::lifecycle_state::registration::shared_child::{ChildCleanup, ChildDispatch};
use cordis_kernel::reversible_value::managed::Action;
use cordis_kernel::Phase;

type Run = Execution<(), ChildDispatch<Callback, ()>, (), ChildCleanup<(), ()>>;
type Recorded = RecordedExecution<ChildDispatch<Callback, ()>, (), (), (), u64, (), ()>;
type RecordedCore =
    Execution<Slot<u64, ()>, ChildDispatch<Callback, ()>, (), Action<(), (), u64, (), ()>>;
fn setup(_: usize) -> Result<(), &'static str> {
    Ok(())
}
fn candidate(_: usize) -> Result<(), &'static str> {
    Err("original candidate")
}
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn begin(world: &mut World<()>, parent: usize) -> Run {
    let mut run = world.begin_managed_execution(parent, 7301).unwrap();
    let call = world.admit_managed_root(parent, &mut run, parent).unwrap();
    let result = world.call_root(parent, call).ok().unwrap();
    run.complete_root(result).ok().unwrap().unwrap();
    run
}
fn take(run: &mut Run) -> (Callback, SharedChild) {
    let receipt = run.take_child().unwrap().run(|request| {
        let ChildDispatch::Native(request) = request else {
            panic!("native request")
        };
        request.into_parts()
    });
    run.complete_request(receipt).ok().unwrap()
}
fn allocate(world: &mut World<()>, run: &mut Run, handle: &SharedChild) -> usize {
    let (payload, request) = take(run);
    let id = world
        .register_shared_child(
            &request,
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![], payload),
            (),
        )
        .ok()
        .unwrap();
    assert_eq!(handle.snapshot().identity().unwrap().id(), id);
    id
}

#[test]
fn foreign_pending_child_cannot_allocate_or_cancel_and_returns_original_payloads() {
    let (mut a, ap) = world::<()>();
    let (mut b, bp) = world::<()>();
    let mut ar = begin(&mut a, ap);
    let _br = begin(&mut b, bp);
    let (child, _) = ar
        .enqueue_native_child(0, candidate as Callback)
        .ok()
        .unwrap();
    assert_eq!(child.domain(), b.domain());
    assert_eq!(child.parent_id(), bp);
    assert_eq!(child.generation(), b.episode_generation(bp));
    assert!(a.owns_shared_child(&child));
    assert!(!b.owns_shared_child(&child));
    let (error, definition, ()) = b
        .register_shared_child(
            &child,
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![], candidate as Callback),
            (),
        )
        .err()
        .unwrap();
    assert_eq!(error, Error::InvalidState);
    assert_eq!((definition.into_payload())(0), Err("original candidate"));
    assert_eq!(b.retire_shared_child(&child), Err(Error::InvalidState));
    assert!(child.snapshot().pending());
    assert_eq!(b.ids(), [bp]);
    let id = allocate(&mut a, &mut ar, &child);
    assert_eq!(child.snapshot().identity().unwrap().id(), id);
}

#[test]
fn assigned_child_rejects_foreign_retirement_and_local_removal_stays_idempotent() {
    let (mut a, ap) = world::<()>();
    let (mut b, bp) = world::<()>();
    let mut ar = begin(&mut a, ap);
    let mut br = begin(&mut b, bp);
    let (child, _) = ar.enqueue_native_child(0, setup as Callback).ok().unwrap();
    let (other, _) = br.enqueue_native_child(0, setup as Callback).ok().unwrap();
    let id = allocate(&mut a, &mut ar, &child);
    assert_eq!(allocate(&mut b, &mut br, &other), id);
    assert_eq!(b.retire_shared_child(&child), Err(Error::InvalidState));
    assert!(!a.retired(id));
    assert!(!b.retired(id));
    assert_eq!(b.phase(id), Some(Phase::Inactive));
    let clone = child.clone();
    assert_eq!(a.retire_shared_child(&clone).unwrap().unwrap().id(), id);
    assert!(a.retired(id));
    assert!(a.contains(id)); // Retirement is not registry removal.
    a.remove(id).ok().unwrap();
    assert_eq!(a.retire_shared_child(&child).unwrap().unwrap().id(), id);
    assert!(a.registered_child(id).is_none());
    assert!(b.contains(id));
    assert!(!b.retired(id));
}

#[test]
fn numeric_identity_wrappers_are_unbound_but_local_registration_factory_is_usable() {
    let (mut owner, parent) = world::<()>();
    assert!(owner.registered_child(parent).is_none());
    assert!(owner.registered_child(usize::MAX).is_none());
    let id = owner
        .register_plugin(
            Some(parent),
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![], setup as Callback),
            (),
        )
        .ok()
        .unwrap();
    let raw = owner.registration(id).unwrap().child_identity().unwrap();
    let unbound = SharedChild::from_identity(raw).0;
    assert!(unbound.execution_domain().is_none());
    assert_eq!(
        owner.retire_shared_child(&unbound),
        Err(Error::InvalidState)
    );
    assert!(!owner.retired(id));
    let child = owner.registered_child(id).unwrap();
    assert!(owner.owns_shared_child(&child));
    assert_eq!(child.snapshot().identity(), Some(raw));
    assert!(child.generation().is_none());
    let mut moved = owner;
    assert!(moved.owns_shared_child(&child.clone()));
    assert_eq!(moved.retire_shared_child(&child).unwrap(), Some(raw));
}

#[test]
fn unlinked_raw_child_keeps_raw_host_contract_but_cannot_enter_native_driver() {
    use cordis_kernel::cleanup_groups::CleanupGroups;
    use cordis_kernel::lifecycle_state::native::NativeHost;
    use cordis_kernel::lifecycle_state::services::NativeServices;
    use cordis_kernel::setup_work::SetupWork;
    let (mut owner, parent) = world::<()>();
    let _run = begin(&mut owner, parent);
    let mut raw = NativeHost::new(owner.domain());
    let id = raw
        .register(
            None,
            &BTreeMap::new(),
            port(1),
            PluginDefinition::new(vec![], vec![], setup as Callback),
            (),
        )
        .ok()
        .unwrap();
    type RawWork = SetupWork<ChildDispatch<Callback, ()>, ()>;
    type RawGroups = CleanupGroups<ChildCleanup<(), ()>>;
    let (mut work, mut groups, _): (RawWork, RawGroups, _) = raw
        .begin_native_execution(id, &NativeServices::<()>::new(owner.domain()), 7301)
        .unwrap();
    let (child, _) = work
        .enqueue_native_child(&mut groups, 0, setup as Callback)
        .ok()
        .unwrap();
    assert!(child.execution_domain().is_none());
    assert_eq!(owner.retire_shared_child(&child), Err(Error::InvalidState));
    assert!(owner
        .register_shared_child(
            &child,
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![], setup as Callback),
            ()
        )
        .is_err());
    assert!(child.snapshot().pending());
    assert!(raw
        .register_shared_child(
            &child,
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![], setup as Callback),
            ()
        )
        .result
        .is_ok());
}

#[test]
fn cancelled_child_stays_terminal_across_a_real_parent_restart() {
    let (mut owner, parent) = world::<()>();
    let mut run = begin(&mut owner, parent);
    let (child, _) = run.enqueue_native_child(0, setup as Callback).ok().unwrap();
    let (_, request) = take(&mut run);
    owner.finish_managed_execution(parent, &mut run).unwrap();
    owner
        .withdraw_managed_execution(parent, &mut run, false)
        .unwrap();
    owner.settle_managed_execution(parent, &run).unwrap();
    owner.begin_cleanup(parent).unwrap();
    let (ticket, inverse) = run.pop(0).unwrap().unwrap();
    let ChildCleanup::Native(inverse) = inverse else {
        panic!("actual child inverse")
    };
    let result = owner.retire_shared_child(&inverse);
    assert_eq!(result, Ok(None));
    run.complete_result(
        0,
        ticket,
        result.map(|_| ()),
        None,
        CleanupPolicy::RetainFailure,
    )
    .ok()
    .unwrap();
    owner.release_managed_execution(parent, &mut run).unwrap();
    let mut next = begin(&mut owner, parent);
    assert!(owner.owns_shared_child(&child));
    assert!(child.snapshot().cancelled());
    assert!(request.snapshot().cancelled());
    assert_ne!(child.generation(), owner.episode_generation(parent));
    assert!(owner
        .register_shared_child(
            &request,
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![], setup as Callback),
            ()
        )
        .is_err());
    let (fresh, _) = next
        .enqueue_native_child(0, setup as Callback)
        .ok()
        .unwrap();
    assert!(owner.owns_shared_child(&fresh));
    allocate(&mut owner, &mut next, &fresh);
}

#[test]
fn recorded_request_handle_and_inverse_keep_the_same_bound_decision() {
    let (mut owner, parent) = world::<Slot<u64, ()>>();
    let (mut foreign, other) = world::<Slot<u64, ()>>();
    let core: RecordedCore = owner.begin_managed_execution(parent, 7301).unwrap();
    let _other: RecordedCore = foreign.begin_managed_execution(other, 7301).unwrap();
    let mut run = Recorded::new(core);
    let call = owner.admit_recorded_root(parent, &mut run, parent).unwrap();
    let result = owner.call_root(parent, call).ok().unwrap();
    run.complete_root(result).ok().unwrap().unwrap();
    let (handle, _) = run.enqueue_native_child(0, setup as Callback).ok().unwrap();
    assert!(owner.owns_shared_child(&handle));
    assert!(!foreign.owns_shared_child(&handle));
    let result = run.take_child().unwrap().run(|request| {
        let ChildDispatch::Native(request) = request else {
            panic!("native")
        };
        let (payload, request) = request.into_parts();
        assert!(owner.owns_shared_child(&request));
        owner.register_shared_child(
            &request,
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![], payload),
            (),
        )
    });
    let id = run.complete_request(result).ok().unwrap().ok().unwrap();
    assert_eq!(handle.snapshot().identity().unwrap().id(), id);
    let cordis_kernel::cleanup_groups::payload::Dispatch::Other(CleanupDispatch::Host {
        action: ChildCleanup::Native(inverse),
        ..
    }) = run.dispatch(0).ok().unwrap().unwrap()
    else {
        panic!("actual inverse")
    };
    assert!(owner.owns_shared_child(&inverse));
    assert_eq!(
        foreign.retire_shared_child(&inverse),
        Err(Error::InvalidState)
    );
    assert!(!owner.retired(id));
    owner.retire_shared_child(&inverse).unwrap();
    assert_eq!(inverse.snapshot().identity(), handle.snapshot().identity());
    assert!(owner.retired(id));
}

#[test]
fn escaped_child_retains_only_domain_metadata_and_releases_it_with_the_last_clone() {
    let payload = Arc::new("payload".to_owned());
    let weak = Arc::downgrade(&payload);
    let mut owner: NativeDriver<Arc<String>, Arc<String>, ()> = NativeDriver {
        state: NativeRuntime::new(7300),
    };
    let parent = owner
        .register_plugin(
            None,
            &BTreeMap::new(),
            port(1),
            PluginDefinition::new(vec![], vec![], payload.clone()),
            payload.clone(),
        )
        .ok()
        .unwrap();
    let id = owner
        .register_plugin(
            Some(parent),
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![], payload.clone()),
            payload.clone(),
        )
        .ok()
        .unwrap();
    let child = owner.registered_child(id).unwrap();
    let clone = child.clone();
    let journal = owner.execution_journal();
    let journal_weak = Arc::downgrade(journal.runtime_identity());
    drop(journal);
    drop(payload);
    drop(owner);
    assert!(weak.upgrade().is_none());
    assert!(journal_weak.upgrade().is_some());
    assert_eq!(child.snapshot().identity().unwrap().id(), id);
    drop(child);
    assert!(journal_weak.upgrade().is_some());
    drop(clone);
    assert!(journal_weak.upgrade().is_none());
}
