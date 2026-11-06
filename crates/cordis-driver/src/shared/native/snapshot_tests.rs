//! Actual Native snapshots across colliding domains, cleanup and owner lifetime.
use super::test_support::{activate, fail, world, Core, ManagedCore};
use super::*;
use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
use cordis_kernel::Phase;

#[test]
fn foreign_historical_cut_is_rejected_with_identical_numeric_selectors() {
    let (mut a, aid) = world::<()>();
    let (mut b, bid) = world::<()>();
    let before = a.publication_snapshot();
    let mut ac = a.poll_control::<()>(aid).unwrap();
    let mut bc = b.poll_control::<()>(bid).unwrap();
    let ar: Core<(), ()> = activate(&mut a, aid, &mut ac);
    let br: Core<(), ()> = activate(&mut b, bid, &mut bc);
    assert_eq!(a.domain(), b.domain());
    assert_eq!(ar.lifecycle_ticket(), br.lifecycle_ticket());
    let pending = b.pending_action(bid);
    assert!(b.recovery_snapshot(&before).is_none());
    assert_eq!(b.pending_action(bid), pending);
    assert_eq!(b.phase(bid), Some(Phase::Active));
    assert!(a.recovery_snapshot(&before).is_some());
    let moved = a;
    assert!(moved.owns_snapshot(&before));
    assert!(moved.recovery_snapshot(&before).is_some());
    assert!(b.recovery_snapshot(&b.publication_snapshot()).is_some());
}

#[test]
fn historical_observation_survives_failure_retry_unload_and_a_new_episode() {
    let (mut owner, id) = world::<()>();
    let before = owner.publication_snapshot();
    let mut control = owner.poll_control::<&'static str>(id).unwrap();
    let mut run: Core<(), ()> = activate(&mut owner, id, &mut control);
    let origin = run.lifecycle_ticket();
    fail(&mut owner, id, &mut run, &mut control, ());
    let pending = owner.pending_action(id);
    let failed = owner.recovery_snapshot(&before).unwrap();
    assert!(owner.owns_snapshot(&failed.cut));
    assert!(run.has_failed());
    assert_eq!(control.cleanup_failure(), Some(&"retained"));
    assert_eq!(owner.pending_action(id), pending);
    assert_eq!(owner.phase(id), Some(Phase::Unloading));
    assert!(owner.release_managed_execution(id, &mut run).is_err());
    owner
        .retry_controlled_execution(id, &mut run, &mut control)
        .unwrap();
    let (ticket, ()) = run.pop(0).unwrap().unwrap();
    run.complete_result(
        0,
        ticket,
        Ok::<_, &str>(()),
        None,
        CleanupPolicy::RetainFailure,
    )
    .ok()
    .unwrap();
    owner
        .release_controlled_execution(id, &mut run, &mut control)
        .unwrap();
    assert_eq!(owner.phase(id), Some(Phase::Inactive));
    assert!(owner.recovery_snapshot(&before).is_some());
    assert!(owner.recovery_snapshot(&failed.cut).is_some());
    let next: Core<(), ()> = activate(&mut owner, id, &mut control);
    assert_ne!(next.lifecycle_ticket(), origin);
    assert!(owner.recovery_snapshot(&before).is_some());
    assert!(owner.recovery_snapshot(&failed.cut).is_some());
    assert_eq!(owner.phase(id), Some(Phase::Active));
}

#[test]
fn configuration_cut_borrows_its_native_source_without_renewing_it() {
    let (mut owner, id) = world::<()>();
    let (other, _) = world::<()>();
    let configuration = owner.configuration::<(), (), (), (), u64, ()>(());
    let checkpoint = owner.configuration_snapshot(&configuration).unwrap();
    let cut = checkpoint.native_snapshot();
    assert!(owner.owns_snapshot(cut));
    assert!(other.recovery_snapshot(cut).is_none());
    let native = cut.native_identity();
    let references = Arc::strong_count(native);
    assert!(std::ptr::eq(cut, checkpoint.native_snapshot()));
    assert_eq!(Arc::strong_count(native), references);
    let revision = owner.registration(id).unwrap().revision();
    owner
        .replace(id, (|_| Ok(())) as super::test_support::Callback)
        .ok()
        .unwrap();
    assert!(owner.registration(id).unwrap().revision() > revision);
    assert!(owner.recovery_snapshot(cut).is_some());
    assert!(other.recovery_snapshot(cut).is_none());
}

#[test]
fn all_specialized_native_factories_retain_the_same_actual_allocation() {
    let (mut owner, id) = world::<Slot<u64, ()>>();
    let (other, _) = world::<Slot<u64, ()>>();
    let mut control = owner.poll_control::<()>(id).unwrap();
    let run: ManagedCore = activate(&mut owner, id, &mut control);
    let scope = run.root_scope().unwrap();
    let cuts = [
        owner.publication_snapshot(),
        owner.state.episode_snapshot(id, &run).unwrap(),
        owner.state.service_snapshot(),
        owner.state.service_episode_snapshot(id, &run).unwrap(),
        owner
            .state
            .controlled_service_episode_snapshot(id, &run, &control)
            .unwrap(),
        owner
            .state
            .scoped_service_episode_snapshot(id, &run, &control, &scope)
            .unwrap(),
        owner.state.payload_service_snapshot(),
        owner
            .state
            .scoped_payload_service_episode_snapshot(id, &run, &control, &scope)
            .unwrap(),
    ];
    for cut in cuts {
        assert!(Arc::ptr_eq(
            cut.native_identity(),
            owner.state.poll_control_identity()
        ));
        assert!(owner.recovery_snapshot(&cut).is_some());
        assert!(other.recovery_snapshot(&cut).is_none());
    }
}

#[test]
fn snapshots_keep_only_metadata_and_projection_releases_native_identity() {
    type Recipe = Box<dyn FnMut(usize) -> Result<(), &'static str>>;
    let payload = Arc::new("recipe, host and published payload".to_owned());
    let weak = Arc::downgrade(&payload);
    let captured = payload.clone();
    let recipe: Recipe = Box::new(move |_| {
        let _ = &captured;
        Ok(())
    });
    let mut owner: NativeDriver<Recipe, Arc<String>, String> = NativeDriver {
        state: NativeRuntime::new(7300),
    };
    let port = Port { key: 1, realm: 0 };
    let id = owner
        .register_plugin(
            None,
            &BTreeMap::new(),
            Port { key: 101, realm: 0 },
            PluginDefinition::new(vec![], vec![port.key], recipe),
            payload.clone(),
        )
        .ok()
        .unwrap();
    let mut run: Core<String, ()> = owner.begin_managed_execution(id, 7301).unwrap();
    let call = owner.admit_managed_root(id, &mut run, id).unwrap();
    let result = owner.call_root(id, call).ok().unwrap();
    run.complete_root(result).ok().unwrap().unwrap();
    run.provide(port, payload.clone()).ok().unwrap();
    owner.finish_managed_execution(id, &mut run).unwrap();
    let snapshot = owner.publication_snapshot();
    let native = Arc::downgrade(snapshot.native_identity());
    let journal = owner.execution_journal();
    let domain = Arc::downgrade(journal.runtime_identity());
    drop(journal);
    drop(run);
    drop(payload);
    drop(owner);
    assert!(weak.upgrade().is_none());
    assert!(native.upgrade().is_some());
    assert!(domain.upgrade().is_some());
    let projection = snapshot.into_joint();
    assert!(native.upgrade().is_none());
    assert!(domain.upgrade().is_some());
    drop(projection.refresh());
    drop(projection);
    assert!(domain.upgrade().is_none());
}
