use cordis_kernel::cleanup_groups::CleanupGroups;
use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
use cordis_kernel::lifecycle_actions::CleanupOutcome;
use cordis_kernel::lifecycle_state::registration::{PluginDefinition, RegisteredPlugin};
use cordis_kernel::lifecycle_state::services::{NativeEpisode, NativeServices, NativeValueError};
use cordis_kernel::lifecycle_state::LifecycleState;
use cordis_kernel::setup_work::SetupWork;
use cordis_kernel::{Error, Phase, Port};
use std::collections::BTreeMap;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

type Work = SetupWork<String, String>;
type Groups = CleanupGroups<String>;
fn port(key: u64, realm: u64) -> Port {
    Port { key, realm }
}
fn register(
    state: &mut LifecycleState,
    dependencies: Vec<u64>,
    provisions: Vec<u64>,
    realm: u64,
) -> RegisteredPlugin<()> {
    let mut realms = BTreeMap::new();
    for key in dependencies.iter().chain(&provisions) {
        realms.insert(*key, realm);
    }
    state
        .register_plugin(
            None,
            &realms,
            port(10_000 + state.kernel().identity_slots() as u64, 0),
            PluginDefinition::new(dependencies, provisions, ()),
        )
        .ok()
        .unwrap()
}
fn begin<T>(
    state: &mut LifecycleState,
    store: &NativeServices<T>,
    registration: &RegisteredPlugin<()>,
    domain: u64,
) -> (Work, Groups, NativeEpisode<T>) {
    state
        .begin_native_execution(store, registration, domain)
        .unwrap()
}
fn root(work: &mut Work) {
    let item = work.issue_root("actual root".to_owned()).ok().unwrap();
    let receipt = item.run(|_| Ok::<(), String>(()));
    work.complete_root(receipt).ok().unwrap().unwrap();
}
fn withdraw(state: &mut LifecycleState, id: usize, work: &mut Work, groups: &Groups) {
    state.leave(id).unwrap();
    work.withdraw();
    state.settle_execution(id, work, groups).unwrap();
    state.begin_cleanup(id).unwrap();
}

#[test]
fn finish_publishes_actual_complete_slots_in_the_declared_realm() {
    let mut state = LifecycleState::new(500);
    let mut store = NativeServices::new(500);
    let recipe = register(&mut state, vec![], vec![1, 2], 7);
    let id = recipe.id();
    let (mut work, groups, mut values) = begin(&mut state, &store, &recipe, 501);
    root(&mut work);
    let actual = Arc::new("first payload".to_owned());
    let rejected = values.provide(port(1, 0), actual.clone()).unwrap_err();
    assert_eq!(rejected.0, NativeValueError::Undeclared);
    assert!(Arc::ptr_eq(&rejected.1, &actual));
    values.provide(port(1, 7), actual.clone()).unwrap();
    assert!(Arc::ptr_eq(values.read(port(1, 7)).unwrap().1, &actual));
    assert_eq!(
        values.read(port(2, 7)).unwrap_err().reason,
        NativeValueError::Missing
    );
    assert_eq!(
        state.finish_native_execution(id, &mut store, &values, &work, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(state.kernel().phase(id), Some(Phase::Loading));
    assert!(!store.has_publications());
    assert!(store.visible(&state, port(1, 7)).is_none());
    let duplicate = Arc::new("duplicate".to_owned());
    let rejected = values.provide(port(1, 7), duplicate.clone()).unwrap_err();
    assert_eq!(rejected.0, NativeValueError::Duplicate);
    assert!(Arc::ptr_eq(&rejected.1, &duplicate));
    values
        .provide(port(2, 7), Arc::new("second".into()))
        .unwrap();
    state
        .finish_native_execution(id, &mut store, &values, &work, &groups)
        .unwrap();
    assert_eq!(store.value_count(), 2);
    assert!(Arc::ptr_eq(
        store.visible(&state, port(1, 7)).unwrap(),
        &actual
    ));
    assert!(store.visible(&state, port(1, 0)).is_none());
    assert_eq!(
        values.read(port(9, 7)).unwrap_err().reason,
        NativeValueError::Undeclared
    );
}

#[test]
fn committed_snapshot_retains_exact_slots_and_excludes_unrelated_providers() {
    let mut state = LifecycleState::new(510);
    let mut store = NativeServices::new(510);
    let provider = register(&mut state, vec![], vec![1], 7);
    let unrelated = register(&mut state, vec![], vec![2], 7);
    let actual = Arc::new("committed".to_owned());
    let other = Arc::new("unrelated".to_owned());
    let (mut pw, pg, mut pv) = begin(&mut state, &store, &provider, 511);
    pv.provide(port(1, 7), actual.clone()).unwrap();
    root(&mut pw);
    state
        .finish_native_execution(provider.id(), &mut store, &pv, &pw, &pg)
        .unwrap();
    let (mut uw, ug, mut uv) = begin(&mut state, &store, &unrelated, 512);
    uv.provide(port(2, 7), other.clone()).unwrap();
    root(&mut uw);
    state
        .finish_native_execution(unrelated.id(), &mut store, &uv, &uw, &ug)
        .unwrap();
    let consumer = register(&mut state, vec![1], vec![], 7);
    let (mut cw, mut cg, mut cv) = begin(&mut state, &store, &consumer, 513);
    assert_eq!(Arc::strong_count(&actual), 4); // caller, episode, publication, one committed import
    assert_eq!(Arc::strong_count(&other), 3);
    let (selected, read) = cv.read(port(1, 7)).unwrap();
    assert_eq!(selected, provider.id());
    assert!(Arc::ptr_eq(read, &actual));
    assert_eq!(
        cv.read(port(2, 7)).unwrap_err().reason,
        NativeValueError::Undeclared
    );
    root(&mut cw);
    state
        .finish_native_execution(consumer.id(), &mut store, &cv, &cw, &cg)
        .unwrap();
    state.leave(provider.id()).unwrap();
    assert!(store.visible(&state, port(1, 7)).is_none());
    assert!(Arc::ptr_eq(cv.read(port(1, 7)).unwrap().1, &actual));
    assert_eq!(state.begin_cleanup(provider.id()), Err(Error::Relied));
    withdraw(&mut state, consumer.id(), &mut cw, &cg);
    let (outcome, released) = state
        .release_native_execution(consumer.id(), &mut store, &mut cv, &mut cw, &mut cg)
        .unwrap();
    assert_eq!(outcome, CleanupOutcome::Succeeded);
    assert_eq!(released.imports.len(), 1);
    assert!(cv.is_closed());
    assert_eq!(
        cv.read(port(1, 7)).unwrap_err().reason,
        NativeValueError::Closed
    );
    assert_eq!(Arc::strong_count(&actual), 4);
    drop(released);
    assert_eq!(Arc::strong_count(&actual), 3);
    assert!(store.visible(&state, port(2, 7)).is_some());
}

#[test]
fn native_begin_rejects_duplicate_foreign_and_wrong_registered_episodes() {
    let mut a = LifecycleState::new(520);
    let mut b = LifecycleState::new(521);
    let mut store: NativeServices<String> = NativeServices::new(520);
    let foreign = NativeServices::<String>::new(521);
    let recipe = register(&mut a, vec![], vec![], 0);
    let other = register(&mut a, vec![], vec![], 0);
    let foreign_recipe = register(&mut b, vec![], vec![], 0);
    let (mut work, groups, values) = begin(&mut a, &store, &recipe, 522);
    let repeated: Result<(Work, Groups, NativeEpisode<String>), _> =
        a.begin_native_execution(&store, &recipe, 523);
    assert!(repeated.is_err());
    let foreign_store: Result<(Work, Groups, NativeEpisode<String>), _> =
        a.begin_native_execution(&foreign, &other, 524);
    assert!(foreign_store.is_err());
    let foreign_registration: Result<(Work, Groups, NativeEpisode<String>), _> =
        a.begin_native_execution(&store, &foreign_recipe, 525);
    assert!(foreign_registration.is_err());
    let _foreign_work: (Work, Groups) = b.begin_execution(foreign_recipe.id(), 526).unwrap();
    root(&mut work);
    assert_eq!(
        b.finish_native_execution(recipe.id(), &mut store, &values, &work, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(
        a.finish_native_execution(other.id(), &mut store, &values, &work, &groups),
        Err(Error::InvalidState)
    );
    assert!(!store.has_publications());
    a.finish_native_execution(recipe.id(), &mut store, &values, &work, &groups)
        .unwrap();
}

#[test]
fn old_closed_values_cannot_finish_or_release_a_later_episode() {
    let mut state = LifecycleState::new(530);
    let mut store = NativeServices::new(530);
    let recipe = register(&mut state, vec![], vec![1], 0);
    let id = recipe.id();
    let (mut w, mut g, mut values) = begin(&mut state, &store, &recipe, 531);
    values
        .provide(port(1, 0), Arc::new("old".to_owned()))
        .unwrap();
    root(&mut w);
    state
        .finish_native_execution(id, &mut store, &values, &w, &g)
        .unwrap();
    withdraw(&mut state, id, &mut w, &g);
    drop(
        state
            .release_native_execution(id, &mut store, &mut values, &mut w, &mut g)
            .unwrap(),
    );
    let (mut next_w, mut next_g, mut next_values) = begin(&mut state, &store, &recipe, 532);
    let fresh = Arc::new("fresh".to_owned());
    next_values.provide(port(1, 0), fresh.clone()).unwrap();
    root(&mut next_w);
    assert_eq!(
        state.finish_native_execution(id, &mut store, &values, &next_w, &next_g),
        Err(Error::InvalidState)
    );
    state
        .finish_native_execution(id, &mut store, &next_values, &next_w, &next_g)
        .unwrap();
    assert!(state
        .release_native_execution(id, &mut store, &mut values, &mut next_w, &mut next_g)
        .is_err());
    assert!(state
        .release_native_execution(id, &mut store, &mut values, &mut w, &mut g)
        .is_err());
    assert_eq!(
        values.provide(port(1, 0), fresh.clone()).unwrap_err().0,
        NativeValueError::Closed
    );
    assert!(Arc::ptr_eq(
        store.visible(&state, port(1, 0)).unwrap(),
        &fresh
    ));
}

#[test]
fn failed_cleanup_keeps_actual_values_until_a_fresh_successful_retry() {
    let mut state = LifecycleState::new(540);
    let mut store = NativeServices::new(540);
    let recipe = register(&mut state, vec![], vec![1], 0);
    let id = recipe.id();
    let (mut work, mut groups, mut values) = begin(&mut state, &store, &recipe, 541);
    let actual = Arc::new("keep me".to_owned());
    values.provide(port(1, 0), actual.clone()).unwrap();
    groups.register(0, "cleanup".into()).ok().unwrap();
    root(&mut work);
    state
        .finish_native_execution(id, &mut store, &values, &work, &groups)
        .unwrap();
    withdraw(&mut state, id, &mut work, &groups);
    let (old_ticket, payload) = groups.pop(0).unwrap().unwrap();
    groups
        .complete_result(
            0,
            old_ticket,
            Err::<(), _>("failure"),
            Some(payload),
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    state.fail_execution(id, &work, &groups).unwrap();
    assert!(state
        .release_native_execution(id, &mut store, &mut values, &mut work, &mut groups)
        .is_err());
    assert!(!values.is_closed());
    assert_eq!(store.value_count(), 1);
    assert!(Arc::ptr_eq(values.read(port(1, 0)).unwrap().1, &actual));
    state.retry_execution(id, &work, &mut groups).unwrap();
    let (ticket, _) = groups.pop(0).unwrap().unwrap();
    assert_ne!(ticket, old_ticket);
    assert!(groups
        .complete_result(
            0,
            old_ticket,
            Ok::<(), &str>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
    groups
        .complete_result(
            0,
            ticket,
            Ok::<(), &str>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    let (_, released) = state
        .release_native_execution(id, &mut store, &mut values, &mut work, &mut groups)
        .unwrap();
    assert!(!store.has_publications());
    assert!(values.is_closed());
    assert_eq!(Arc::strong_count(&actual), 3);
    drop(released);
    assert_eq!(Arc::strong_count(&actual), 1);
}

struct DropCount(Arc<AtomicUsize>);
impl Drop for DropCount {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}
#[test]
fn cancelled_partial_setup_transfers_noncopy_payloads_without_publishing_or_dropping_them() {
    let mut state = LifecycleState::new(550);
    let mut store = NativeServices::new(550);
    let recipe = register(&mut state, vec![], vec![1, 2], 0);
    let id = recipe.id();
    let (mut work, mut groups, mut values) = begin(&mut state, &store, &recipe, 551);
    let drops = Arc::new(AtomicUsize::new(0));
    assert!(values
        .provide(port(1, 0), Arc::new(DropCount(drops.clone())))
        .is_ok());
    root(&mut work);
    withdraw(&mut state, id, &mut work, &groups);
    let (_, released) = state
        .release_native_execution(id, &mut store, &mut values, &mut work, &mut groups)
        .unwrap();
    assert!(released.published.is_none());
    assert_eq!(released.owned.len(), 1);
    assert!(!store.has_publications());
    assert!(values.is_closed());
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    drop(released);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn stale_registry_generation_is_neither_visible_nor_imported() {
    let mut state = LifecycleState::new(560);
    let mut store = NativeServices::new(560);
    let provider = register(&mut state, vec![], vec![1], 0);
    let id = provider.id();
    let (mut w, mut g, mut v) = begin(&mut state, &store, &provider, 561);
    v.provide(port(1, 0), Arc::new("obsolete".to_owned()))
        .unwrap();
    root(&mut w);
    state
        .finish_native_execution(id, &mut store, &v, &w, &g)
        .unwrap();
    withdraw(&mut state, id, &mut w, &g);
    // Deliberately use the lower-level control API, leaving a stale registry.
    // Managed observation must still refuse to attach that old slot to Begin.
    state.release_execution(id, &mut w, &mut g).unwrap();
    let (mut nw, ng): (Work, Groups) = state.begin_execution(id, 562).unwrap();
    root(&mut nw);
    state.finish_execution(id, &nw, &ng).unwrap();
    assert_eq!(state.kernel().phase(id), Some(Phase::Active));
    assert!(store.visible(&state, port(1, 0)).is_none());
    let consumer = register(&mut state, vec![1], vec![], 0);
    let (_, _, cv) = begin(&mut state, &store, &consumer, 563);
    let error = cv.read(port(1, 0)).unwrap_err();
    assert_eq!(error.reason, NativeValueError::Missing);
    assert_eq!(error.provider, Some(id));
}

#[test]
fn equal_lifecycle_tickets_cannot_substitute_a_different_work_domain() {
    // Raw embeddings can deliberately reuse lifecycle domain numbers. Even
    // then, a value owner must use the work domain captured by its own Begin.
    let mut actual = LifecycleState::new(580);
    let mut other = LifecycleState::new(580);
    let mut store = NativeServices::new(580);
    let other_store = NativeServices::<String>::new(580);
    let recipe = register(&mut actual, vec![], vec![1], 0);
    let other_recipe = register(&mut other, vec![], vec![1], 0);
    let (mut work, mut groups, mut values) = begin(&mut actual, &store, &recipe, 581);
    let (mut wrong_work, mut wrong_groups, _) = begin(&mut other, &other_store, &other_recipe, 582);
    assert_eq!(work.lifecycle_ticket(), wrong_work.lifecycle_ticket());
    assert_eq!(values.cleanup_domain(), work.domain());
    assert_ne!(values.cleanup_domain(), wrong_work.domain());
    root(&mut work);
    root(&mut wrong_work);
    let value = Arc::new("belongs to the first Begin".to_owned());
    values.provide(port(1, 0), value.clone()).unwrap();
    assert_eq!(
        actual.finish_native_execution(
            recipe.id(),
            &mut store,
            &values,
            &wrong_work,
            &wrong_groups
        ),
        Err(Error::InvalidState)
    );
    assert_eq!(actual.kernel().phase(recipe.id()), Some(Phase::Loading));
    assert_eq!(store.value_count(), 0);
    actual
        .finish_native_execution(recipe.id(), &mut store, &values, &work, &groups)
        .unwrap();
    withdraw(&mut actual, recipe.id(), &mut work, &groups);
    wrong_work.withdraw();
    assert!(matches!(
        actual.release_native_execution(
            recipe.id(),
            &mut store,
            &mut values,
            &mut wrong_work,
            &mut wrong_groups
        ),
        Err(Error::InvalidState)
    ));
    assert_eq!(actual.kernel().phase(recipe.id()), Some(Phase::Unloading));
    assert!(!values.is_closed());
    assert!(Arc::ptr_eq(values.own(port(1, 0)).unwrap(), &value));
    assert_eq!(store.value_count(), 1);
    actual
        .release_native_execution(recipe.id(), &mut store, &mut values, &mut work, &mut groups)
        .unwrap();
    assert!(values.is_closed());
    assert_eq!(store.value_count(), 0);
}
