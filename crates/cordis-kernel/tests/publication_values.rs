use cordis_kernel::lifecycle_actions::CleanupOutcome;
use cordis_kernel::lifecycle_state::LifecycleState;
use cordis_kernel::publication::values::{PublicationStore, ValueCell};
use cordis_kernel::publication::{PublicationError, PublicationId};
use cordis_kernel::Port;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

struct Payload {
    name: &'static str,
    drops: Arc<AtomicUsize>,
}
impl Drop for Payload {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}
fn payload(name: &'static str, drops: &Arc<AtomicUsize>) -> Box<Payload> {
    Box::new(Payload {
        name,
        drops: drops.clone(),
    })
}
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn activate(state: &mut LifecycleState, id: usize) {
    let setup = state.begin(id).unwrap();
    state.complete_setup(setup).unwrap();
    state.finish(id).unwrap();
}

#[test]
fn noncopy_payloads_follow_their_own_publication_and_lease() {
    let drops = Arc::new(AtomicUsize::new(0));
    let mut store = PublicationStore::for_domain(31);
    let original = payload("old", &drops);
    let address = std::ptr::from_ref(original.as_ref());
    let old = store
        .publish(4, 1, port(1), original)
        .map_err(|r| r.error)
        .unwrap();
    let lease = store.acquire_for(old, 5, 1).unwrap();
    let replacement = payload("new", &drops);
    let rejected = store.replace(old, 4, 2, replacement).err().unwrap();
    assert_eq!(rejected.error, PublicationError::InvalidState);
    assert_eq!(
        std::ptr::from_ref(store.value(old).unwrap().as_ref()),
        address
    );
    store.revoke(old).unwrap();
    assert_eq!(store.reclaim(old).err(), Some(PublicationError::Relied));
    let new = store
        .publish(6, 1, port(1), rejected.value)
        .map_err(|r| r.error)
        .unwrap();
    assert_ne!(old, new);
    assert_eq!(store.value(old).unwrap().name, "old");
    assert_eq!(store.value(new).unwrap().name, "new");
    assert_eq!(store.registry().leased_slot(lease), Ok(old.0));
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    store.release(lease).unwrap();
    let recovered = store.reclaim(old).unwrap();
    assert_eq!(std::ptr::from_ref(recovered.as_ref()), address);
    assert!(store.value(old).is_none());
    assert_eq!(store.retained_count(), 1);
    assert_eq!(store.reclaim(old).err(), Some(PublicationError::Released));
    drop(recovered);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn replacement_moves_old_value_out_and_rejection_returns_new_input() {
    let drops = Arc::new(AtomicUsize::new(0));
    let mut cell = ValueCell::new(payload("before", &drops));
    let inverse = cell.replace(payload("after", &drops));
    assert_eq!(inverse.name, "before");
    assert_eq!(cell.get().name, "after");
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    let displaced = cell.replace(inverse);
    assert_eq!(cell.get().name, "before");
    assert_eq!(displaced.name, "after");
    let mut store = PublicationStore::for_domain(32);
    let id = store
        .publish(7, 1, port(1), displaced)
        .map_err(|r| r.error)
        .unwrap();
    let rejected = store
        .publish(8, 1, port(1), payload("conflict", &drops))
        .err()
        .unwrap();
    assert_eq!(rejected.error, PublicationError::Conflict);
    let previous = store
        .replace(id, 7, 1, rejected.value)
        .map_err(|r| r.error)
        .unwrap();
    assert_eq!(previous.name, "after");
    assert_eq!(store.value(id).unwrap().name, "conflict");
    assert_eq!(drops.load(Ordering::SeqCst), 0);
}

#[test]
fn actual_values_are_released_only_with_complete_manifest_and_accepted_cleanup() {
    let mut state = LifecycleState::new(33);
    let mut store = PublicationStore::for_domain(33);
    let provider = state.insert(None, vec![], vec![port(1)]).unwrap();
    activate(&mut state, provider);
    let publication = store
        .publish(provider, 1, port(1), String::from("provider-value"))
        .map_err(|r| r.error)
        .unwrap();
    let consumer = state.insert(None, vec![port(1)], vec![port(2)]).unwrap();
    activate(&mut state, consumer);
    let lease = store.acquire_for(publication, consumer, 1).unwrap();
    let own = store
        .publish(consumer, 1, port(2), String::from("consumer-value"))
        .map_err(|r| r.error)
        .unwrap();
    for id in [provider, consumer] {
        state.retire(id).unwrap();
        state.leave(id).unwrap();
    }
    store.revoke(publication).unwrap();
    store.revoke(own).unwrap();
    let failed = state.begin_cleanup(consumer).unwrap();
    state
        .complete_cleanup(failed, CleanupOutcome::Failed)
        .unwrap();
    assert!(store
        .finish_resources(&mut state, consumer, false, &[lease], &[own])
        .is_err());
    assert!(state.begin_cleanup(provider).is_err());
    let retry = state.retry_cleanup(consumer).unwrap();
    assert!(state
        .complete_cleanup(failed, CleanupOutcome::Succeeded)
        .is_err());
    state
        .complete_cleanup(retry, CleanupOutcome::Succeeded)
        .unwrap();
    assert!(store
        .finish_resources(&mut state, consumer, false, &[], &[own])
        .is_err());
    assert!(store
        .finish_resources(&mut state, consumer, false, &[lease], &[])
        .is_err());
    assert!(store
        .finish_resources(
            &mut state,
            consumer,
            false,
            &[lease],
            &[own, PublicationId(99)]
        )
        .is_err());
    assert_eq!(store.value(own).map(String::as_str), Some("consumer-value"));
    assert_eq!(store.registry().leased_slot(lease), Ok(publication.0));
    assert!(!state.kernel().committed(consumer).is_empty());
    let released = store
        .finish_resources(&mut state, consumer, false, &[lease], &[own])
        .unwrap();
    assert_eq!(released.len(), 1);
    assert_eq!(released[0].publication, own);
    assert_eq!(released[0].value, "consumer-value");
    assert!(store.value(own).is_none());
    assert!(state.kernel().committed(consumer).is_empty());
    let cleanup = state.begin_cleanup(provider).unwrap();
    state
        .complete_cleanup(cleanup, CleanupOutcome::Succeeded)
        .unwrap();
    let released = store
        .finish_resources(&mut state, provider, false, &[], &[publication])
        .unwrap();
    assert_eq!(released[0].value, "provider-value");
    assert_eq!(store.retained_count(), 0);
}

#[test]
fn releasing_one_publication_does_not_release_an_aliased_js_handle() {
    let mut store = PublicationStore::for_domain(34);
    let a = store
        .publish(1, 1, port(1), 100u64)
        .map_err(|r| r.error)
        .unwrap();
    let b = store
        .publish(2, 1, port(2), 100u64)
        .map_err(|r| r.error)
        .unwrap();
    store.revoke(a).unwrap();
    assert_eq!(store.reclaim(a), Ok(100));
    assert!(store.contains_handle(100));
    store.revoke(b).unwrap();
    assert_eq!(store.reclaim(b), Ok(100));
    assert!(!store.contains_handle(100));
}

#[test]
fn managed_publication_and_replacement_check_actual_owner_generation_and_domain() {
    let mut state = LifecycleState::new(35);
    let owner = state.insert(None, vec![], vec![]).unwrap();
    let mut foreign = PublicationStore::for_domain(36);
    let rejected = foreign
        .publish_checked(&state, owner, 0, port(1), String::from("foreign"))
        .err()
        .unwrap();
    assert_eq!(rejected.error, PublicationError::InvalidState);
    assert_eq!(rejected.value, "foreign");
    let mut store = PublicationStore::for_domain(35);
    activate(&mut state, owner);
    let stale = store
        .publish_checked(&state, owner, 0, port(1), String::from("stale"))
        .err()
        .unwrap();
    assert_eq!(stale.error, PublicationError::InvalidState);
    let id = store
        .publish_checked(&state, owner, 1, port(1), stale.value)
        .map_err(|r| r.error)
        .unwrap();
    let other = store
        .publish_checked(&state, owner, 1, port(2), String::from("second"))
        .map_err(|r| r.error)
        .unwrap();
    let lease = store.acquire_for(other, 100, 2).unwrap();
    let (selected, value) = store.leased_value(lease).unwrap();
    assert_eq!(selected, other);
    assert_eq!(value, "second");
    store.revoke(other).unwrap();
    assert_eq!(store.leased_value(lease).unwrap().1, "second");
    state.retire(owner).unwrap();
    let rejected = store
        .replace_checked(&state, id, owner, 1, String::from("after-retire"))
        .err()
        .unwrap();
    assert_eq!(rejected.error, PublicationError::InvalidState);
    assert_eq!(rejected.value, "after-retire");
    assert_eq!(store.value(id).unwrap(), "stale");
    store.release(lease).unwrap();
    assert_eq!(
        store.leased_value(lease).err(),
        Some(PublicationError::Released)
    );
}
