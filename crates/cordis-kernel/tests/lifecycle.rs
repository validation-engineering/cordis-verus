use cordis_kernel::{Binding, Error, Kernel, Phase, Port};

fn port(key: u64, realm: u64) -> Port {
    Port { key, realm }
}

fn activate(kernel: &mut Kernel, id: usize) {
    kernel.begin(id).unwrap();
    kernel.finish(id).unwrap();
}

fn deactivate(kernel: &mut Kernel, id: usize) {
    kernel.leave(id).unwrap();
    kernel.begin_cleanup(id).unwrap();
    kernel.finish_cleanup(id).unwrap();
}

fn pair() -> (Kernel, usize, usize, Port) {
    let mut kernel = Kernel::new();
    let service = port(7, 0);
    let provider = kernel.insert(None, vec![], vec![service]).unwrap();
    let consumer = kernel.insert(None, vec![service], vec![]).unwrap();
    (kernel, provider, consumer, service)
}

#[test]
fn retired_active_provider_remains_visible_until_it_leaves_active() {
    let (mut kernel, provider, consumer, service) = pair();
    activate(&mut kernel, provider);
    kernel.retire(provider).unwrap();

    assert!(kernel.retired(provider));
    assert_eq!(kernel.phase(provider), Some(Phase::Active));
    assert_eq!(kernel.resolve(service), Some(provider));
    assert_eq!(kernel.target(provider), None);
    activate(&mut kernel, consumer);
    assert_eq!(kernel.committed(consumer)[0].provider, provider);

    kernel.leave(provider).unwrap();
    assert_eq!(kernel.resolve(service), None);
    assert_eq!(kernel.phase(consumer), Some(Phase::Active));
    assert_eq!(kernel.target(consumer), None);
    assert_eq!(kernel.committed(consumer)[0].provider, provider);
}

#[test]
fn active_consumer_may_temporarily_disagree_with_its_current_target() {
    let (mut kernel, provider, consumer, _) = pair();
    activate(&mut kernel, provider);
    activate(&mut kernel, consumer);
    let bindings = kernel.committed(consumer);
    kernel.leave(provider).unwrap();

    assert_eq!(kernel.phase(consumer), Some(Phase::Active));
    assert_eq!(kernel.target(consumer), None);
    assert_eq!(kernel.committed(consumer), bindings);
    assert_eq!(kernel.begin_cleanup(provider), Err(Error::Relied));
    assert!(!kernel.cleanup_started(provider));
}

#[test]
fn loading_bindings_pin_provider_and_finish_rechecks_the_target() {
    let (mut kernel, provider, consumer, _) = pair();
    activate(&mut kernel, provider);
    kernel.begin(consumer).unwrap();
    let bindings = kernel.committed(consumer);
    assert_eq!(bindings[0].provider, provider);
    kernel.leave(provider).unwrap();

    assert_eq!(kernel.begin_cleanup(provider), Err(Error::Relied));
    assert_eq!(kernel.finish(consumer), Err(Error::Changed));
    assert_eq!(kernel.phase(consumer), Some(Phase::Loading));
    assert_eq!(kernel.committed(consumer), bindings);

    deactivate(&mut kernel, consumer);
    kernel.begin_cleanup(provider).unwrap();
    kernel.finish_cleanup(provider).unwrap();
    assert_eq!(kernel.phase(provider), Some(Phase::Inactive));
}

#[test]
fn provider_cleanup_waits_until_consumer_cleanup_has_finished() {
    let (mut kernel, provider, consumer, _) = pair();
    activate(&mut kernel, provider);
    activate(&mut kernel, consumer);
    kernel.leave(provider).unwrap();
    kernel.leave(consumer).unwrap();
    kernel.begin_cleanup(consumer).unwrap();

    assert_eq!(kernel.begin_cleanup(provider), Err(Error::Relied));
    assert!(!kernel.committed(consumer).is_empty());
    kernel.finish_cleanup(consumer).unwrap();
    assert!(kernel.committed(consumer).is_empty());
    kernel.begin_cleanup(provider).unwrap();
    assert!(kernel.cleanup_started(provider));
    kernel.finish_cleanup(provider).unwrap();
}

#[test]
fn registry_removal_requires_retirement_inactivity_and_no_children() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    let child = kernel.insert(Some(parent), vec![], vec![]).unwrap();
    assert_eq!(kernel.remove(parent), Err(Error::InvalidState));
    kernel.retire(parent).unwrap();
    assert_eq!(kernel.remove(parent), Err(Error::Children));
    // Raw O-Insert requires an existing parent, including a retired one. This
    // permits a previously admitted child stage to land after retirement.
    let late_child = kernel.insert(Some(parent), vec![], vec![]).unwrap();
    assert_eq!(kernel.children(parent), vec![child, late_child]);

    activate(&mut kernel, child);
    kernel.retire(child).unwrap();
    assert_eq!(kernel.remove(child), Err(Error::InvalidState));
    deactivate(&mut kernel, child);
    kernel.remove(child).unwrap();
    assert_eq!(kernel.remove(parent), Err(Error::Children));
    kernel.retire(late_child).unwrap();
    kernel.remove(late_child).unwrap();
    kernel.remove(parent).unwrap();
    assert!(kernel.ids().is_empty());
}

#[test]
fn replacing_an_identical_port_changes_binding_identity() {
    let (mut kernel, old_provider, consumer, service) = pair();
    activate(&mut kernel, old_provider);
    activate(&mut kernel, consumer);
    let old_binding = kernel.committed(consumer)[0];
    deactivate(&mut kernel, consumer);
    kernel.retire(old_provider).unwrap();
    deactivate(&mut kernel, old_provider);
    kernel.remove(old_provider).unwrap();

    // Host values can be equal: the kernel binds to fiber identity, not values.
    let new_provider = kernel.insert(None, vec![], vec![service]).unwrap();
    assert_ne!(new_provider, old_provider);
    activate(&mut kernel, new_provider);
    activate(&mut kernel, consumer);
    let new_binding = kernel.committed(consumer)[0];
    assert_eq!(new_binding.key, old_binding.key);
    assert_eq!(new_binding.realm, old_binding.realm);
    assert_ne!(new_binding, old_binding);
    assert_eq!(new_binding.provider, new_provider);
}

#[test]
fn realm_is_part_of_service_identity_and_conflict_detection() {
    let mut kernel = Kernel::new();
    let global = port(7, 0);
    let isolated = port(7, 1);
    let provider = kernel.insert(None, vec![], vec![global]).unwrap();
    let scoped = kernel.insert(None, vec![], vec![isolated]).unwrap();
    let consumer = kernel.insert(None, vec![isolated], vec![]).unwrap();
    activate(&mut kernel, provider);
    assert_eq!(kernel.resolve(global), Some(provider));
    assert_eq!(kernel.resolve(isolated), None);
    assert_eq!(kernel.begin(consumer), Err(Error::MissingDependency));
    assert_eq!(
        kernel.insert(None, vec![], vec![global]),
        Err(Error::Conflict)
    );
    activate(&mut kernel, scoped);
    activate(&mut kernel, consumer);
    assert_eq!(kernel.committed(consumer)[0].provider, scoped);
}

type Snapshot = Vec<(
    usize,
    Option<Phase>,
    bool,
    bool,
    Vec<Binding>,
    Option<Vec<Binding>>,
    Vec<usize>,
)>;

fn snapshot(kernel: &Kernel, ids: &[usize]) -> Snapshot {
    ids.iter()
        .map(|&id| {
            (
                id,
                kernel.phase(id),
                kernel.retired(id),
                kernel.cleanup_started(id),
                kernel.committed(id),
                kernel.target(id),
                kernel.children(id),
            )
        })
        .collect()
}

#[test]
fn repeated_cleanup_or_removal_fails_without_mutating_other_fibers() {
    let (mut kernel, provider, consumer, _) = pair();
    activate(&mut kernel, provider);
    activate(&mut kernel, consumer);
    deactivate(&mut kernel, consumer);
    let before = snapshot(&kernel, &[provider, consumer]);
    assert_eq!(kernel.finish_cleanup(consumer), Err(Error::InvalidState));
    assert_eq!(kernel.begin_cleanup(consumer), Err(Error::InvalidState));
    assert_eq!(kernel.leave(consumer), Err(Error::InvalidState));
    assert_eq!(snapshot(&kernel, &[provider, consumer]), before);
    kernel.retire(consumer).unwrap();
    kernel.remove(consumer).unwrap();
    let before = snapshot(&kernel, &[provider, consumer]);
    assert_eq!(kernel.remove(consumer), Err(Error::Unknown));
    assert_eq!(kernel.retire(consumer), Err(Error::Unknown));
    assert_eq!(snapshot(&kernel, &[provider, consumer]), before);
}

fn apply(kernel: &mut Kernel, action: usize) -> Result<(), Error> {
    let id = action / 7;
    match action % 7 {
        0 => kernel.begin(id),
        1 => kernel.finish(id),
        2 => kernel.leave(id),
        3 => kernel.retire(id),
        4 => kernel.begin_cleanup(id),
        5 => kernel.finish_cleanup(id),
        _ => kernel.remove(id),
    }
}

fn assert_live_bindings_keep_resources(kernel: &Kernel) {
    for consumer in kernel.ids() {
        for binding in kernel.committed(consumer) {
            assert_ne!(kernel.phase(consumer), Some(Phase::Inactive));
            assert!(kernel.contains(binding.provider));
            assert_ne!(kernel.phase(binding.provider), Some(Phase::Inactive));
            assert!(!kernel.cleanup_started(binding.provider));
        }
    }
}

#[test]
fn short_deterministic_traces_preserve_guards_and_error_atomicity() {
    // Enumerate 8,232 three-step traces from inactive, Loading, and Active
    // consumer states. This regression complements the unbounded Verus proof.
    for initial in 0..3 {
        for a in 0..14 {
            for b in 0..14 {
                for c in 0..14 {
                    let (mut kernel, provider, consumer, _) = pair();
                    if initial > 0 {
                        activate(&mut kernel, provider);
                        kernel.begin(consumer).unwrap();
                    }
                    if initial == 2 {
                        kernel.finish(consumer).unwrap();
                    }
                    for action in [a, b, c] {
                        let before = snapshot(&kernel, &[provider, consumer]);
                        let ids_before = kernel.ids();
                        if apply(&mut kernel, action).is_err() {
                            assert_eq!(snapshot(&kernel, &[provider, consumer]), before);
                            assert_eq!(kernel.ids(), ids_before);
                        }
                        assert_live_bindings_keep_resources(&kernel);
                    }
                }
            }
        }
    }
}

#[test]
fn compaction_preserves_live_episode_order_and_cleanup_guards() {
    let (mut kernel, provider, consumer, service) = pair();
    activate(&mut kernel, provider);
    for _ in 0..64 {
        activate(&mut kernel, consumer);
        deactivate(&mut kernel, consumer);
    }
    activate(&mut kernel, consumer);
    let bound = kernel.committed(consumer);
    let target = kernel.target(consumer);
    assert_eq!(kernel.binding_records(), 65);
    assert_eq!(kernel.compact_bindings(), 64);
    assert_eq!(kernel.committed(consumer), bound);
    assert_eq!(kernel.target(consumer), target);
    kernel.leave(provider).unwrap();
    kernel.leave(consumer).unwrap();
    assert_eq!(kernel.compact_bindings(), 0);
    assert_eq!(kernel.begin_cleanup(provider), Err(Error::Relied));
    kernel.begin_cleanup(consumer).unwrap();
    kernel.finish_cleanup(consumer).unwrap();
    kernel.begin_cleanup(provider).unwrap();
    kernel.finish_cleanup(provider).unwrap();
    kernel.retire(consumer).unwrap();
    kernel.remove(consumer).unwrap();
    assert_eq!(kernel.compact_declarations(), 1);
    assert_eq!(
        kernel.insert(None, vec![], vec![service]),
        Err(Error::Conflict)
    );
    kernel.retire(provider).unwrap();
    kernel.remove(provider).unwrap();
    assert_eq!(kernel.compact_declarations(), 1);
    assert_eq!(kernel.compact_bindings(), 1);
    assert_eq!(kernel.declaration_records(), 0);
    let replacement = kernel.insert(None, vec![], vec![service]).unwrap();
    assert!(replacement > consumer);
    activate(&mut kernel, replacement);
    assert_eq!(kernel.resolve(service), Some(replacement));
    assert!(!kernel.contains(provider));
}
