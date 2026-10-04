use cordis_kernel::{Binding, Error, Kernel, Phase, Port};

fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}

type Observation = (usize, Option<Phase>, bool, bool, Vec<Binding>);

fn observed(kernel: &Kernel) -> Vec<Observation> {
    kernel
        .ids()
        .into_iter()
        .map(|id| {
            (
                id,
                kernel.phase(id),
                kernel.retired(id),
                kernel.cleanup_started(id),
                kernel.committed(id),
            )
        })
        .collect()
}

#[test]
fn strict_paper_departure_rejects_a_coherent_episode_without_changes() {
    let mut kernel = Kernel::new();
    let id = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.begin(id).unwrap();
    let loading = observed(&kernel);
    assert!(kernel.leave_if_changed(id).is_err());
    assert_eq!(observed(&kernel), loading);
    kernel.finish(id).unwrap();
    let active = observed(&kernel);
    assert!(kernel.leave_if_changed(id).is_err());
    assert_eq!(observed(&kernel), active);
    // An explicit host restart has a different rule, while preserving safety.
    kernel.leave(id).unwrap();
    assert_eq!(kernel.phase(id), Some(Phase::Unloading));
}

#[test]
fn strict_departure_preserves_committed_views_until_guarded_unload() {
    let mut kernel = Kernel::new();
    let provider = kernel.insert(None, vec![], vec![port(7)]).unwrap();
    kernel.begin(provider).unwrap();
    kernel.finish(provider).unwrap();
    let consumer = kernel.insert(None, vec![port(7)], vec![]).unwrap();
    kernel.begin(consumer).unwrap();
    kernel.finish(consumer).unwrap();
    let committed = kernel.committed(consumer);
    kernel.retire(provider).unwrap();
    assert_eq!(kernel.resolve(port(7)), Some(provider));
    kernel.leave_if_changed(provider).unwrap();
    assert_eq!(kernel.phase(consumer), Some(Phase::Active));
    assert_eq!(kernel.target(consumer), None);
    assert_eq!(kernel.begin_cleanup(provider), Err(Error::Relied));
    kernel.leave_if_changed(consumer).unwrap();
    assert_eq!(kernel.committed(consumer), committed);
    kernel.begin_cleanup(consumer).unwrap();
    assert_eq!(kernel.committed(consumer), committed);
    kernel.finish_cleanup(consumer).unwrap();
    assert!(kernel.committed(consumer).is_empty());
    kernel.begin_cleanup(provider).unwrap();
    kernel.finish_cleanup(provider).unwrap();
}

#[test]
fn retirement_diverts_loading_and_does_not_remove_children() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    let child = kernel.insert(Some(parent), vec![], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    kernel.retire(parent).unwrap();
    kernel.leave_if_changed(parent).unwrap();
    kernel.begin_cleanup(parent).unwrap();
    kernel.finish_cleanup(parent).unwrap();
    let before = observed(&kernel);
    assert_eq!(kernel.remove(parent), Err(Error::Children));
    assert_eq!(observed(&kernel), before);
    kernel.retire(child).unwrap();
    kernel.remove(child).unwrap();
    kernel.remove(parent).unwrap();
    let replacement = kernel.insert(None, vec![], vec![]).unwrap();
    assert!(replacement > child);
}

#[test]
fn rejected_mutations_preserve_all_observable_fibers() {
    let mut kernel = Kernel::new();
    let provider = kernel.insert(None, vec![], vec![port(8)]).unwrap();
    let missing = kernel.insert(None, vec![port(9)], vec![]).unwrap();
    kernel.begin(provider).unwrap();
    kernel.finish(provider).unwrap();
    let before = observed(&kernel);
    let identity_slots = kernel.identity_slots();
    assert_eq!(kernel.begin(missing), Err(Error::MissingDependency));
    assert_eq!(kernel.finish(missing), Err(Error::InvalidState));
    assert!(kernel.insert(None, vec![], vec![port(8)]).is_err());
    assert!(kernel.insert(None, vec![port(1), port(1)], vec![]).is_err());
    assert!(kernel.insert(Some(usize::MAX), vec![], vec![]).is_err());
    assert!(kernel.retire(usize::MAX).is_err());
    assert!(kernel.remove(provider).is_err());
    assert!(kernel.finish_cleanup(provider).is_err());
    assert_eq!(kernel.identity_slots(), identity_slots);
    assert_eq!(observed(&kernel), before);
}
