use cordis_kernel::{Binding, Error, Kernel, Phase, Port};

fn port(key: u64, realm: u64) -> Port {
    Port { key, realm }
}

#[derive(Debug, PartialEq, Eq)]
struct FiberObservation {
    id: usize,
    phase: Option<Phase>,
    retired: bool,
    restoring: bool,
    generation: Option<u64>,
    children: Vec<usize>,
    committed: Vec<Binding>,
    target: Option<Vec<Binding>>,
    reservations: Vec<bool>,
}

#[derive(Debug, PartialEq, Eq)]
struct Observation {
    slots: usize,
    declarations: usize,
    bindings: usize,
    fibers: Vec<FiberObservation>,
}

fn observe(kernel: &Kernel, ports: &[Port]) -> Observation {
    Observation {
        slots: kernel.identity_slots(),
        declarations: kernel.declaration_records(),
        bindings: kernel.binding_records(),
        fibers: kernel
            .ids()
            .into_iter()
            .map(|id| FiberObservation {
                id,
                phase: kernel.phase(id),
                retired: kernel.retired(id),
                restoring: kernel.cleanup_started(id),
                generation: kernel.episode_generation(id),
                children: kernel.children(id),
                committed: kernel.committed(id),
                target: kernel.target(id),
                reservations: ports
                    .iter()
                    .map(|&port| kernel.provision_reserved(id, port))
                    .collect(),
            })
            .collect(),
    }
}

fn checked_insert(
    kernel: &mut Kernel,
    parent: Option<usize>,
    dependencies: Vec<Port>,
    provisions: Vec<Port>,
    expected: Result<(), Error>,
) -> Result<usize, Error> {
    let probes: Vec<_> = dependencies.iter().chain(&provisions).copied().collect();
    let before = observe(kernel, &probes);
    let checked = kernel.check_insert(parent, &dependencies, &provisions);
    assert_eq!(checked, expected);
    assert_eq!(observe(kernel, &probes), before);
    let inserted = kernel.insert(parent, dependencies, provisions);
    assert_eq!(inserted.map(|_| ()), checked);
    if inserted.is_err() {
        assert_eq!(observe(kernel, &probes), before);
    }
    inserted
}

#[test]
fn preflight_and_insert_agree_on_duplicates_and_parent_error_precedence() {
    let mut kernel = Kernel::new();
    let service = port(1, 0);
    let provider = kernel.insert(None, vec![], vec![service]).unwrap();
    kernel.begin(provider).unwrap();
    kernel.finish(provider).unwrap();
    let consumer = kernel.insert(None, vec![service], vec![]).unwrap();
    kernel.begin(consumer).unwrap();
    kernel.finish(consumer).unwrap();
    let fresh = port(2, 1);
    for (dependencies, provisions) in [
        (vec![fresh, fresh], vec![]),
        (vec![], vec![fresh, fresh]),
        (vec![], vec![service]),
    ] {
        assert_eq!(
            checked_insert(
                &mut kernel,
                None,
                dependencies,
                provisions,
                Err(Error::Conflict)
            ),
            Err(Error::Conflict)
        );
    }
    // An absent parent is checked before either conflicting interface list.
    assert_eq!(
        checked_insert(
            &mut kernel,
            Some(99),
            vec![fresh, fresh],
            vec![service],
            Err(Error::Unknown),
        ),
        Err(Error::Unknown)
    );
}

#[test]
fn same_key_in_distinct_realms_is_not_a_duplicate_or_reservation_conflict() {
    let mut kernel = Kernel::new();
    let a = port(7, 1);
    let b = port(7, 2);
    let provider = checked_insert(&mut kernel, None, vec![], vec![a, b], Ok(())).unwrap();
    kernel.begin(provider).unwrap();
    kernel.finish(provider).unwrap();
    let consumer = checked_insert(&mut kernel, None, vec![a, b], vec![], Ok(())).unwrap();
    kernel.begin(consumer).unwrap();
    assert_eq!(kernel.committed(consumer).len(), 2);
    assert_eq!(kernel.resolve(a), Some(provider));
    assert_eq!(kernel.resolve(b), Some(provider));
}

#[test]
fn inactive_and_retired_providers_reserve_ports_until_registry_removal() {
    let mut kernel = Kernel::new();
    let service = port(8, 0);
    let reserved = checked_insert(&mut kernel, None, vec![], vec![service], Ok(())).unwrap();
    assert_eq!(kernel.phase(reserved), Some(Phase::Inactive));
    assert_eq!(kernel.resolve(service), None);
    assert_eq!(
        checked_insert(
            &mut kernel,
            None,
            vec![],
            vec![service],
            Err(Error::Conflict)
        ),
        Err(Error::Conflict)
    );
    kernel.retire(reserved).unwrap();
    assert_eq!(
        checked_insert(
            &mut kernel,
            None,
            vec![],
            vec![service],
            Err(Error::Conflict)
        ),
        Err(Error::Conflict)
    );
    kernel.remove(reserved).unwrap();
    let replacement = checked_insert(&mut kernel, None, vec![], vec![service], Ok(())).unwrap();
    assert!(replacement > reserved);
    assert!(!kernel.contains(reserved));
}

#[test]
fn registration_accepts_missing_dependencies_and_inactive_or_retired_parents() {
    let mut kernel = Kernel::new();
    let parent = checked_insert(&mut kernel, None, vec![], vec![], Ok(())).unwrap();
    let missing = port(9, 0);
    let child = checked_insert(&mut kernel, Some(parent), vec![missing], vec![], Ok(())).unwrap();
    assert_eq!(kernel.phase(parent), Some(Phase::Inactive));
    assert_eq!(kernel.phase(child), Some(Phase::Inactive));
    assert_eq!(kernel.begin(child), Err(Error::MissingDependency));
    kernel.retire(parent).unwrap();
    let late_child =
        checked_insert(&mut kernel, Some(parent), vec![missing], vec![], Ok(())).unwrap();
    assert!(kernel.retired(parent));
    assert!(!kernel.retired(late_child));
    assert_eq!(kernel.children(parent), vec![child, late_child]);
    // Insertion checks its current domain; it does not promise activation.
    assert_eq!(kernel.begin(late_child), Err(Error::MissingDependency));
}

#[test]
fn successful_preflight_does_not_reserve_a_future_insertion() {
    let mut kernel = Kernel::new();
    let service = port(10, 0);
    let before = observe(&kernel, &[service]);
    assert_eq!(kernel.check_insert(None, &[], &[service]), Ok(()));
    assert_eq!(kernel.check_insert(None, &[], &[service]), Ok(()));
    assert_eq!(observe(&kernel, &[service]), before);
    checked_insert(&mut kernel, None, vec![], vec![service], Ok(())).unwrap();
    // A competing registration changes the domain even without publication.
    assert_eq!(
        checked_insert(
            &mut kernel,
            None,
            vec![],
            vec![service],
            Err(Error::Conflict)
        ),
        Err(Error::Conflict)
    );
}
