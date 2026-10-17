use cordis_kernel::identity_issuer::IdentityIssuer;
use std::sync::{Arc, Barrier};

#[test]
fn sequential_allocations_have_distinct_permissions() {
    let issuer = IdentityIssuer::new();
    {
        let mut first = issuer.issue().ok().unwrap();
        let second = issuer.issue().ok().unwrap();
        assert_eq!((first.get(), second.get()), (1, 2));
        assert!(first.distinct_from(&second));
    }
    assert_eq!(issuer.issue().ok().unwrap().get(), 3);
}

#[test]
fn concurrent_issuance_is_gapless_and_never_repeats() {
    const THREADS: usize = 8;
    const PER_THREAD: usize = 512;
    let issuer = Arc::new(IdentityIssuer::new());
    let ready = Arc::new(Barrier::new(THREADS));
    let workers: Vec<_> = (0..THREADS)
        .map(|_| {
            let issuer = issuer.clone();
            let ready = ready.clone();
            std::thread::spawn(move || {
                ready.wait();
                (0..PER_THREAD)
                    .map(|_| issuer.issue().ok().unwrap().get())
                    .collect::<Vec<_>>()
            })
        })
        .collect();
    let mut values: Vec<_> = workers
        .into_iter()
        .flat_map(|worker| worker.join().unwrap())
        .collect();
    values.sort_unstable();
    assert_eq!(
        values,
        (1..=(THREADS * PER_THREAD) as u64).collect::<Vec<_>>()
    );
    assert_eq!(issuer.issue().ok().unwrap().get(), values.len() as u64 + 1);
}

#[test]
fn exhaustion_never_wraps_or_reissues_the_last_identity() {
    let issuer = IdentityIssuer::starting_at(u64::MAX - 1).unwrap();
    let exhausted = {
        let last = issuer.issue().ok().unwrap();
        assert_eq!(last.get(), u64::MAX - 1);
        issuer.issue().err().unwrap()
    };
    for _ in 0..8 {
        assert!(issuer.remains_exhausted(&exhausted));
        assert!(issuer.issue().is_err());
    }
}

#[test]
fn zero_is_rejected_and_exhausted_namespace_stays_exhausted() {
    assert!(IdentityIssuer::starting_at(0).is_none());
    let issuer = IdentityIssuer::starting_at(u64::MAX).unwrap();
    let exhausted = issuer.issue().err().unwrap();
    assert!(issuer.remains_exhausted(&exhausted));
    assert!(issuer.issue().is_err());
}

#[test]
fn numeric_identity_is_scoped_to_its_issuer() {
    let left = IdentityIssuer::new();
    let right = IdentityIssuer::new();
    // Equal integers in different namespaces do not establish object identity.
    assert_eq!(
        left.issue().ok().unwrap().get(),
        right.issue().ok().unwrap().get()
    );
}
