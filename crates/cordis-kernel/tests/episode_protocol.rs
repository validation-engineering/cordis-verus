use cordis_kernel::episode::{cancelled_admission_witness, StageProtocol};
use cordis_kernel::Binding;

fn binding(provider: usize) -> Vec<Binding> {
    vec![Binding {
        key: 7,
        realm: 11,
        provider,
    }]
}

#[test]
fn drift_preserves_pending_stage_and_collects_its_inverse_before_unload() {
    let committed = binding(3);
    let replacement = binding(4);
    let mut protocol = StageProtocol::iterator(committed.clone());
    assert!(protocol.admit(Some(&committed)));
    protocol.register(10);
    assert_eq!(protocol.pop(), None);

    // The provider identity, not its equal-valued payload, drives cancellation.
    assert!(protocol.admit(Some(&replacement)));
    assert!(protocol.is_pending());
    assert!(!protocol.can_finish(&replacement));
    assert!(protocol.land(20));
    assert!(protocol.is_settled());
    assert!(!protocol.is_pending());
    assert!(!protocol.admit(Some(&committed)));
    assert_eq!(protocol.pop(), Some(20));
    assert_eq!(protocol.pop(), Some(10));
    assert_eq!(protocol.pop(), None);
}

#[test]
fn consecutive_stages_accumulate_lifo_and_publish_only_when_exhausted() {
    let committed = binding(3);
    let mut protocol = StageProtocol::iterator(committed.clone());
    assert!(!protocol.land(99));
    assert!(!protocol.end());
    for token in [1, 2, 3] {
        assert!(protocol.admit(Some(&committed)));
        assert!(!protocol.can_finish(&committed));
        assert!(protocol.land(token));
        assert_eq!(protocol.pop(), None);
    }
    assert!(protocol.admit(Some(&committed)));
    assert!(protocol.end());
    assert!(protocol.can_finish(&committed));
    assert!(!protocol.can_finish(&binding(4)));
    assert_eq!(protocol.pop(), Some(3));
    assert_eq!(protocol.pop(), Some(2));
    assert_eq!(protocol.pop(), Some(1));
    assert!(protocol.is_empty());
}

#[test]
fn cancellation_at_boundary_discards_continuation_without_polling() {
    let committed = binding(3);
    let mut protocol = StageProtocol::iterator(committed.clone());
    assert!(protocol.admit(Some(&committed)));
    assert!(protocol.land(8));
    protocol.cancel();
    assert!(!protocol.admit(Some(&committed)));
    assert!(protocol.is_settled());
    assert_eq!(protocol.pop(), Some(8));
}

#[test]
fn retirement_preserves_outstanding_poll_until_end() {
    let committed = binding(3);
    let mut protocol = StageProtocol::iterator(committed.clone());
    assert!(protocol.admit(Some(&committed)));
    protocol.register(8);
    protocol.cancel();
    assert!(protocol.admit(None));
    assert_eq!(protocol.pop(), None);
    assert!(protocol.end());
    assert!(!protocol.admit(Some(&committed)));
    assert_eq!(protocol.pop(), Some(8));
}

#[test]
fn realm_and_key_are_part_of_the_committed_identity() {
    let committed = binding(3);
    for changed in [
        vec![Binding {
            realm: 12,
            ..committed[0]
        }],
        vec![Binding {
            key: 8,
            ..committed[0]
        }],
        vec![],
    ] {
        let mut protocol = StageProtocol::iterator(committed.clone());
        assert!(!protocol.admit(Some(&changed)));
        assert!(protocol.is_settled());
        assert!(!protocol.admit(Some(&committed)));
    }
}

#[test]
fn verified_cancelled_admission_client_executes_both_terminal_paths() {
    let committed = binding(3);
    for inverse in [Some(41), None] {
        let mut protocol = cancelled_admission_witness(committed.clone(), &committed, inverse);
        assert!(protocol.is_settled());
        assert!(!protocol.is_pending());
        // The checked client must return the yielded inverse for real cleanup,
        // including when cancellation preceded the terminal reply.
        assert_eq!(protocol.pop(), inverse);
        assert!(protocol.is_empty());
        assert!(!protocol.admit(Some(&committed)));
        assert_eq!(protocol.pop(), None);
    }
}

#[test]
fn admission_and_finish_use_binding_identities_independent_of_buffer_order() {
    let a = binding(3)[0];
    let b = Binding {
        key: 8,
        realm: 12,
        provider: 4,
    };
    let committed = vec![a, b, a];
    let target = vec![b, a];
    let mut protocol = StageProtocol::iterator(committed.clone());
    assert!(protocol.admit(Some(&target)));
    assert!(protocol.land(17));
    assert!(protocol.admit(Some(&[a, a, b, b])));
    assert!(protocol.end());
    assert!(protocol.can_finish(&target));
    assert!(!protocol.can_finish(&[a]));
    assert!(!protocol.can_finish(&[a, b, Binding { provider: 5, ..b }]));
    assert_eq!(protocol.pop(), Some(17));
    let mut cancelled = cancelled_admission_witness(committed, &target, Some(23));
    assert_eq!(cancelled.pop(), Some(23));
}

#[test]
fn binding_matcher_agrees_with_identity_sets_for_small_buffers() {
    use cordis_kernel::episode::same_bindings;
    use std::collections::BTreeSet;
    let a = binding(3)[0];
    let alphabet = [
        a,
        Binding { key: 8, ..a },
        Binding { realm: 12, ..a },
        Binding { provider: 4, ..a },
    ];
    let mut buffers = vec![vec![]];
    for len in 1..=3 {
        for mut index in 0..4_usize.pow(len) {
            let mut buffer = Vec::new();
            for _ in 0..len {
                buffer.push(alphabet[index % 4]);
                index /= 4;
            }
            buffers.push(buffer);
        }
    }
    let identities = |buffer: &[Binding]| -> BTreeSet<_> {
        buffer
            .iter()
            .map(|b| (b.key, b.realm, b.provider))
            .collect()
    };
    for left in &buffers {
        for right in &buffers {
            assert_eq!(
                same_bindings(left, right),
                identities(left) == identities(right),
                "left={left:?}, right={right:?}"
            );
        }
    }
}
