use cordis_kernel::episode::StageProtocol;
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
