use cordis_kernel::action_ledger::{ActionError, ActionKind, ActionLedger, ActionTicket};

#[test]
fn exact_completion_rejects_every_stale_ticket_field_without_consuming_work() {
    let mut ledger = ActionLedger::new(7);
    let ticket = ledger.issue(4, 9, ActionKind::Setup).unwrap();
    for forged in [
        ActionTicket {
            domain: 8,
            ..ticket
        },
        ActionTicket { id: 5, ..ticket },
        ActionTicket {
            generation: 10,
            ..ticket
        },
        ActionTicket {
            action: ticket.action + 1,
            ..ticket
        },
        ActionTicket {
            kind: ActionKind::Cleanup,
            ..ticket
        },
    ] {
        assert!(ledger.complete(forged).is_err());
        assert_eq!(ledger.pending(4), Some(ticket));
        assert_eq!(ledger.len(), 1);
    }
    ledger.complete(ticket).unwrap();
    assert_eq!(ledger.complete(ticket), Err(ActionError::Stale));
    assert!(ledger.is_empty());
}

#[test]
fn one_outstanding_action_per_owner_and_completion_does_not_consume_other_owners() {
    let mut ledger = ActionLedger::new(1);
    let first = ledger.issue(10, 1, ActionKind::Setup).unwrap();
    let second = ledger.issue(11, 2, ActionKind::Cleanup).unwrap();
    let third = ledger.issue(12, 3, ActionKind::Setup).unwrap();
    assert_eq!(
        ledger.issue(11, 9, ActionKind::Setup),
        Err(ActionError::Pending)
    );
    ledger.complete(second).unwrap();
    assert_eq!(ledger.pending(10), Some(first));
    assert_eq!(ledger.pending(11), None);
    assert_eq!(ledger.pending(12), Some(third));
    ledger.complete(first).unwrap();
    assert_eq!(ledger.pending(12), Some(third));
    ledger.complete(third).unwrap();
    assert!(ledger.is_empty());
}

#[test]
fn reused_owner_and_episode_cannot_alias_completed_action_or_other_domain() {
    let mut ledger = ActionLedger::new(2);
    let old = ledger.issue(0, 3, ActionKind::Cleanup).unwrap();
    ledger.complete(old).unwrap();
    let retry = ledger.issue(0, 3, ActionKind::Cleanup).unwrap();
    assert!(retry.action > old.action);
    assert_eq!(ledger.complete(old), Err(ActionError::Stale));
    assert_eq!(ledger.pending(0), Some(retry));
    let mut other = ActionLedger::new(3);
    let other_ticket = other.issue(0, 3, ActionKind::Cleanup).unwrap();
    assert_eq!(other.complete(retry), Err(ActionError::WrongDomain));
    assert_eq!(other.pending(0), Some(other_ticket));
}

#[test]
fn completed_actions_do_not_accumulate_registry_tombstones() {
    let mut ledger = ActionLedger::new(5);
    let mut previous_action = 0;
    for generation in 1..=1000 {
        let ticket = ledger.issue(3, generation, ActionKind::Setup).unwrap();
        assert!(ticket.action > previous_action);
        previous_action = ticket.action;
        assert_eq!(ledger.len(), 1);
        ledger.complete(ticket).unwrap();
        assert_eq!(ledger.len(), 0);
    }
}

#[test]
fn capacity_preflight_is_atomic_and_does_not_reserve_tokens() {
    let mut ledger = ActionLedger::new(12);
    assert_eq!(ledger.check_capacity(u64::MAX), Err(ActionError::Capacity));
    ledger.check_capacity(u64::MAX - 1).unwrap();
    let ticket = ledger.issue(0, 1, ActionKind::Setup).unwrap();
    assert_eq!(ticket.action, 1);
    assert_eq!(
        ledger.check_capacity(u64::MAX - 1),
        Err(ActionError::Capacity)
    );
    assert_eq!(ledger.pending(0), Some(ticket));
    assert_eq!(ledger.domain(), 12);
}
