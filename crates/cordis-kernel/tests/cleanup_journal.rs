use cordis_kernel::cleanup_journal::{CleanupJournal, RestoreOutcome, RestoreTicket};

#[test]
fn failure_retains_selected_token_and_retry_rejects_old_or_foreign_receipts() {
    let mut journal = CleanupJournal::scope(41);
    journal.register(1);
    journal.register(2);
    let first = journal.begin_restore().unwrap().unwrap();
    assert_eq!(first.token, 2);
    journal.register(3); // Late registration cannot replace the in-flight receipt.
    assert!(!journal.complete(
        RestoreTicket {
            domain: 42,
            ..first
        },
        RestoreOutcome::Succeeded
    ));
    assert!(journal.complete(first, RestoreOutcome::Failed));
    assert!(!journal.is_empty());
    assert_eq!(journal.receipt(), Some(first));
    assert_eq!(journal.begin_restore().unwrap(), None);
    assert!(!journal.complete(first, RestoreOutcome::Succeeded));
    let retry = journal.retry().unwrap();
    assert_eq!(retry.token, first.token);
    assert!(retry.attempt > first.attempt);
    assert!(!journal.complete(first, RestoreOutcome::Succeeded));
    assert!(journal.complete(retry, RestoreOutcome::Succeeded));
    assert!(!journal.complete(retry, RestoreOutcome::Succeeded));
    for token in [3, 1] {
        let ticket = journal.begin_restore().unwrap().unwrap();
        assert_eq!(ticket.token, token);
        assert!(journal.complete(ticket, RestoreOutcome::Succeeded));
    }
    assert!(journal.is_empty());
    assert!(journal.retry().is_err());
}

#[test]
fn pending_setup_must_land_before_restoration_can_select_any_inverse() {
    let mut journal = CleanupJournal::iterator(7, vec![]);
    assert!(journal.admit(Some(&[])));
    journal.register(1);
    journal.cancel();
    assert_eq!(journal.begin_restore().unwrap(), None);
    assert!(journal.land(2));
    let last = journal.begin_restore().unwrap().unwrap();
    assert_eq!(last.token, 2);
    assert!(journal.complete(last, RestoreOutcome::Drained));
    let earlier = journal.begin_restore().unwrap().unwrap();
    assert_eq!(earlier.token, 1);
    assert!(journal.complete(earlier, RestoreOutcome::Succeeded));
    assert!(journal.is_empty());
}

#[test]
fn equal_local_token_and_attempt_numbers_do_not_cross_journal_domains() {
    let mut left = CleanupJournal::scope(11);
    let mut right = CleanupJournal::scope(12);
    left.register(0);
    right.register(0);
    let a = left.begin_restore().unwrap().unwrap();
    let b = right.begin_restore().unwrap().unwrap();
    assert_eq!((a.token, a.attempt), (b.token, b.attempt));
    assert!(!right.complete(a, RestoreOutcome::Succeeded));
    assert_eq!(right.receipt(), Some(b));
    assert!(right.complete(b, RestoreOutcome::Succeeded));
    assert!(!left.is_empty());
}
