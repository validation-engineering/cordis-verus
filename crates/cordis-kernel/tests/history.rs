use cordis_kernel::history::Journal;
use cordis_kernel::resources::ResourceError;

#[test]
fn journal_restores_checkpoint_then_exact_initial_values() {
    let mut journal = Journal::new(vec![10, 20]);
    journal.write(7, 0, 11).unwrap();
    let checkpoint = journal.len();
    journal.write(7, 0, 12).unwrap();
    journal.write(8, 1, 21).unwrap();
    assert_eq!(journal.read(0), Some(12));
    assert_eq!(journal.read(1), Some(21));
    assert!(journal.rollback_to(checkpoint));
    assert_eq!(journal.len(), checkpoint);
    assert_eq!(journal.read(0), Some(11));
    assert_eq!(journal.read(1), Some(20));
    assert!(journal.rollback_to(0));
    assert_eq!(journal.read(0), Some(10));
    assert_eq!(journal.read(1), Some(20));
    assert!(journal.is_empty());
    // Full recovery restores ownership, not only the numeric observation.
    journal.write(99, 0, 100).unwrap();
}

#[test]
fn rejected_operations_preserve_the_witnessed_history() {
    let mut journal = Journal::new(vec![3]);
    journal.write(1, 0, 4).unwrap();
    assert_eq!(journal.write(2, 0, 5), Err(ResourceError::Owned));
    assert_eq!(journal.write(1, 1, 5), Err(ResourceError::Unknown));
    assert!(!journal.rollback_to(2));
    assert!(!journal.rollback_to(usize::MAX));
    assert_eq!(journal.len(), 1);
    assert_eq!(journal.read(0), Some(4));
    assert!(journal.rollback_one());
    assert_eq!(journal.read(0), Some(3));
    assert!(!journal.rollback_one());
    assert!(journal.rollback_to(0));
}

#[test]
fn disjoint_owners_and_repeated_writes_unwind_in_exact_order() {
    let mut journal = Journal::new(vec![1, 2, 3]);
    journal.write(10, 0, 11).unwrap();
    journal.write(20, 1, 22).unwrap();
    journal.write(10, 0, 33).unwrap();
    journal.write(30, 2, 44).unwrap();
    for expected in [
        vec![33, 22, 3],
        vec![11, 22, 3],
        vec![11, 2, 3],
        vec![1, 2, 3],
    ] {
        assert!(journal.rollback_one());
        for (index, value) in expected.into_iter().enumerate() {
            assert_eq!(journal.read(index), Some(value));
        }
    }
    assert!(journal.is_empty());
}

#[test]
fn empty_store_has_no_valid_writes_but_valid_empty_checkpoint() {
    let mut journal = Journal::new(vec![]);
    assert_eq!(journal.read(0), None);
    assert_eq!(journal.write(0, 0, 1), Err(ResourceError::Unknown));
    assert!(!journal.rollback_one());
    assert!(journal.rollback_to(0));
}
