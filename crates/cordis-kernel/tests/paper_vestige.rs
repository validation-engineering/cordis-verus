//! Executable counterexamples to unrestricted vestigial-entry invisibility.
//! They concern the printed lemma's rule applicability, not memory safety.
use cordis_kernel::{Error, Kernel, Phase};

#[test]
fn erasing_a_vestigial_child_changes_the_parent_removal_guard() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    let child = kernel.insert(Some(parent), vec![], vec![]).unwrap();
    kernel.retire(child).unwrap();
    kernel.retire(parent).unwrap();
    assert_eq!(kernel.phase(child), Some(Phase::Inactive));
    assert!(kernel.children(child).is_empty());
    assert_eq!(kernel.remove(parent), Err(Error::Children));
    // Lemma 62(2) lists only O-Insert exceptions, but this O-Remove changes.
    kernel.remove(child).unwrap();
    assert_eq!(kernel.remove(parent), Ok(()));
}

#[test]
fn vestigial_parent_is_observable_to_new_child_insertion() {
    let mut before = Kernel::new();
    let parent = before.insert(None, vec![], vec![]).unwrap();
    before.retire(parent).unwrap();
    assert_eq!(before.phase(parent), Some(Phase::Inactive));
    assert!(before.children(parent).is_empty());
    let child = before.insert(Some(parent), vec![], vec![]).unwrap();
    assert_eq!(before.children(parent), vec![child]);

    let mut erased = Kernel::new();
    let same_parent = erased.insert(None, vec![], vec![]).unwrap();
    erased.retire(same_parent).unwrap();
    erased.remove(same_parent).unwrap();
    assert_eq!(
        erased.insert(Some(same_parent), vec![], vec![]),
        Err(Error::Unknown)
    );
}

#[test]
fn retiring_an_already_removed_child_requires_an_idempotent_extension() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.begin(parent).unwrap();
    let child = kernel.insert(Some(parent), vec![], vec![]).unwrap();
    // The orchestrator may remove an inactive child before its parent's inverse.
    kernel.retire(child).unwrap();
    kernel.remove(child).unwrap();
    assert_eq!(kernel.retire(child), Err(Error::Unknown));
    assert_eq!(kernel.phase(parent), Some(Phase::Loading));
}
