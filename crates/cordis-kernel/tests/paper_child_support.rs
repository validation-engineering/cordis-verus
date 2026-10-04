//! A general external Insert keeps its ownership parent without making that
//! parent an implicit activation dependency. This is the executable counterpart
//! of `child_history::external_parent_support_counterexample`.
use cordis_kernel::{Kernel, Phase};

#[test]
fn external_child_can_be_quietly_active_under_an_inactive_retired_parent() {
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.retire(parent).unwrap();
    let child = kernel.insert(Some(parent), vec![], vec![]).unwrap();
    kernel.begin(child).unwrap();
    kernel.finish(child).unwrap();

    assert_eq!(kernel.children(parent), vec![child]);
    assert_eq!(kernel.phase(parent), Some(Phase::Inactive));
    assert!(kernel.retired(parent));
    assert_eq!(kernel.target(parent), None);
    assert_eq!(kernel.phase(child), Some(Phase::Active));
    assert!(!kernel.retired(child));
    assert_eq!(kernel.target(child), Some(vec![]));
}
