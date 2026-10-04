//! The orchestration target can differ from the child an activation creates,
//! while its parent-existence guard still depends on that creation.
use cordis_kernel::{Error, Kernel, Phase};

#[test]
fn inserting_under_a_new_child_cannot_move_before_the_creating_stage() {
    let mut ordered = Kernel::new();
    let creator = ordered.insert(None, vec![], vec![]).unwrap();
    ordered.begin(creator).unwrap();
    let child = ordered.insert(Some(creator), vec![], vec![]).unwrap();
    ordered.finish(creator).unwrap();
    let descendant = ordered.insert(Some(child), vec![], vec![]).unwrap();
    assert_ne!(descendant, child);
    assert_ne!(descendant, creator);
    assert_eq!(ordered.phase(creator), Some(Phase::Active));

    let mut transposed = Kernel::new();
    let same_creator = transposed.insert(None, vec![], vec![]).unwrap();
    transposed.begin(same_creator).unwrap();
    assert_eq!(
        transposed.insert(Some(child), vec![], vec![]),
        Err(Error::Unknown)
    );
    assert_eq!(transposed.phase(same_creator), Some(Phase::Loading));
}
