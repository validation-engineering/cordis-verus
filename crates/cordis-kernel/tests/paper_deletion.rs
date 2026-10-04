//! A never-activated child can still be the parent of an external insertion.
//! Closing the creator's real ChildEpisode does not make that child vestigial.
use cordis_kernel::ownership::ChildEpisode;
use cordis_kernel::{Error, Kernel, Phase};

#[test]
fn external_descendant_prevents_deleting_a_closed_creator_episode() {
    let mut kernel = Kernel::new();
    let creator = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.begin(creator).unwrap();
    let mut episode = ChildEpisode::attach(&kernel, creator).unwrap();
    assert_eq!(episode.admit_current(&kernel), Ok(true));
    let child = episode.land_child(&mut kernel, vec![], vec![]).unwrap();
    assert_eq!(episode.admit_current(&kernel), Ok(true));
    assert!(episode.end());
    kernel.finish(creator).unwrap();

    let descendant = kernel.insert(Some(child), vec![], vec![]).unwrap();
    kernel.retire(descendant).unwrap();
    kernel.retire(creator).unwrap();
    kernel.leave_if_changed(creator).unwrap();
    episode.finish_restore(&mut kernel).unwrap();

    assert!(episode.is_empty());
    for id in [creator, child, descendant] {
        assert_eq!(kernel.phase(id), Some(Phase::Inactive));
        assert!(kernel.retired(id));
        assert_eq!(kernel.target(id), None);
    }
    assert_eq!(kernel.children(child), vec![descendant]);
    assert_eq!(kernel.remove(child), Err(Error::Children));

    // Deleting the creator's activation removes the only birth of `child`.
    // The external insertion's parent parameter remains part of its input.
    let mut deleted = Kernel::new();
    assert_eq!(deleted.insert(None, vec![], vec![]), Ok(creator));
    assert_eq!(
        deleted.insert(Some(child), vec![], vec![]),
        Err(Error::Unknown)
    );
}
