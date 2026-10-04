//! Regression for the distinction between declaration precedence and the union
//! with dynamic ownership in the paper's Lemma 75. A retired child's declaration
//! remains registered until removal and may participate in a union cycle.
use cordis_kernel::{Kernel, Phase, Port};

#[test]
fn replacing_a_removed_provider_can_cycle_support_through_a_retired_child() {
    let mut kernel = Kernel::new();
    let x = Port { key: 0, realm: 0 };
    let y = Port { key: 1, realm: 0 };
    let z = Port { key: 2, realm: 0 };
    let old_provider = kernel.insert(None, vec![], vec![x]).unwrap();
    let parent = kernel.insert(None, vec![x], vec![]).unwrap();
    kernel.begin(old_provider).unwrap();
    kernel.finish(old_provider).unwrap();
    kernel.begin(parent).unwrap();
    // This is the insertion yielded by one stage of the parent's activation.
    // The child never begins: its z dependency has no provider.
    let child = kernel.insert(Some(parent), vec![z], vec![y]).unwrap();
    kernel.finish(parent).unwrap();

    kernel.retire(old_provider).unwrap();
    assert_eq!(kernel.target(old_provider), None);
    kernel.leave(old_provider).unwrap();
    assert_eq!(kernel.target(parent), None);
    kernel.leave(parent).unwrap();
    kernel.begin_cleanup(parent).unwrap();
    // Definition 52's inverse retires the child; it need not remove it.
    kernel.retire(child).unwrap();
    kernel.finish_cleanup(parent).unwrap();
    kernel.begin_cleanup(old_provider).unwrap();
    kernel.finish_cleanup(old_provider).unwrap();
    kernel.remove(old_provider).unwrap();

    let replacement = kernel.insert(None, vec![y], vec![x]).unwrap();
    assert_eq!(kernel.ids(), vec![parent, child, replacement]);
    for id in kernel.ids() {
        assert_eq!(kernel.phase(id), Some(Phase::Inactive));
        assert_eq!(kernel.target(id), None);
    }
    assert!(kernel.retired(child));
    assert!(!kernel.retired(parent));
    assert!(!kernel.retired(replacement));
    assert_eq!(kernel.children(parent), vec![child]);

    // Precedence: child -y-> replacement -x-> parent, an acyclic chain.
    // Ownership adds parent -> child, producing a union cycle. The root model
    // proves this exact final state's precedence ranks and absence of any union
    // ranking in global::replacement_support_cycle. Support itself is empty
    // and unique because the child is retired; that weaker fact is unaffected.
}
