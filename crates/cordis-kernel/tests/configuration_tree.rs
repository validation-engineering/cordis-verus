use cordis_kernel::configuration_runtime::Allocation;
use cordis_kernel::configuration_tree::{MountError, Tree, TreeError};
use cordis_kernel::lifecycle_state::native::runtime::NativeRuntime;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::Port;
use std::collections::BTreeMap;

type World = NativeRuntime<(), (), ()>;
fn allocate(world: &mut World, parent: Option<usize>, anchor: u64) -> Allocation {
    let id = world
        .register(
            parent,
            &BTreeMap::new(),
            Port {
                key: anchor,
                realm: 0,
            },
            PluginDefinition::new(vec![], vec![], ()),
            (),
        )
        .ok()
        .unwrap();
    world.configuration_allocation(id).unwrap()
}

#[test]
fn exact_names_parent_ownership_and_real_allocations_gate_tree_readiness() {
    let mut world = World::new(7300);
    let mut foreign = World::new(7301);
    let mut tree = Tree::new(7300, None);
    let parent = tree
        .insert("parent".into(), None, true, None, "root recipe")
        .unwrap();
    let child = tree
        .insert(
            "parent/child".into(),
            Some(parent),
            true,
            None,
            "child recipe",
        )
        .unwrap();
    assert!(!tree.ready());
    assert!(tree.get(parent, "parent/child").is_none());
    assert!(tree.get(child, "parent").is_none());
    assert!(matches!(
        tree.insert("parent".into(), None, false, None, "duplicate"),
        Err(TreeError::Duplicate)
    ));
    assert!(matches!(
        tree.mount::<(), _>(child, "parent/child", |_, _| panic!("must wait for parent")),
        Err(MountError::Tree(TreeError::MissingParent))
    ));
    let first = tree
        .mount::<(), _>(parent, "parent", |recipe, parent| {
            assert_eq!((*recipe, parent), ("root recipe", None));
            Ok(allocate(&mut world, parent, 73001))
        })
        .ok()
        .unwrap();
    let other = allocate(&mut foreign, None, 73002);
    assert_eq!(other.id(), first); // Numeric equality is not a domain identity.
    let wrong = tree.mount::<(), _>(child, "parent/child", |_, _| Ok(other));
    assert!(matches!(wrong, Err(MountError::Mismatch(_))));
    assert!(tree.get(child, "parent/child").unwrap().id().is_none());
    let wrong_parent = allocate(&mut world, None, 73003);
    let rejected = tree.mount::<(), _>(child, "parent/child", |_, _| Ok(wrong_parent));
    match rejected {
        Err(MountError::Mismatch(allocation)) => assert_eq!(allocation.parent(), None),
        _ => panic!("a rejected allocation must be returned to its owner"),
    }
    tree.mount::<(), _>(child, "parent/child", |recipe, parent| {
        assert_eq!((*recipe, parent), ("child recipe", Some(first)));
        Ok(allocate(&mut world, parent, 73004))
    })
    .ok()
    .unwrap();
    assert!(tree.ready());
    let second = tree
        .mount::<(), _>(parent, "parent", |_, parent| {
            Ok(allocate(&mut world, parent, 73005))
        })
        .ok()
        .unwrap();
    assert_ne!(first, second);
    assert!(!tree.ready()); // The retained child still belongs to the old parent.
    tree.mount::<(), _>(child, "parent/child", |_, parent| {
        assert_eq!(parent, Some(second));
        Ok(allocate(&mut world, parent, 73006))
    })
    .ok()
    .unwrap();
    assert!(tree.ready());
    assert!(tree.clone().ready());
}

#[test]
fn inactive_entries_never_receive_identities_and_callback_failure_keeps_recipe() {
    let mut tree = Tree::new(7400, None);
    let disabled = tree
        .insert("disabled".into(), None, false, None, 10)
        .unwrap();
    assert!(matches!(
        tree.insert("child".into(), Some(disabled), true, None, 20),
        Err(TreeError::DisabledParent)
    ));
    assert!(matches!(
        tree.mount::<(), _>(disabled, "disabled", |_, _| panic!("disabled node")),
        Err(MountError::Tree(TreeError::Disabled))
    ));
    let enabled = tree.insert("enabled".into(), None, true, None, 30).unwrap();
    assert!(matches!(
        tree.mount(enabled, "enabled", |recipe, _| {
            assert_eq!(*recipe, 30);
            Err("factory failed")
        }),
        Err(MountError::Callback("factory failed"))
    ));
    assert_eq!(**tree.get(enabled, "enabled").unwrap(), 30);
    assert!(tree.get(enabled, "enabled").unwrap().id().is_none());
}
