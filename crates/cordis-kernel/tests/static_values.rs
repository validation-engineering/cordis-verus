use cordis_kernel::{
    execution::Execution,
    host_context::Association,
    static_values::{Import, Values},
    Port,
};
use std::sync::Arc;
type Work = Execution<(), (), (), ()>;
const PORT: Port = Port { key: 10, realm: 2 };
#[test]
fn static_inputs_preserve_real_slots_and_reject_missing_duplicate_and_extra_ports() {
    let work = Work::new(401);
    let value = Arc::new(String::from("selected provider"));
    let input = || Import {
        port: PORT,
        provider: 7,
        value: value.clone(),
    };
    let values = Values::new(&work, 9, 1, vec![PORT], vec![], vec![input()])
        .unwrap_or_else(|_| panic!("valid input"));
    let context = values.context();
    assert!(context.association().matches(&work));
    let (provider, slot) = values.read(PORT).unwrap();
    assert_eq!(provider, 7);
    assert!(Arc::ptr_eq(slot, &value));
    assert!(Values::new(&work, 9, 1, vec![PORT], vec![], vec![input(), input()]).is_err());
    assert!(Values::new(
        &work,
        9,
        1,
        vec![PORT, Port { key: 11, realm: 2 }],
        vec![],
        vec![input(), input()]
    )
    .is_err());
    assert!(Values::new(
        &work,
        9,
        1,
        vec![Port { key: 11, realm: 2 }],
        vec![],
        vec![input()]
    )
    .is_err());
    assert!(Values::new(&work, 9, 0, vec![PORT], vec![], vec![input()]).is_err());
}
#[test]
fn static_publication_uses_its_bound_owner_and_declarations() {
    let work = Work::new(402);
    let mut values = Values::<u64>::new(&work, 9, 1, vec![], vec![PORT], vec![])
        .unwrap_or_else(|_| panic!("valid input"));
    assert!(values.provide(8, &[PORT], PORT, Arc::new(1)).is_err());
    let wrong = Port { key: 11, realm: 2 };
    assert!(values.provide(9, &[wrong], wrong, Arc::new(2)).is_err());
    let value = Arc::new(3);
    values.provide(9, &[PORT], PORT, value.clone()).unwrap();
    assert!(values.provide(9, &[PORT], PORT, Arc::new(4)).is_err());
    assert!(Arc::ptr_eq(values.read(PORT).unwrap().1, &value));
}
#[test]
fn association_distinguishes_actual_work_owners_even_without_native_begin() {
    let a = Work::new(403);
    let b = Work::new(404);
    let owner = Association::from_execution(&a);
    assert!(owner.matches(&a));
    assert!(!owner.matches(&b));
}

#[test]
fn static_definition_resolves_realms_and_preserves_inherited_foreign_ports() {
    use cordis_kernel::{realm_context::RealmContext, static_values::Definition};
    let work = Work::new(405);
    let inherited = Port { key: 10, realm: 7 };
    let definitions = Definition {
        owner: 11,
        generation: 3,
        realms: RealmContext::default().with_realm(10, 2),
        dependencies: vec![10],
        inherited: vec![inherited, inherited],
        provisions: vec![12],
    };
    let inputs = vec![
        Import {
            port: PORT,
            provider: 8,
            value: Arc::new(1),
        },
        Import {
            port: inherited,
            provider: 9,
            value: Arc::new(2),
        },
    ];
    let values = Values::from_definition(&work, definitions, inputs)
        .unwrap_or_else(|_| panic!("valid resolved imports"));
    assert_eq!(values.read(PORT).unwrap().0, 8);
    assert_eq!(values.read(inherited).unwrap().0, 9);
    assert_eq!(
        values.context().provision_ports(),
        &[Port { key: 12, realm: 0 }]
    );
}
