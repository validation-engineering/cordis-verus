use cordis_kernel::{Kernel, Port};
use std::fmt::Debug;

fn compare(reference: &Kernel, compacted: &Kernel) {
    assert_eq!(reference.identity_slots(), compacted.identity_slots());
    assert_eq!(reference.ids(), compacted.ids());
    for id in 0..=reference.identity_slots() {
        assert_eq!(reference.phase(id), compacted.phase(id));
        assert_eq!(reference.retired(id), compacted.retired(id));
        assert_eq!(reference.cleanup_started(id), compacted.cleanup_started(id));
        assert_eq!(reference.children(id), compacted.children(id));
        assert_eq!(reference.target(id), compacted.target(id));
        assert_eq!(reference.committed(id), compacted.committed(id));
        assert_eq!(reference.check_iteration(id), compacted.check_iteration(id));
    }
    for key in 0..3 {
        for realm in 0..2 {
            assert_eq!(
                reference.resolve(Port { key, realm }),
                compacted.resolve(Port { key, realm })
            );
        }
    }
}

fn step<T: Debug + PartialEq>(
    reference: &mut Kernel,
    compacted: &mut Kernel,
    action: impl Fn(&mut Kernel) -> T,
) -> T {
    compacted.compact_declarations();
    compacted.compact_bindings();
    compare(reference, compacted);
    let expected = action(reference);
    assert_eq!(expected, action(compacted));
    compacted.compact_bindings();
    compacted.compact_declarations();
    compare(reference, compacted);
    expected
}

#[test]
fn interleaved_compaction_preserves_multilevel_binding_order_errors_and_fresh_ids() {
    let mut reference = Kernel::new();
    let mut compacted = Kernel::new();
    let a = Port { key: 1, realm: 0 };
    let b = Port { key: 2, realm: 0 };
    for _ in 0..8 {
        let provider = step(&mut reference, &mut compacted, |k| {
            k.insert(None, vec![], vec![a])
        })
        .unwrap();
        let middle = step(&mut reference, &mut compacted, |k| {
            k.insert(Some(provider), vec![a], vec![b])
        })
        .unwrap();
        let consumer = step(&mut reference, &mut compacted, |k| {
            k.insert(None, vec![b, a], vec![])
        })
        .unwrap();
        for _ in 0..5 {
            for id in [provider, middle, consumer] {
                step(&mut reference, &mut compacted, |k| k.begin(id)).unwrap();
                step(&mut reference, &mut compacted, |k| k.finish(id)).unwrap();
            }
            step(&mut reference, &mut compacted, |k| k.leave(provider)).unwrap();
            assert!(step(&mut reference, &mut compacted, |k| k
                .begin_cleanup(provider))
            .is_err());
            for id in [middle, consumer] {
                step(&mut reference, &mut compacted, |k| k.leave(id)).unwrap();
            }
            for id in [consumer, middle, provider] {
                step(&mut reference, &mut compacted, |k| k.begin_cleanup(id)).unwrap();
                step(&mut reference, &mut compacted, |k| k.finish_cleanup(id)).unwrap();
            }
        }
        step(&mut reference, &mut compacted, |k| k.retire(provider)).unwrap();
        assert!(step(&mut reference, &mut compacted, |k| k.remove(provider)).is_err());
        assert!(step(&mut reference, &mut compacted, |k| k.insert(
            None,
            vec![],
            vec![a]
        ))
        .is_err());
        for id in [consumer, middle] {
            step(&mut reference, &mut compacted, |k| k.retire(id)).unwrap();
            step(&mut reference, &mut compacted, |k| k.remove(id)).unwrap();
        }
        step(&mut reference, &mut compacted, |k| k.remove(provider)).unwrap();
    }
    assert!(reference.binding_records() > 0);
    assert!(reference.declaration_records() > 0);
    assert_eq!(compacted.binding_records(), 0);
    assert_eq!(compacted.declaration_records(), 0);
    assert_eq!(compacted.identity_slots(), 24);
}
