//! Runtime regression cases for the Kernel's paper-level binding comparison.
//!
//! The public API builds each fixture. Only then do these module-local tests
//! reorder or duplicate the consumer's live links. These representations retain
//! typing and dependency coverage; the providers have no dependencies, so the
//! edits also preserve commitment order. The current `wf` permits them, but these
//! tests do not claim that public API histories can produce them. Their purpose
//! is to ensure that storage order and multiplicity do not override the paper's
//! provider-identity semantics.

use super::{Binding, Error, Kernel, Phase, Port};

#[derive(Debug, PartialEq, Eq)]
struct Snapshot {
    nodes: Vec<(bool, bool, Phase, bool, Option<usize>, u64)>,
    declarations: Vec<(usize, Port, bool)>,
    links: Vec<(usize, Binding, bool)>,
}

fn snapshot(kernel: &Kernel) -> Snapshot {
    Snapshot {
        nodes: kernel
            .nodes
            .iter()
            .map(|node| {
                (
                    node.present,
                    node.retired,
                    node.phase,
                    node.restoring,
                    node.parent,
                    node.generation,
                )
            })
            .collect(),
        declarations: kernel
            .declarations
            .iter()
            .map(|declaration| (declaration.owner, declaration.port, declaration.provides))
            .collect(),
        links: kernel
            .links
            .iter()
            .map(|link| (link.consumer, link.binding, link.live))
            .collect(),
    }
}

fn loading_consumer() -> (Kernel, [usize; 2], usize) {
    let mut kernel = Kernel::new();
    // Equal keys in different realms must still preserve distinct identities.
    let ports = [Port { key: 7, realm: 1 }, Port { key: 7, realm: 2 }];
    let providers = ports.map(|port| {
        let provider = kernel.insert(None, vec![], vec![port]).unwrap();
        kernel.begin(provider).unwrap();
        kernel.finish(provider).unwrap();
        provider
    });
    let consumer = kernel.insert(None, ports.to_vec(), vec![]).unwrap();
    kernel.begin(consumer).unwrap();
    (kernel, providers, consumer)
}

fn vary_consumer_links(kernel: &mut Kernel, consumer: usize, reorder: bool, duplicate: bool) {
    let positions: Vec<_> = kernel
        .links
        .iter()
        .enumerate()
        .filter_map(|(index, link)| (link.live && link.consumer == consumer).then_some(index))
        .collect();
    assert_eq!(positions.len(), 2);
    if reorder {
        kernel.links.swap(positions[0], positions[1]);
    }
    if duplicate {
        let link = kernel.links[positions[0]];
        kernel.links.insert(positions[0] + 1, link);
    }
}

#[test]
fn coherent_representations_accept_iteration_and_finish_without_rewriting_bindings() {
    for (reorder, duplicate) in [(true, false), (false, true), (true, true)] {
        let (mut kernel, providers, consumer) = loading_consumer();
        let canonical = kernel.target(consumer).unwrap();
        assert_eq!(canonical[0].provider, providers[0]);
        assert_eq!(canonical[1].provider, providers[1]);
        vary_consumer_links(&mut kernel, consumer, reorder, duplicate);
        let committed = kernel.committed(consumer);
        assert_ne!(committed, canonical);
        assert!(committed.iter().all(|binding| canonical.contains(binding)));
        assert!(canonical.iter().all(|binding| committed.contains(binding)));

        let before = snapshot(&kernel);
        assert_eq!(kernel.check_iteration(consumer), Ok(()));
        assert_eq!(snapshot(&kernel), before);
        assert_eq!(kernel.finish(consumer), Ok(()));
        assert_eq!(kernel.committed(consumer), committed);
        assert_eq!(kernel.target(consumer), Some(canonical));
        let mut expected = before;
        expected.nodes[consumer].2 = Phase::Active;
        assert_eq!(snapshot(&kernel), expected);
    }
}

#[test]
fn withdrawn_provider_rejects_iteration_and_finish_without_mutation() {
    let (mut kernel, providers, consumer) = loading_consumer();
    vary_consumer_links(&mut kernel, consumer, true, true);
    let committed = kernel.committed(consumer);
    kernel.leave(providers[0]).unwrap();
    assert_eq!(kernel.target(consumer), None);
    let before = snapshot(&kernel);

    assert_eq!(kernel.check_iteration(consumer), Err(Error::Changed));
    assert_eq!(snapshot(&kernel), before);
    assert_eq!(kernel.finish(consumer), Err(Error::Changed));
    assert_eq!(snapshot(&kernel), before);
    assert_eq!(kernel.committed(consumer), committed);
}

#[test]
fn retired_consumer_rejects_iteration_and_finish_without_mutation() {
    let (mut kernel, _, consumer) = loading_consumer();
    vary_consumer_links(&mut kernel, consumer, true, true);
    let committed = kernel.committed(consumer);
    kernel.retire(consumer).unwrap();
    assert_eq!(kernel.target(consumer), None);
    let before = snapshot(&kernel);

    assert_eq!(kernel.check_iteration(consumer), Err(Error::Changed));
    assert_eq!(snapshot(&kernel), before);
    assert_eq!(kernel.finish(consumer), Err(Error::Changed));
    assert_eq!(snapshot(&kernel), before);
    assert_eq!(kernel.committed(consumer), committed);
}
