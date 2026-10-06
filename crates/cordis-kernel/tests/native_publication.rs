use cordis_kernel::publication::{LeaseId, PublicationError, PublicationId, PublicationRegistry};
use cordis_kernel::{Error, Kernel, Phase, Port};

fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}

fn activate(kernel: &mut Kernel, id: usize) {
    kernel.begin(id).unwrap();
    kernel.finish(id).unwrap();
}

#[test]
fn setup_can_publish_under_its_own_logical_fiber() {
    let mut kernel = Kernel::new();
    let provider = kernel.insert(None, vec![], vec![]).unwrap();
    let consumer = kernel.insert(None, vec![port(1)], vec![]).unwrap();
    kernel.begin(provider).unwrap();
    kernel.declare_provision(provider, port(1)).unwrap();
    assert_eq!(kernel.resolve(port(1)), None);
    assert_eq!(kernel.begin(consumer), Err(Error::MissingDependency));
    kernel.finish(provider).unwrap();
    activate(&mut kernel, consumer);
    assert_eq!(kernel.resolve(port(1)), Some(provider));
    assert_eq!(kernel.committed(consumer)[0].provider, provider);
    assert_eq!(kernel.identity_slots(), 2);

    kernel.leave(provider).unwrap();
    assert_eq!(kernel.begin_cleanup(provider), Err(Error::Relied));
    kernel.leave(consumer).unwrap();
    kernel.begin_cleanup(consumer).unwrap();
    kernel.finish_cleanup(consumer).unwrap();
    kernel.begin_cleanup(provider).unwrap();
    kernel.finish_cleanup(provider).unwrap();
}

#[test]
fn active_publication_is_idempotent_and_preserves_existing_bindings() {
    let mut kernel = Kernel::new();
    let first = kernel.insert(None, vec![], vec![port(1)]).unwrap();
    activate(&mut kernel, first);
    let owner = kernel.insert(None, vec![port(1)], vec![]).unwrap();
    activate(&mut kernel, owner);
    let bindings = kernel.committed(owner);
    let generation = kernel.episode_generation(owner);
    kernel.declare_provision(owner, port(2)).unwrap();
    let declarations = kernel.declaration_records();
    kernel.declare_provision(owner, port(2)).unwrap();
    assert_eq!(kernel.declaration_records(), declarations);
    assert_eq!(kernel.committed(owner), bindings);
    assert_eq!(kernel.episode_generation(owner), generation);
    assert_eq!(kernel.resolve(port(2)), Some(owner));
    assert_eq!(
        kernel.declare_provision(owner, port(1)),
        Err(Error::Conflict)
    );
    assert_eq!(kernel.declaration_records(), declarations);
}

#[test]
fn invalid_phase_retirement_and_registered_reservations_reject_extension() {
    let mut kernel = Kernel::new();
    let reserved = kernel.insert(None, vec![], vec![port(1)]).unwrap();
    let owner = kernel.insert(None, vec![], vec![]).unwrap();
    assert_eq!(
        kernel.declare_provision(usize::MAX, port(2)),
        Err(Error::Unknown)
    );
    kernel.declare_provision(owner, port(2)).unwrap();
    assert_eq!(kernel.resolve(port(2)), None);
    kernel.begin(owner).unwrap();
    assert_eq!(
        kernel.declare_provision(owner, port(1)),
        Err(Error::Conflict)
    );
    kernel.retire(reserved).unwrap();
    assert_eq!(
        kernel.declare_provision(owner, port(1)),
        Err(Error::Conflict)
    );
    kernel.remove(reserved).unwrap();
    kernel.declare_provision(owner, port(1)).unwrap();
    kernel.retire(owner).unwrap();
    assert_eq!(
        kernel.declare_provision(owner, port(2)),
        Err(Error::Retired)
    );
    assert_eq!(kernel.phase(owner), Some(Phase::Loading));
}

#[test]
fn revoked_service_remains_available_only_to_captured_leases() {
    let mut registry = PublicationRegistry::new();
    let publication = registry.publish(7, 3, port(1), 40).unwrap();
    let first = registry.acquire(publication).unwrap();
    let second = registry.acquire(publication).unwrap();
    registry.revoke(publication).unwrap();
    assert_eq!(registry.resolve(port(1)), None);
    assert_eq!(
        registry.acquire(publication),
        Err(PublicationError::Revoked)
    );
    assert_eq!(registry.leased_slot(first), Ok(40));
    assert_eq!(registry.reclaim(publication), Err(PublicationError::Relied));
    registry.release(first).unwrap();
    assert_eq!(registry.release(first), Err(PublicationError::Released));
    assert_eq!(registry.leased_slot(first), Err(PublicationError::Released));
    assert_eq!(registry.leased_slot(second), Ok(40));
    assert_eq!(registry.reclaim(publication), Err(PublicationError::Relied));
    registry.release(second).unwrap();
    assert_eq!(registry.reclaim(publication), Ok(40));
    assert_eq!(
        registry.reclaim(publication),
        Err(PublicationError::Released)
    );
}

#[test]
fn replacement_preserves_retained_old_value_and_uses_fresh_identity() {
    let mut registry = PublicationRegistry::new();
    let old = registry.publish(7, 1, port(1), 20).unwrap();
    let lease = registry.acquire(old).unwrap();
    assert_eq!(
        registry.publish(8, 1, port(1), 21),
        Err(PublicationError::Conflict)
    );
    registry.revoke(old).unwrap();
    assert_eq!(
        registry.publish(8, 1, port(1), 20),
        Err(PublicationError::Conflict)
    );
    let new = registry.publish(8, 1, port(1), 21).unwrap();
    assert_ne!(old, new);
    assert_eq!(registry.resolve(port(1)), Some(new));
    assert_eq!(registry.leased_slot(lease), Ok(20));
    assert_eq!(registry.entry(old).unwrap().owner, 7);
    assert_eq!(registry.entry(new).unwrap().owner, 8);
    registry.release(lease).unwrap();
    registry.reclaim(old).unwrap();
    let reused_slot = registry.publish(9, 1, port(2), 20).unwrap();
    assert_ne!(old, reused_slot);
    assert_eq!(registry.acquire(old), Err(PublicationError::Revoked));
    assert_eq!(registry.resolve(port(1)), Some(new));
}

#[test]
fn slot_value_updates_preserve_publication_and_lease_identity() {
    let mut registry = PublicationRegistry::new();
    let mut values = ["old"];
    let publication = registry.publish(4, 11, port(1), 0).unwrap();
    let lease = registry.acquire(publication).unwrap();
    let before = registry.entry(publication).unwrap();
    values[before.slot] = "new";
    assert_eq!(registry.entry(publication), Some(before));
    assert_eq!(registry.resolve(port(1)), Some(publication));
    assert_eq!(values[registry.leased_slot(lease).unwrap()], "new");
}

#[test]
fn reclaim_requires_revocation_and_invalid_handles_do_not_alias_zero() {
    let mut registry = PublicationRegistry::new();
    let publication = registry.publish(0, 1, port(1), 0).unwrap();
    assert_eq!(
        registry.reclaim(publication),
        Err(PublicationError::Visible)
    );
    assert_eq!(
        registry.acquire(PublicationId(usize::MAX)),
        Err(PublicationError::Unknown)
    );
    assert_eq!(
        registry.revoke(PublicationId(usize::MAX)),
        Err(PublicationError::Unknown)
    );
    assert_eq!(
        registry.release(LeaseId(usize::MAX)),
        Err(PublicationError::Unknown)
    );
    assert_eq!(registry.resolve(port(1)), Some(publication));
    registry.revoke(publication).unwrap();
    registry.revoke(publication).unwrap();
    registry.reclaim(publication).unwrap();
    registry.revoke(publication).unwrap();
    assert!(!registry.entry(publication).unwrap().retained);
}

#[test]
fn reservation_transfer_waits_for_old_committed_cleanup_without_removing_owner() {
    let mut kernel = Kernel::new();
    let old = kernel.insert(None, vec![], vec![port(1), port(2)]).unwrap();
    let new = kernel.insert(None, vec![], vec![]).unwrap();
    let consumer = kernel.insert(None, vec![port(1)], vec![]).unwrap();
    activate(&mut kernel, old);
    activate(&mut kernel, new);
    activate(&mut kernel, consumer);
    let committed = kernel.committed(consumer);
    let generation = kernel.episode_generation(old);
    let declarations = kernel.declaration_records();
    assert_eq!(kernel.release_provision(old, port(1)), Err(Error::Relied));
    assert_eq!(kernel.declaration_records(), declarations);
    assert_eq!(kernel.committed(consumer), committed);
    assert_eq!(kernel.declare_provision(new, port(1)), Err(Error::Conflict));
    kernel.leave(consumer).unwrap();
    kernel.begin_cleanup(consumer).unwrap();
    assert_eq!(kernel.release_provision(old, port(1)), Err(Error::Relied));
    kernel.finish_cleanup(consumer).unwrap();
    kernel.release_provision(old, port(1)).unwrap();
    assert!(!kernel.provision_reserved(old, port(1)));
    assert_eq!(kernel.resolve(port(1)), None);
    assert_eq!(kernel.resolve(port(2)), Some(old));
    assert_eq!(kernel.phase(old), Some(Phase::Active));
    assert_eq!(kernel.episode_generation(old), generation);
    kernel.declare_provision(new, port(1)).unwrap();
    activate(&mut kernel, consumer);
    assert_eq!(kernel.committed(consumer)[0].provider, new);
    assert_eq!(kernel.identity_slots(), 3);
}

#[test]
fn unrelated_commitments_do_not_prevent_a_port_release() {
    let mut kernel = Kernel::new();
    let provider = kernel.insert(None, vec![], vec![port(1), port(2)]).unwrap();
    let consumer = kernel.insert(None, vec![port(2)], vec![]).unwrap();
    activate(&mut kernel, provider);
    activate(&mut kernel, consumer);
    let bindings = kernel.committed(consumer);
    kernel.release_provision(provider, port(1)).unwrap();
    assert_eq!(kernel.committed(consumer), bindings);
    assert_eq!(kernel.resolve(port(2)), Some(provider));
    assert_eq!(
        kernel.release_provision(provider, port(2)),
        Err(Error::Relied)
    );
}

#[test]
fn reservation_release_is_idempotent_but_stale_owner_cannot_release_replacement() {
    let mut kernel = Kernel::new();
    let old = kernel.insert(None, vec![], vec![port(1)]).unwrap();
    kernel.retire(old).unwrap();
    kernel.release_provision(old, port(1)).unwrap();
    let new = kernel.insert(None, vec![], vec![port(1)]).unwrap();
    activate(&mut kernel, new);
    kernel.release_provision(old, port(1)).unwrap();
    assert_eq!(kernel.resolve(port(1)), Some(new));
    kernel.remove(old).unwrap();
    assert_eq!(kernel.release_provision(old, port(1)), Err(Error::Unknown));
    assert_eq!(kernel.resolve(port(1)), Some(new));
}

#[test]
fn reserved_identity_can_seal_observer_dependencies_before_first_begin() {
    let mut kernel = Kernel::new();
    let provider = kernel.insert(None, vec![], vec![port(2)]).unwrap();
    activate(&mut kernel, provider);
    let plugin = kernel.insert(None, vec![port(1)], vec![port(3)]).unwrap();
    let slots = kernel.identity_slots();
    kernel
        .configure_pending_dependencies(plugin, vec![port(2)])
        .unwrap();
    assert_eq!(kernel.identity_slots(), slots);
    assert_eq!(kernel.episode_generation(plugin), Some(0));
    assert!(kernel.provision_reserved(plugin, port(3)));
    activate(&mut kernel, plugin);
    assert_eq!(kernel.committed(plugin)[0].provider, provider);
    assert_eq!(kernel.committed(plugin)[0].key, 2);
    assert_eq!(kernel.resolve(port(3)), Some(plugin));
}

#[test]
fn sealing_rejects_duplicates_and_never_mutates_started_or_retired_fibers() {
    let mut kernel = Kernel::new();
    let provider = kernel.insert(None, vec![], vec![port(1)]).unwrap();
    activate(&mut kernel, provider);
    let plugin = kernel.insert(None, vec![port(1)], vec![]).unwrap();
    let declarations = kernel.declaration_records();
    assert_eq!(
        kernel.configure_pending_dependencies(plugin, vec![port(2), port(2)]),
        Err(Error::Conflict)
    );
    assert_eq!(kernel.declaration_records(), declarations);
    activate(&mut kernel, plugin);
    assert_eq!(
        kernel.configure_pending_dependencies(plugin, vec![]),
        Err(Error::InvalidState)
    );
    kernel.leave(plugin).unwrap();
    kernel.begin_cleanup(plugin).unwrap();
    kernel.finish_cleanup(plugin).unwrap();
    assert_eq!(
        kernel.configure_pending_dependencies(plugin, vec![]),
        Err(Error::InvalidState)
    );
    let retired = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.retire(retired).unwrap();
    assert_eq!(
        kernel.configure_pending_dependencies(retired, vec![]),
        Err(Error::Retired)
    );
    assert_eq!(
        kernel.configure_pending_dependencies(usize::MAX, vec![]),
        Err(Error::Unknown)
    );
}

#[test]
fn sealing_preserves_other_active_interfaces_and_clears_previous_injection() {
    let mut kernel = Kernel::new();
    let provider = kernel.insert(None, vec![], vec![port(1)]).unwrap();
    activate(&mut kernel, provider);
    let active = kernel.insert(None, vec![port(1)], vec![]).unwrap();
    activate(&mut kernel, active);
    let plugin = kernel.insert(None, vec![port(99)], vec![]).unwrap();
    let committed = kernel.committed(active);
    kernel
        .configure_pending_dependencies(plugin, vec![port(2), port(3)])
        .unwrap();
    kernel
        .configure_pending_dependencies(plugin, vec![])
        .unwrap();
    activate(&mut kernel, plugin);
    assert!(kernel.committed(plugin).is_empty());
    assert_eq!(kernel.committed(active), committed);
    assert_eq!(kernel.resolve(port(1)), Some(provider));
}

#[test]
fn initial_publication_declaration_preserves_phase_but_later_inactive_is_closed() {
    let mut kernel = Kernel::new();
    let id = kernel.insert(None, vec![], vec![]).unwrap();
    kernel.declare_provision(id, port(1)).unwrap();
    assert_eq!(kernel.phase(id), Some(Phase::Inactive));
    assert_eq!(kernel.episode_generation(id), Some(0));
    assert_eq!(kernel.resolve(port(1)), None);
    activate(&mut kernel, id);
    kernel.leave(id).unwrap();
    kernel.begin_cleanup(id).unwrap();
    kernel.finish_cleanup(id).unwrap();
    assert_eq!(kernel.phase(id), Some(Phase::Inactive));
    assert_eq!(
        kernel.declare_provision(id, port(2)),
        Err(Error::InvalidState)
    );
}

#[test]
fn reservation_adoption_preserves_identity_and_requires_unleased_initial_generation() {
    let mut registry = PublicationRegistry::new();
    let id = registry.publish(7, 0, port(1), 40).unwrap();
    let before = registry.entry(id).unwrap();
    for (owner, generation) in [(8, 1), (7, 0), (7, 2)] {
        assert_eq!(
            registry.can_adopt(id, owner, generation),
            Err(PublicationError::InvalidState)
        );
        assert_eq!(
            registry.adopt(id, owner, generation),
            Err(PublicationError::InvalidState)
        );
        assert_eq!(registry.entry(id), Some(before));
    }
    let lease = registry.acquire(id).unwrap();
    assert_eq!(registry.adopt(id, 7, 1), Err(PublicationError::Relied));
    assert_eq!(registry.entry(id), Some(before));
    registry.release(lease).unwrap();
    registry.can_adopt(id, 7, 1).unwrap();
    registry.adopt(id, 7, 1).unwrap();
    assert_eq!(
        registry.entry(id),
        Some(cordis_kernel::publication::Publication {
            generation: 1,
            ..before
        })
    );
    assert_eq!(registry.resolve(port(1)), Some(id));
    assert_eq!(
        registry.adopt(id, 7, 1),
        Err(PublicationError::InvalidState)
    );
    let revoked = registry.publish(7, 0, port(2), 41).unwrap();
    registry.revoke(revoked).unwrap();
    registry.adopt(revoked, 7, 1).unwrap();
    assert!(!registry.entry(revoked).unwrap().visible);
    let released = registry.publish(7, 0, port(3), 42).unwrap();
    registry.revoke(released).unwrap();
    registry.reclaim(released).unwrap();
    assert_eq!(
        registry.adopt(released, 7, 1),
        Err(PublicationError::Released)
    );
    assert_eq!(
        registry.adopt(PublicationId(usize::MAX), 7, 1),
        Err(PublicationError::Unknown)
    );
}

#[test]
fn releasing_middle_records_preserves_logical_identity_and_other_publications() {
    let mut registry = PublicationRegistry::new();
    let publications: Vec<_> = (0..4)
        .map(|i| {
            registry
                .publish(i as usize, 1, port(i), 100 + i as usize)
                .unwrap()
        })
        .collect();
    let tokens: Vec<_> = (0..12)
        .map(|i| registry.acquire(publications[i % 4]).unwrap())
        .collect();
    let mut live = [true; 12];
    // Removing from the middle, beginning and end must not reinterpret IDs as
    // their current Vec positions or release a surviving consumer's lease.
    for index in [5, 0, 11, 3, 1, 8, 6, 2, 10, 4, 9, 7] {
        registry.release(tokens[index]).unwrap();
        live[index] = false;
        assert_eq!(registry.lease_allocation_count(), 12);
        assert_eq!(
            registry.lease_record_count(),
            live.iter().filter(|v| **v).count()
        );
        for (i, token) in tokens.iter().enumerate() {
            if live[i] {
                assert_eq!(
                    registry.lease(*token).unwrap().publication,
                    publications[i % 4]
                );
                assert_eq!(registry.leased_slot(*token), Ok(100 + i % 4));
            } else {
                assert_eq!(registry.lease(*token), None);
                assert_eq!(
                    registry.leased_slot(*token),
                    Err(PublicationError::Released)
                );
                assert_eq!(registry.release(*token), Err(PublicationError::Released));
            }
        }
    }
    let fresh = registry.acquire(publications[0]).unwrap();
    assert_eq!(fresh, LeaseId(12));
    assert_eq!(registry.leased_slot(fresh), Ok(100));
    for token in tokens {
        assert_eq!(registry.release(token), Err(PublicationError::Released));
    }
    assert_eq!(registry.lease_record_count(), 1);
    assert_eq!(registry.leased_slot(fresh), Ok(100));
}

#[test]
fn unrelated_churn_does_not_collect_a_revoked_publications_old_cleanup_lease() {
    let mut registry = PublicationRegistry::new();
    let old = registry.publish(1, 1, port(1), 10).unwrap();
    let pinned = registry.acquire(old).unwrap();
    registry.revoke(old).unwrap();
    let replacement = registry.publish(2, 1, port(1), 11).unwrap();
    let first_released = registry.acquire(replacement).unwrap();
    registry.release(first_released).unwrap();
    for _ in 0..1_000 {
        let transient = registry.acquire(replacement).unwrap();
        assert_eq!(registry.leased_slot(transient), Ok(11));
        registry.release(transient).unwrap();
        assert_eq!(registry.lease_record_count(), 1);
        assert_eq!(registry.leased_slot(pinned), Ok(10));
        assert_eq!(registry.reclaim(old), Err(PublicationError::Relied));
        assert_eq!(
            registry.release(first_released),
            Err(PublicationError::Released)
        );
    }
    assert_eq!(registry.lease_allocation_count(), 1_002);
    registry.release(pinned).unwrap();
    assert_eq!(registry.lease_record_count(), 0);
    assert_eq!(registry.reclaim(old), Ok(10));
    assert_eq!(registry.resolve(port(1)), Some(replacement));
    assert_eq!(registry.lease(pinned), None);
    assert_eq!(
        registry.leased_slot(pinned),
        Err(PublicationError::Released)
    );
}

#[test]
fn failed_operations_preserve_live_records_and_allocation_high_water() {
    let mut registry = PublicationRegistry::new();
    let publication = registry.publish(1, 1, port(1), 10).unwrap();
    let active = registry.acquire(publication).unwrap();
    let released = registry.acquire(publication).unwrap();
    registry.release(released).unwrap();
    registry.revoke(publication).unwrap();
    let before = registry.lease(active);
    let entry = registry.entry(publication);
    assert_eq!(
        registry.acquire(publication),
        Err(PublicationError::Revoked)
    );
    assert_eq!(
        registry.acquire(PublicationId(999)),
        Err(PublicationError::Unknown)
    );
    assert_eq!(registry.release(released), Err(PublicationError::Released));
    for unknown in [LeaseId(2), LeaseId(999), LeaseId(usize::MAX)] {
        assert_eq!(registry.lease(unknown), None);
        assert_eq!(registry.release(unknown), Err(PublicationError::Unknown));
        assert_eq!(
            registry.leased_slot(unknown),
            Err(PublicationError::Unknown)
        );
    }
    assert_eq!(registry.reclaim(publication), Err(PublicationError::Relied));
    assert_eq!(registry.lease_record_count(), 1);
    assert_eq!(registry.lease_allocation_count(), 2);
    assert_eq!(registry.lease(active), before);
    assert_eq!(registry.entry(publication), entry);
    assert_eq!(registry.leased_slot(active), Ok(10));
}
