use cordis_kernel::{typed_child_domain::exercise_domain_gap, Error, Kernel, Phase, Port};

#[test]
fn the_verified_client_constructs_both_domains_from_real_kernel_calls() {
    assert_eq!(exercise_domain_gap(), (Ok(()), Err(Error::Conflict)));
}

#[test]
fn an_empty_reservation_blocks_creation_until_removal_even_after_retirement() {
    let dependency = Port { key: 1, realm: 0 };
    let provision = Port { key: 0, realm: 0 };
    let mut kernel = Kernel::new();
    let parent = kernel.insert(None, vec![], vec![dependency]).unwrap();
    assert_eq!(
        kernel.check_insert(Some(parent), &[dependency], &[provision]),
        Ok(())
    );
    let reservation = kernel
        .insert(Some(parent), vec![dependency], vec![provision])
        .unwrap();
    assert_eq!(kernel.phase(reservation), Some(Phase::Inactive));
    assert_eq!(
        kernel.check_insert(Some(parent), &[dependency], &[provision]),
        Err(Error::Conflict)
    );
    kernel.retire(reservation).unwrap();
    assert_eq!(
        kernel.check_insert(Some(parent), &[dependency], &[provision]),
        Err(Error::Conflict)
    );
    kernel.remove(reservation).unwrap();
    assert_eq!(
        kernel.check_insert(Some(parent), &[dependency], &[provision]),
        Ok(())
    );
    let child = kernel
        .insert(Some(parent), vec![dependency], vec![provision])
        .unwrap();
    assert!(child > reservation);
}
