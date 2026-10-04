use cordis_kernel::mixed_driver::fresh::admitted::{Admission, AdmissionError};
use cordis_kernel::mixed_driver::fresh::{
    Blueprint, Command, DriverError, FreshDriver, Instruction, Outcome,
};
use cordis_kernel::{Error, Phase, Port};
fn key() -> Port {
    Port { key: 7, realm: 3 }
}
fn provider() -> Blueprint {
    Blueprint::new(
        vec![],
        vec![key()],
        vec![Instruction::Provide {
            key: key(),
            value: 7,
            next: None,
        }],
    )
}
fn client() -> Blueprint {
    Blueprint::new(
        vec![key()],
        vec![],
        vec![Instruction::Xor {
            key: key(),
            mask: 5,
            next: None,
        }],
    )
}
fn install(driver: &mut FreshDriver, bp: usize) -> usize {
    let id = driver.insert(None, bp).unwrap();
    driver.begin(id).unwrap();
    driver.step(id).unwrap();
    id
}
fn admit(driver: FreshDriver, actor: usize) -> Admission {
    match driver.admit(actor) {
        Ok(admitted) => admitted,
        Err(rejected) => panic!("admission failed: {:?}", rejected.error),
    }
}
fn setup() -> (FreshDriver, usize, usize) {
    let mut d = FreshDriver::new(vec![provider(), client()]);
    let p = install(&mut d, 0);
    let c = d.insert(None, 1).unwrap();
    d.begin(c).unwrap();
    (d, p, c)
}

#[test]
fn admitted_xor_lands_after_provider_departure_and_undo_uses_captured_provider() {
    let (driver, provider, client) = setup();
    let mut admitted = admit(driver, client);
    admitted.apply(Command::Retire { actor: provider }).unwrap();
    admitted.apply(Command::Depart { actor: provider }).unwrap();
    let result = admitted.land().unwrap();
    assert!(result.diverted);
    assert_eq!(result.actor, client);
    assert_eq!(result.outcome, Outcome::Finished);
    assert_eq!(admitted.phase(client), Some(Phase::Unloading));
    assert_eq!(admitted.read(provider, key()), Some(7 ^ 5));
    assert_eq!(admitted.inverse_count(client), Some(1));
    assert!(admitted.is_consumed());
    assert_eq!(admitted.land(), Err(AdmissionError::StaleAdmission));
    assert_eq!(admitted.read(provider, key()), Some(7 ^ 5));
    assert_eq!(admitted.inverse_count(client), Some(1));
    assert_eq!(
        admitted.apply(Command::Unload { actor: provider }),
        Err(DriverError::Kernel(Error::Relied))
    );
    admitted.apply(Command::Unload { actor: client }).unwrap();
    assert_eq!(admitted.read(provider, key()), Some(7));
    admitted.apply(Command::Unload { actor: provider }).unwrap();
}

#[test]
fn admitted_child_allocates_at_landing_and_diverts_without_terminal_publication() {
    let missing = Port { key: 99, realm: 3 };
    let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let parent = Blueprint::new(
        vec![],
        vec![missing],
        vec![Instruction::Child {
            blueprint: 0,
            next: None,
        }],
    );
    let mut driver = FreshDriver::new(vec![leaf, parent]);
    let parent = driver.insert(None, 1).unwrap();
    driver.begin(parent).unwrap();
    let mut admitted = admit(driver, parent);
    let external = admitted
        .apply(Command::Insert {
            parent: None,
            blueprint: 0,
        })
        .unwrap()
        .actor();
    assert_eq!(external, 1);
    admitted.apply(Command::Retire { actor: parent }).unwrap();
    let result = admitted.land().unwrap();
    assert_eq!(
        result.outcome,
        Outcome::Child {
            child: 2,
            finished: true
        }
    );
    assert!(result.diverted);
    assert_eq!(admitted.phase(parent), Some(Phase::Unloading));
    assert_eq!(admitted.read(parent, missing), None);
    assert_eq!(admitted.inverse_count(parent), Some(1));
    assert_eq!(
        admitted.apply(Command::Remove { actor: 2 }),
        Err(DriverError::Retained)
    );
    admitted.apply(Command::Unload { actor: parent }).unwrap();
    let mut driver = admitted.into_driver();
    assert!(driver.retired(2));
    assert!(!driver.retired(external));
    driver.remove(2).unwrap();
    assert_eq!(driver.phase(external), Some(Phase::Inactive));
}

#[test]
fn same_actor_progress_makes_admission_stale_without_landing_twice() {
    let (driver, provider, client) = setup();
    let mut admitted = admit(driver, client);
    admitted.apply(Command::Step { actor: client }).unwrap();
    assert_eq!(admitted.land(), Err(AdmissionError::StaleAdmission));
    assert!(!admitted.is_consumed());
    assert_eq!(admitted.read(provider, key()), Some(7 ^ 5));
    assert_eq!(admitted.inverse_count(client), Some(1));
    assert_eq!(admitted.phase(client), Some(Phase::Active));
}

#[test]
fn old_generation_is_rejected_even_when_same_code_and_pc_return_on_reactivation() {
    let (driver, provider, client) = setup();
    let mut admitted = admit(driver, client);
    for command in [
        Command::Retire { actor: provider },
        Command::Depart { actor: provider },
        Command::Depart { actor: client },
        Command::Unload { actor: client },
        Command::Unload { actor: provider },
        Command::Remove { actor: provider },
    ] {
        admitted.apply(command).unwrap();
    }
    let replacement = admitted
        .apply(Command::Insert {
            parent: None,
            blueprint: 0,
        })
        .unwrap()
        .actor();
    admitted
        .apply(Command::Begin { actor: replacement })
        .unwrap();
    admitted
        .apply(Command::Step { actor: replacement })
        .unwrap();
    admitted.apply(Command::Begin { actor: client }).unwrap();
    assert_eq!(admitted.land(), Err(AdmissionError::StaleAdmission));
    assert_eq!(admitted.phase(client), Some(Phase::Loading));
    assert_eq!(admitted.inverse_count(client), Some(0));
    assert_eq!(admitted.read(replacement, key()), Some(7));
    assert!(!admitted.is_consumed());
    let mut driver = admitted.into_driver();
    driver.step(client).unwrap();
    assert_eq!(driver.read(replacement, key()), Some(7 ^ 5));
}

#[test]
fn coherent_terminal_failure_keeps_pending_ticket_payload_journal_and_allocator() {
    let saved = Port { key: 8, realm: 3 };
    let leaf = Blueprint::new(vec![], vec![], vec![Instruction::Unit]);
    let incomplete = Blueprint::new(
        vec![],
        vec![key(), saved],
        vec![
            Instruction::Provide {
                key: saved,
                value: 55,
                next: Some(1),
            },
            Instruction::Child {
                blueprint: 0,
                next: None,
            },
        ],
    );
    let mut driver = FreshDriver::new(vec![leaf, incomplete]);
    let actor = driver.insert(None, 1).unwrap();
    driver.begin(actor).unwrap();
    driver.step(actor).unwrap();
    let mut admitted = admit(driver, actor);
    assert_eq!(
        admitted.land(),
        Err(AdmissionError::Driver(DriverError::IncompleteProvision))
    );
    assert_eq!(
        admitted.land(),
        Err(AdmissionError::Driver(DriverError::IncompleteProvision))
    );
    assert!(!admitted.is_consumed());
    assert_eq!(admitted.phase(actor), Some(Phase::Loading));
    assert_eq!(admitted.inverse_count(actor), Some(1));
    assert_eq!(admitted.read(actor, saved), Some(55));
    assert_eq!(admitted.phase(1), None);
    let mut driver = admitted.into_driver();
    assert_eq!(driver.insert(None, 0), Ok(1));
}

#[test]
fn admission_rejection_returns_the_same_owned_machine() {
    let (mut driver, provider, client) = setup();
    driver.retire(provider).unwrap();
    driver.depart(provider).unwrap();
    let rejected = match driver.admit(client) {
        Err(rejected) => rejected,
        Ok(_) => panic!("target loss must reject new admission"),
    };
    assert_eq!(
        rejected.error,
        AdmissionError::Driver(DriverError::Kernel(Error::Changed))
    );
    assert_eq!(rejected.machine.phase(client), Some(Phase::Loading));
    assert_eq!(rejected.machine.inverse_count(client), Some(0));
    assert_eq!(rejected.machine.read(provider, key()), Some(7));
}
