use cordis_kernel::mixed_driver::fresh::admitted::script::{
    run_script, Effect, ScriptAction, ScriptError,
};
use cordis_kernel::mixed_driver::fresh::admitted::AdmissionError;
use cordis_kernel::mixed_driver::fresh::{Blueprint, Command, Instruction, Outcome};
use cordis_kernel::{Phase, Port};

fn key() -> Port {
    Port { key: 11, realm: 2 }
}
fn leaf() -> Blueprint {
    Blueprint::new(vec![], vec![], vec![Instruction::Unit])
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
fn xor_user() -> Blueprint {
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
fn call(command: Command) -> ScriptAction {
    ScriptAction::Call(command)
}

#[test]
fn admitted_xor_lands_after_target_loss_and_actual_unload_restores_old_provider() {
    use Command::*;
    let actions = [
        call(Insert {
            parent: None,
            blueprint: 0,
        }),
        call(Begin { actor: 0 }),
        call(Step { actor: 0 }),
        call(Insert {
            parent: None,
            blueprint: 1,
        }),
        call(Begin { actor: 1 }),
        ScriptAction::Admit { actor: 1 },
        call(Retire { actor: 0 }),
        call(Depart { actor: 0 }),
        ScriptAction::Land,
        ScriptAction::Release,
        call(Unload { actor: 1 }),
    ];
    let landed = run_script(vec![provider(), xor_user()], &actions[..9]);
    assert_eq!(landed.error, None);
    assert_eq!(landed.completed, 9);
    assert_eq!(landed.machine.phase(1), Some(Phase::Unloading));
    assert_eq!(landed.machine.read(0, key()), Some(7 ^ 5));
    assert_eq!(landed.machine.inverse_count(1), Some(1));
    let Effect::Land(effect) = landed.events.last().unwrap().effect else {
        panic!("missing landing")
    };
    assert!(effect.diverted);
    assert_eq!(effect.outcome, Outcome::Finished);
    assert_eq!(landed.events.last().unwrap().action_index, 8);

    let restored = run_script(vec![provider(), xor_user()], &actions);
    assert_eq!(restored.error, None);
    assert_eq!(restored.completed, actions.len());
    assert_eq!(restored.events.len(), actions.len() - 2);
    assert_eq!(restored.machine.read(0, key()), Some(7));
    assert_eq!(restored.machine.phase(1), Some(Phase::Inactive));
    assert_eq!(restored.machine.inverse_count(1), Some(0));
}

fn child_bank() -> Vec<Blueprint> {
    vec![
        leaf(),
        provider(),
        Blueprint::new(
            vec![key()],
            vec![],
            vec![Instruction::Child {
                blueprint: 0,
                next: None,
            }],
        ),
    ]
}

#[test]
fn admitted_child_allocates_at_landing_and_its_receipt_is_recovered_after_divert() {
    use Command::*;
    let actions = [
        call(Insert {
            parent: None,
            blueprint: 1,
        }),
        call(Begin { actor: 0 }),
        call(Step { actor: 0 }),
        call(Insert {
            parent: None,
            blueprint: 2,
        }),
        call(Begin { actor: 1 }),
        ScriptAction::Admit { actor: 1 },
        call(Insert {
            parent: None,
            blueprint: 0,
        }),
        call(Retire { actor: 0 }),
        call(Depart { actor: 0 }),
        ScriptAction::Land,
        ScriptAction::Release,
        call(Unload { actor: 1 }),
        call(Remove { actor: 3 }),
    ];
    let landed = run_script(child_bank(), &actions[..10]);
    assert_eq!(landed.error, None);
    let Effect::Land(effect) = landed.events.last().unwrap().effect else {
        panic!("missing landing")
    };
    assert!(effect.diverted);
    assert_eq!(
        effect.outcome,
        Outcome::Child {
            child: 3,
            finished: true
        }
    );
    assert_eq!(landed.machine.phase(3), Some(Phase::Inactive));
    assert_eq!(landed.machine.inverse_count(1), Some(1));

    let restored = run_script(child_bank(), &actions);
    assert_eq!(restored.error, None);
    assert_eq!(restored.machine.phase(3), None);
    assert_eq!(restored.machine.phase(2), Some(Phase::Inactive));
    assert_eq!(restored.machine.phase(1), Some(Phase::Inactive));
    assert_eq!(restored.machine.inverse_count(1), Some(0));
}

#[test]
fn same_actor_progress_rejects_the_old_pc_and_preserves_the_successful_prefix() {
    use Command::*;
    let code = Blueprint::new(
        vec![],
        vec![key()],
        vec![
            Instruction::Provide {
                key: key(),
                value: 7,
                next: Some(1),
            },
            Instruction::Xor {
                key: key(),
                mask: 5,
                next: None,
            },
        ],
    );
    let report = run_script(
        vec![code],
        &[
            call(Insert {
                parent: None,
                blueprint: 0,
            }),
            call(Begin { actor: 0 }),
            ScriptAction::Admit { actor: 0 },
            call(Step { actor: 0 }),
            ScriptAction::Land,
            call(Retire { actor: 0 }),
        ],
    );
    assert_eq!(
        report.error,
        Some(ScriptError::Admission(AdmissionError::StaleAdmission))
    );
    assert_eq!(report.completed, 4);
    assert_eq!(report.events.len(), 3);
    assert_eq!(report.machine.phase(0), Some(Phase::Loading));
    assert_eq!(report.machine.read(0, key()), Some(7));
    assert_eq!(report.machine.inverse_count(0), Some(1));
    assert!(!report.machine.retired(0));
}

#[test]
fn a_new_episode_at_the_same_pc_cannot_use_the_previous_admission() {
    use Command::*;
    let report = run_script(
        vec![provider(), xor_user()],
        &[
            call(Insert {
                parent: None,
                blueprint: 0,
            }),
            call(Begin { actor: 0 }),
            call(Step { actor: 0 }),
            call(Insert {
                parent: None,
                blueprint: 1,
            }),
            call(Begin { actor: 1 }),
            ScriptAction::Admit { actor: 1 },
            call(Retire { actor: 0 }),
            call(Depart { actor: 0 }),
            call(Depart { actor: 1 }),
            call(Unload { actor: 1 }),
            call(Unload { actor: 0 }),
            call(Remove { actor: 0 }),
            call(Insert {
                parent: None,
                blueprint: 0,
            }),
            call(Begin { actor: 2 }),
            call(Step { actor: 2 }),
            call(Begin { actor: 1 }),
            ScriptAction::Land,
        ],
    );
    assert_eq!(
        report.error,
        Some(ScriptError::Admission(AdmissionError::StaleAdmission))
    );
    assert_eq!(report.completed, 16);
    assert_eq!(report.events.len(), 15);
    assert_eq!(report.machine.phase(1), Some(Phase::Loading));
    assert_eq!(report.machine.read(2, key()), Some(7));
    assert_eq!(report.machine.inverse_count(1), Some(0));
}

#[test]
fn metadata_release_adds_no_source_event_and_landing_requires_an_owned_session() {
    use Command::*;
    let released = run_script(
        vec![leaf()],
        &[
            call(Insert {
                parent: None,
                blueprint: 0,
            }),
            call(Begin { actor: 0 }),
            ScriptAction::Admit { actor: 0 },
            ScriptAction::Release,
            call(Step { actor: 0 }),
        ],
    );
    assert_eq!(released.error, None);
    assert_eq!(released.completed, 5);
    assert_eq!(
        released
            .events
            .iter()
            .map(|event| event.action_index)
            .collect::<Vec<_>>(),
        vec![0, 1, 4]
    );
    assert_eq!(released.machine.phase(0), Some(Phase::Active));

    let absent = run_script(vec![leaf()], &[ScriptAction::Land]);
    assert_eq!(absent.error, Some(ScriptError::NotAdmitted));
    assert_eq!(absent.completed, 0);
    assert!(absent.events.is_empty());

    let consumed = run_script(
        vec![leaf()],
        &[
            call(Insert {
                parent: None,
                blueprint: 0,
            }),
            call(Begin { actor: 0 }),
            ScriptAction::Admit { actor: 0 },
            ScriptAction::Land,
            ScriptAction::Land,
        ],
    );
    assert_eq!(
        consumed.error,
        Some(ScriptError::Admission(AdmissionError::StaleAdmission))
    );
    assert_eq!(consumed.completed, 4);
    assert_eq!(consumed.events.len(), 3);
    assert_eq!(consumed.machine.inverse_count(0), Some(1));
}
