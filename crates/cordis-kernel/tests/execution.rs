use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
use cordis_kernel::effect_work::EffectOutput;
use cordis_kernel::execution::{Execution, ExecutionPhase};
use cordis_kernel::lifecycle_state::native::NativeHost;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::lifecycle_state::services::{NativeServices, NativeValueError};
use cordis_kernel::{Error, Phase, Port};
use std::collections::BTreeMap;
use std::sync::Arc;

type Owner = Execution<String, String, String, String>;
type Host = NativeHost<fn(u64) -> Result<(), String>, ()>;
fn setup(argument: u64) -> Result<(), String> {
    assert_eq!(argument, 42);
    Ok(())
}
fn registered(domain: u64) -> (Host, NativeServices<String>, usize) {
    let mut host = Host::new(domain);
    let owner = host
        .register(
            None,
            &BTreeMap::new(),
            Port { key: 100, realm: 0 },
            PluginDefinition::new(vec![], vec![1], setup as fn(u64) -> Result<(), String>),
            (),
        )
        .ok()
        .unwrap();
    (host, NativeServices::new(domain), owner)
}
fn complete_root(host: &mut Host, owner: usize, execution: &mut Owner) {
    let invocation = host.admit_managed_root(owner, execution, 42).unwrap();
    let reply = host.call(owner, invocation).ok().unwrap();
    execution.complete_root(reply).ok().unwrap().unwrap();
}
fn port() -> Port {
    Port { key: 1, realm: 0 }
}
fn active(domain: u64) -> (Host, NativeServices<String>, usize, Owner) {
    let (mut host, mut store, owner) = registered(domain);
    let mut execution = host
        .begin_managed_execution(owner, &store, domain + 1)
        .unwrap();
    complete_root(&mut host, owner, &mut execution);
    execution
        .provide(port(), Arc::new("actual service".into()))
        .unwrap();
    host.finish_managed_execution(owner, &mut store, &mut execution)
        .unwrap();
    (host, store, owner, execution)
}
fn withdraw(host: &mut Host, owner: usize, execution: &mut Owner) {
    host.withdraw_managed_execution(owner, execution, false)
        .unwrap();
    host.settle_managed_execution(owner, execution).unwrap();
    host.begin_cleanup(owner).unwrap();
}
fn external(domain: u64) -> Owner {
    let mut execution = Owner::new(domain);
    let item = execution.issue_root(()).unwrap();
    execution
        .complete_root(item.run(|()| Ok::<_, String>(())))
        .ok()
        .unwrap()
        .unwrap();
    execution
}
fn dispatch(execution: &mut Owner) {
    let item = execution.take_group().unwrap();
    let receipt = item.run(|request| execution.activate_effect(request));
    assert!(execution.complete_request(receipt).ok().unwrap().is_ok());
}

#[test]
fn native_publication_and_phase_change_together() {
    let (mut host, mut store, owner) = registered(1200);
    let mut execution: Owner = host.begin_managed_execution(owner, &store, 1201).unwrap();
    assert_eq!(execution.phase(), ExecutionPhase::Loading);
    assert!(!execution.activate_external());
    assert_eq!(
        host.finish_managed_execution(owner, &mut store, &mut execution),
        Err(Error::InvalidState)
    );
    complete_root(&mut host, owner, &mut execution);
    assert_eq!(
        host.finish_managed_execution(owner, &mut store, &mut execution),
        Err(Error::InvalidState)
    );
    assert_eq!(execution.phase(), ExecutionPhase::Loading);
    assert!(!store.has_publications());
    let value = Arc::new("same allocation".to_owned());
    execution.provide(port(), value.clone()).unwrap();
    host.finish_managed_execution(owner, &mut store, &mut execution)
        .unwrap();
    assert_eq!(execution.phase(), ExecutionPhase::Active);
    assert_eq!(host.kernel().phase(owner), Some(Phase::Active));
    assert!(Arc::ptr_eq(
        host.native_value(&store, port()).unwrap(),
        &value
    ));
    assert!(!execution.seal_external());
    assert_eq!(execution.phase(), ExecutionPhase::Active);
}

#[test]
fn release_closes_values_work_and_phase_and_rejects_old_episode() {
    let (mut host, mut store, owner, mut execution) = active(1210);
    withdraw(&mut host, owner, &mut execution);
    let retained = execution.read(port()).unwrap().1.clone();
    let (_, values) = host
        .release_managed_execution(owner, &mut store, &mut execution)
        .unwrap();
    assert_eq!(execution.phase(), ExecutionPhase::Closed);
    assert_eq!(host.kernel().phase(owner), Some(Phase::Inactive));
    assert!(Arc::ptr_eq(values.owned.get(&(1, 0)).unwrap(), &retained));
    assert_eq!(
        execution.read(port()).unwrap_err().reason,
        NativeValueError::Closed
    );
    assert!(execution.issue_root(()).is_err());
    assert!(!execution.accepts_acquisition(0));
    let mut next: Owner = host.begin_managed_execution(owner, &store, 1212).unwrap();
    complete_root(&mut host, owner, &mut next);
    next.provide(port(), Arc::new("new service".into()))
        .unwrap();
    host.finish_managed_execution(owner, &mut store, &mut next)
        .unwrap();
    assert!(host
        .release_managed_execution(owner, &mut store, &mut execution)
        .is_err());
    assert_eq!(next.phase(), ExecutionPhase::Active);
    assert_eq!(
        host.native_value(&store, port()).unwrap().as_str(),
        "new service"
    );
}

#[test]
fn retained_failure_and_fresh_retry_preserve_the_same_value_owner() {
    let (mut host, mut store, owner, mut execution) = active(1220);
    execution.register(0, "cleanup".into()).unwrap();
    withdraw(&mut host, owner, &mut execution);
    let (old_ticket, payload) = execution.pop(0).unwrap().unwrap();
    execution
        .complete_result(
            0,
            old_ticket,
            Err("failed"),
            Some(payload),
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    host.fail_managed_execution(owner, &execution).unwrap();
    assert!(host
        .release_managed_execution(owner, &mut store, &mut execution)
        .is_err());
    assert_eq!(execution.phase(), ExecutionPhase::Restoring);
    assert_eq!(execution.read(port()).unwrap().1.as_str(), "actual service");
    host.retry_managed_execution(owner, &mut execution).unwrap();
    let (current, _) = execution.pop(0).unwrap().unwrap();
    assert_ne!(old_ticket, current);
    assert!(execution
        .complete_result(
            0,
            old_ticket,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
    assert!(execution.has_issued());
    execution
        .complete_result(
            0,
            current,
            Ok::<_, &str>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    host.release_managed_execution(owner, &mut store, &mut execution)
        .unwrap();
    assert_eq!(execution.phase(), ExecutionPhase::Closed);
}

#[test]
fn runner_ownership_rejects_foreign_return_and_keeps_real_payload() {
    let mut a = external(1230);
    let mut b = external(1240);
    let id = a
        .enqueue_effect(0, 1231, vec![], "actual iterator".into())
        .unwrap();
    b.enqueue_effect(0, 1241, vec![], "other iterator".into())
        .unwrap();
    dispatch(&mut a);
    dispatch(&mut b);
    let run = a.take_effect(id).unwrap();
    let rejected = b.put_effect(run).err().unwrap();
    assert_eq!(rejected.get(), "actual iterator");
    assert_eq!(b.effects().get(&id).unwrap().get(), "other iterator");
    assert!(a.put_effect(rejected).is_ok());
    a.cancel(id);
    assert!(!a.remove(id)); // The live runner is still owned.
    assert!(!a.seal_external());
    let run = a.take_effect(id).unwrap();
    assert!(!a.remove(id));
    assert!(!a.seal_external());
    let actual = a.retire_effect(run).ok().unwrap();
    assert_eq!(actual, "actual iterator");
    assert!(a.seal_external());
}

#[test]
fn withdrawal_keeps_an_inflight_inverse_and_blocks_new_work() {
    let mut execution = external(1250);
    let id = execution
        .enqueue_effect(0, 1251, vec![], "poll payload".into())
        .unwrap();
    dispatch(&mut execution);
    let mut run = execution.take_effect(id).unwrap();
    assert!(execution.admit_effect(&mut run, Some(&[])));
    execution.withdraw();
    execution.cancel(id);
    assert!(execution
        .enqueue_effect(0, 1252, vec![], "too late".into())
        .is_err());
    assert!(!execution.seal_external());
    let (mut run, reply) = run
        .call((), |payload, ()| {
            (
                payload,
                EffectOutput::<String, String>::Ready(Ok(Some("actual inverse".into()))),
            )
        })
        .ok()
        .unwrap();
    let report = execution
        .land_effect(&mut run, reply)
        .ok()
        .unwrap()
        .unwrap();
    assert!(!report.continue_iteration);
    let (ticket, inverse) = execution.pop(id).unwrap().unwrap();
    assert_eq!(inverse, "actual inverse");
    assert!(!execution.seal_external());
    execution
        .complete_result(
            id,
            ticket,
            Ok::<_, String>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .unwrap();
    assert!(!execution.remove(id));
    assert!(!execution.seal_external());
    assert_eq!(execution.retire_effect(run).ok().unwrap(), "poll payload");
    assert!(execution.seal_external());
}

#[test]
fn dispatched_request_and_abandoned_root_prevent_release() {
    let mut execution = external(1260);
    execution
        .enqueue_effect(0, 1261, vec![], "queued".into())
        .unwrap();
    let item = execution.take_group().unwrap();
    execution.withdraw();
    execution.cancel(1);
    assert!(!execution.seal_external()); // Empty dispatch queue still has issued work.
    let reply = item.run(|request| execution.activate_effect(request));
    assert!(execution.complete_request(reply).ok().unwrap().is_ok());
    let run = execution.take_effect(1).unwrap();
    assert!(!execution.remove(1));
    assert!(!execution.seal_external());
    assert_eq!(execution.retire_effect(run).ok().unwrap(), "queued");
    assert!(execution.seal_external());
    let mut abandoned = Owner::new(1270);
    let item = abandoned.issue_root(()).unwrap();
    assert!(abandoned.start_root(item.ticket()));
    abandoned.abandon_root();
    assert_eq!(abandoned.phase(), ExecutionPhase::Restoring);
    assert!(!abandoned.seal_external());
    assert!(!abandoned.activate_external());
}

#[test]
fn abandoned_checkout_cannot_be_mistaken_for_an_empty_owner() {
    let mut execution = external(1280);
    let id = execution
        .enqueue_effect(0, 1281, vec![], "held".into())
        .unwrap();
    dispatch(&mut execution);
    let run = execution.take_effect(id).unwrap();
    execution.cancel(id);
    assert!(execution.effects().is_empty());
    assert!(execution.groups().can_seal());
    assert!(!execution.can_finish(&[]));
    assert!(!execution.remove(id));
    assert!(!execution.seal_external());
    drop(run);
    assert!(!execution.remove(id));
    assert!(!execution.seal_external());
}

#[test]
fn managed_withdrawal_rejects_foreign_episode_and_closes_admission() {
    let (mut host, _, owner, mut execution) = active(1290);
    let (_, _, _, mut foreign) = active(1300);
    assert_eq!(
        host.withdraw_managed_execution(owner, &mut foreign, true),
        Err(Error::InvalidState)
    );
    assert!(!host.kernel().retired(owner));
    assert_eq!(foreign.phase(), ExecutionPhase::Active);
    host.withdraw_managed_execution(owner, &mut execution, true)
        .unwrap();
    assert!(host.kernel().retired(owner));
    assert_eq!(execution.phase(), ExecutionPhase::Restoring);
    assert!(!execution.accepts_acquisition(0));
    assert_eq!(execution.read(port()).unwrap().1.as_str(), "actual service");
    assert!(execution
        .enqueue_effect(0, 1292, vec![], "too late".into())
        .is_err());
}
