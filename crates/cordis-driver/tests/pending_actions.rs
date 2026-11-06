use cordis_driver::shared::{CleanupOutcome, LifecycleDriver};
use cordis_driver::{ActionKind, ActionTicket};
use cordis_kernel::action_ledger::{ActionKind as KernelKind, ActionTicket as KernelTicket};
use cordis_kernel::availability::Availability;
use cordis_kernel::cleanup_groups::CleanupGroups;
use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::lifecycle_state::services::NativeServices;
use cordis_kernel::publication::values::PublicationStore;
use cordis_kernel::setup_work::SetupWork;
use cordis_kernel::{Error, Phase, Port};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

type Work = SetupWork<String, String>;
type Groups = CleanupGroups<String>;

fn root(work: &mut Work) {
    let item = work.issue_root("input".to_owned()).ok().unwrap();
    let receipt = item.run(|_| Ok::<(), String>(()));
    work.complete_root(receipt).ok().unwrap().unwrap();
}

// Compare against the ticket issued with the actual owner/admission, including
// the decimal wire representation. This is behavioral evidence for the adapter.
fn observed(driver: &LifecycleDriver, id: usize, ticket: KernelTicket) -> ActionTicket {
    let view = driver.pending_action(id).unwrap();
    assert_eq!(
        (view.domain, view.id, view.generation, view.action),
        (ticket.domain, ticket.id, ticket.generation, ticket.action)
    );
    assert_eq!(
        view.kind,
        match ticket.kind {
            KernelKind::Setup => ActionKind::Setup,
            KernelKind::Cleanup => ActionKind::Cleanup,
        }
    );
    let wire = serde_json::to_value(&view).unwrap();
    assert_eq!(
        wire,
        serde_json::json!({
            "domain": ticket.domain.to_string(), "id": ticket.id.to_string(),
            "generation": ticket.generation.to_string(), "action": ticket.action.to_string(),
            "kind": if ticket.kind == KernelKind::Setup {"setup"} else {"cleanup"},
        })
    );
    assert_eq!(serde_json::from_value::<ActionTicket>(wire).unwrap(), view);
    view
}

#[test]
fn execution_views_follow_real_failure_retry_release_and_next_generation() {
    let mut driver = LifecycleDriver::new().unwrap();
    let id = driver.insert(None, vec![], vec![]).unwrap();
    let other = driver.insert(None, vec![], vec![]).unwrap();
    driver.begin(other).unwrap();
    let other_ticket = driver.pending_action(other).unwrap();
    let (mut work, mut groups): (Work, Groups) = driver.begin_execution(id, 801).unwrap();
    let setup = observed(&driver, id, work.lifecycle_ticket().unwrap());
    assert_eq!(
        driver.finish_execution(id, &work, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(driver.pending_action(id).as_ref(), Some(&setup));
    root(&mut work);
    groups.register(0, "retry inverse".to_owned()).unwrap();
    driver.finish_execution(id, &work, &groups).unwrap();
    assert!(driver.pending_action(id).is_none());
    driver.leave(id).unwrap();
    work.withdraw();
    groups.cancel(0);
    driver.settle_execution(id, &work, &groups).unwrap();
    driver.begin_cleanup(id).unwrap();
    let failed = driver.pending_action(id).unwrap();
    let (ticket, inverse) = groups.pop(0).unwrap().unwrap();
    groups
        .complete_result(
            0,
            ticket,
            Err("injected failure"),
            Some(inverse),
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    driver.fail_execution(id, &work, &groups).unwrap();
    assert!(driver.pending_action(id).is_none());
    assert_eq!(
        driver.release_execution(id, &mut work, &mut groups),
        Err(Error::InvalidState)
    );
    let retry = driver.retry_execution(id, &work, &mut groups).unwrap();
    assert!(retry.action > failed.action);
    assert_eq!(driver.pending_action(id).as_ref(), Some(&retry));
    assert_eq!(
        driver
            .complete_cleanup(&failed, CleanupOutcome::Succeeded)
            .unwrap_err()
            .code,
        "StaleAction"
    );
    assert_eq!(driver.pending_action(id).as_ref(), Some(&retry));
    let (ticket, _) = groups.pop(0).unwrap().unwrap();
    groups
        .complete_result(
            0,
            ticket,
            Ok::<(), &str>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    assert_eq!(
        driver.release_execution(id, &mut work, &mut groups),
        Ok(CleanupOutcome::Succeeded)
    );
    assert!(driver.pending_action(id).is_none());
    let (next, _next_groups): (Work, Groups) = driver.begin_execution(id, 802).unwrap();
    let current = observed(&driver, id, next.lifecycle_ticket().unwrap());
    assert!(current.generation > setup.generation && current.action > retry.action);
    assert_eq!(
        driver.complete_action(&setup).unwrap_err().code,
        "StaleAction"
    );
    assert_eq!(
        driver.settle_execution(id, &work, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(driver.pending_action(id).as_ref(), Some(&current));
    assert_eq!(driver.pending_action(other).as_ref(), Some(&other_ticket));
}

#[test]
fn failed_finish_can_settle_the_ticket_without_activating_the_episode() {
    let mut driver = LifecycleDriver::new().unwrap();
    let id = driver.insert(None, vec![], vec![]).unwrap();
    let (mut work, groups): (Work, Groups) = driver.begin_execution(id, 811).unwrap();
    let setup = observed(&driver, id, work.lifecycle_ticket().unwrap());
    root(&mut work);
    // The work remains complete; the actual lifecycle has withdrawn first.
    driver.leave(id).unwrap();
    assert_eq!(driver.pending_action(id).as_ref(), Some(&setup));
    assert_eq!(
        driver.finish_execution(id, &work, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(driver.phase(id), Some(Phase::Unloading));
    assert!(driver.pending_action(id).is_none());
    assert_eq!(
        driver.complete_action(&setup).unwrap_err().code,
        "StaleAction"
    );
    driver.begin_cleanup(id).unwrap();
    let cleanup = driver.pending_action(id).unwrap();
    driver
        .complete_cleanup(&cleanup, CleanupOutcome::Succeeded)
        .unwrap();
    driver.finish_cleanup(id).unwrap();
    driver.retire(id).unwrap();
    driver.remove(id).unwrap();
    assert!(driver.pending_action(id).is_none());
}

#[test]
fn native_publication_views_follow_actual_setup_and_release() {
    let mut driver = LifecycleDriver::new().unwrap();
    let port = Port { key: 7, realm: 0 };
    let registration = driver
        .register_plugin(
            None,
            &BTreeMap::new(),
            Port {
                key: 8000,
                realm: 0,
            },
            PluginDefinition::new(vec![], vec![7], ()),
        )
        .ok()
        .unwrap();
    let id = registration.id();
    let mut store = NativeServices::<String>::new(driver.domain());
    let (mut work, mut groups, mut values): (Work, Groups, _) = driver
        .begin_native_execution(&store, &registration, 821)
        .unwrap();
    let setup = observed(&driver, id, values.ticket());
    root(&mut work);
    assert_eq!(
        driver.finish_native_execution(id, &mut store, &values, &work, &groups),
        Err(Error::InvalidState)
    );
    assert_eq!(driver.pending_action(id).as_ref(), Some(&setup));
    values
        .provide(port, Arc::new("published".to_owned()))
        .unwrap();
    driver
        .finish_native_execution(id, &mut store, &values, &work, &groups)
        .unwrap();
    assert!(driver.pending_action(id).is_none());
    assert_eq!(
        driver.native_value(&store, port).unwrap().as_str(),
        "published"
    );
    driver.leave(id).unwrap();
    work.withdraw();
    driver.begin_cleanup(id).unwrap();
    assert_eq!(driver.pending_action(id).unwrap().kind, ActionKind::Cleanup);
    let (outcome, _) = driver
        .release_native_execution(id, &mut store, &mut values, &mut work, &mut groups)
        .unwrap();
    assert_eq!(outcome, CleanupOutcome::Succeeded);
    assert!(driver.pending_action(id).is_none());
    assert_eq!(store.value_count(), 0);
}

#[test]
fn checked_admission_views_survive_rejection_and_end_after_resource_release() {
    let mut driver = LifecycleDriver::new().unwrap();
    let id = driver.insert(None, vec![], vec![]).unwrap();
    let mut store = PublicationStore::for_domain(driver.domain());
    let availability = Availability::new(driver.domain());
    let checked = BTreeSet::new();
    let admission = driver
        .begin_checked(id, &mut store, &availability, &checked)
        .unwrap();
    let setup = observed(&driver, id, admission.ticket());
    assert!(driver
        .begin_checked(id, &mut store, &availability, &checked)
        .is_err());
    assert_eq!(driver.pending_action(id).as_ref(), Some(&setup));
    driver.settle_setup(id).unwrap();
    assert!(driver.pending_action(id).is_none());
    driver.finish(id).unwrap();
    driver.retire(id).unwrap();
    driver.leave(id).unwrap();
    driver.begin_cleanup(id).unwrap();
    let failed = driver.pending_action(id).unwrap();
    driver
        .complete_cleanup(&failed, CleanupOutcome::Failed)
        .unwrap();
    assert!(driver.pending_action(id).is_none());
    assert!(driver
        .finish_admission_values(&mut store, &admission, &[])
        .is_err());
    let retry = driver.retry_cleanup(id).unwrap();
    assert_eq!(driver.pending_action(id).as_ref(), Some(&retry));
    assert_eq!(
        driver
            .complete_cleanup(&failed, CleanupOutcome::Succeeded)
            .unwrap_err()
            .code,
        "StaleAction"
    );
    assert_eq!(driver.pending_action(id).as_ref(), Some(&retry));
    driver
        .complete_cleanup(&retry, CleanupOutcome::Succeeded)
        .unwrap();
    assert!(driver.pending_action(id).is_none());
    driver
        .finish_admission_values(&mut store, &admission, &[])
        .unwrap();
    driver.remove(id).unwrap();
    assert!(driver.pending_action(id).is_none());
}
