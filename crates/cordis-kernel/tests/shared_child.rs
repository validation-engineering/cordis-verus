use cordis_kernel::cleanup_groups::CleanupGroups;
use cordis_kernel::cleanup_journal::RestoreOutcome;
use cordis_kernel::lifecycle_state::native::NativeHost;
use cordis_kernel::lifecycle_state::registration::shared_child::{
    ChildCleanup, ChildDispatch, ChildTransition, SharedChild,
};
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::lifecycle_state::services::{NativeEpisode, NativeServices};
use cordis_kernel::setup_work::SetupWork;
use cordis_kernel::{Error, Port};
use std::collections::BTreeMap;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    mpsc, Arc, Barrier,
};
use std::time::Duration;

type Host = NativeHost<String, String>;
type Work<P = String> = SetupWork<ChildDispatch<P, ()>, ()>;
type Groups = CleanupGroups<ChildCleanup<(), ()>>;
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn setup(
    domain: u64,
) -> (
    Host,
    usize,
    Work,
    Groups,
    NativeServices<u64>,
    NativeEpisode<u64>,
) {
    let mut host = Host::new(domain);
    let parent = host
        .register(
            None,
            &BTreeMap::new(),
            port(1),
            PluginDefinition::new(vec![], vec![], "parent recipe".into()),
            "parent host".into(),
        )
        .ok()
        .unwrap();
    let store = NativeServices::new(domain);
    let (mut work, groups, values): (Work, Groups, _) = host
        .begin_native_execution(parent, &store, domain + 1)
        .unwrap();
    let receipt = work.issue_root(()).unwrap().run(|()| Ok::<(), ()>(()));
    work.complete_root(receipt).ok().unwrap().unwrap();
    (host, parent, work, groups, store, values)
}
#[allow(clippy::type_complexity)]
fn allocate(
    host: &mut Host,
    child: &SharedChild,
    key: u64,
    recipe: &str,
) -> ChildTransition<Result<usize, (Error, PluginDefinition<String>, String)>> {
    host.register_shared_child(
        child,
        &BTreeMap::new(),
        port(key),
        PluginDefinition::new(vec![], vec![], recipe.into()),
        format!("{recipe} host"),
    )
}
fn take_request(work: &mut Work) -> (String, SharedChild) {
    let mut actual = None;
    let receipt = work.take_child().unwrap().run(|request| {
        let ChildDispatch::Native(request) = request else {
            panic!("native request")
        };
        actual = Some(request.into_parts());
    });
    work.complete_request(receipt).ok().unwrap();
    actual.unwrap()
}
#[allow(clippy::type_complexity)]
fn restore_inverse(
    host: &mut Host,
    groups: &mut Groups,
) -> (
    SharedChild,
    ChildTransition<
        Result<Option<cordis_kernel::lifecycle_state::registration::ChildIdentity>, Error>,
    >,
) {
    let (ticket, action) = groups.pop(0).unwrap().unwrap();
    let ChildCleanup::Native(child) = action else {
        panic!("native inverse")
    };
    let report = host.retire_shared_child(&child);
    // Feed the actual operation result back into its issued cleanup ticket.
    groups
        .complete_result(
            0,
            ticket,
            report.result.map(|_| ()),
            None,
            cordis_kernel::cleanup_queue::completion::CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    (child, report)
}

#[test]
fn checked_pair_keeps_fifo_requests_lifo_inverses_and_actual_payloads_distinct() {
    let (mut host, parent, mut work, mut groups, _, _) = setup(700);
    let (first, first_token) = work
        .enqueue_native_child(&mut groups, 0, "first".into())
        .ok()
        .unwrap();
    let (second, second_token) = work
        .enqueue_native_child(&mut groups, 0, "second".into())
        .ok()
        .unwrap();
    assert_ne!(first_token, second_token);
    assert_eq!(first.domain(), 700);
    assert_eq!(first.parent_id(), parent);
    assert_eq!(
        first.generation(),
        work.lifecycle_ticket().map(|t| t.generation)
    );
    let (payload, request) = take_request(&mut work);
    assert_eq!(payload, "first");
    let registered = allocate(&mut host, &request, 2, &payload);
    assert!(registered.before.pending());
    let id = registered.result.ok().unwrap();
    assert_eq!(first.snapshot().identity().unwrap().id(), id);
    assert!(second.snapshot().pending());
    assert_eq!(host.host(id).unwrap(), "first host");
    let (_, retired) = restore_inverse(&mut host, &mut groups);
    assert!(retired.after.cancelled());
    assert!(second.snapshot().cancelled());
    assert!(!host.kernel().retired(id));
    let (_, retired) = restore_inverse(&mut host, &mut groups);
    assert_eq!(retired.result.unwrap().unwrap().id(), id);
    assert!(host.kernel().retired(id));
    assert!(!host.kernel().retired(parent));
}

#[test]
fn cleanup_before_dispatch_cancels_the_exact_request_without_late_allocation() {
    let (mut host, parent, mut work, mut groups, _, _) = setup(710);
    let (handle, _) = work
        .enqueue_native_child(&mut groups, 0, "retained recipe".into())
        .ok()
        .unwrap();
    let (_, retired) = restore_inverse(&mut host, &mut groups);
    assert!(retired.before.pending());
    assert!(retired.after.cancelled());
    assert_eq!(retired.result, Ok(None));
    let (recipe, request) = take_request(&mut work);
    let result = allocate(&mut host, &request, 2, &recipe);
    assert!(result.before.cancelled() && result.after.cancelled());
    let (error, definition, bookkeeping) = result.result.err().unwrap();
    assert_eq!(error, Error::InvalidState);
    assert_eq!(definition.into_payload(), "retained recipe");
    assert_eq!(bookkeeping, "retained recipe host");
    assert_eq!(host.ids(), vec![parent]);
    assert!(!handle.reject().result);
    assert!(handle.snapshot().cancelled());
}

#[test]
fn failed_and_assigned_slots_never_return_to_pending_or_accept_replacement() {
    let (mut host, parent, mut work, mut groups, _, _) = setup(720);
    let (failed, _) = work
        .enqueue_native_child(&mut groups, 0, "failed".into())
        .ok()
        .unwrap();
    let rejected = failed.reject();
    assert!(rejected.result && rejected.before.pending() && rejected.after.failed());
    assert!(!failed.clone().reject().result);
    assert!(allocate(&mut host, &failed, 2, "unaccepted")
        .result
        .is_err());
    assert!(host.retire_shared_child(&failed).after.failed());
    assert_eq!(host.ids(), vec![parent]);
    let (assigned, _) = work
        .enqueue_native_child(&mut groups, 0, "assigned".into())
        .ok()
        .unwrap();
    let id = allocate(&mut host, &assigned, 3, "real")
        .result
        .ok()
        .unwrap();
    assert!(!assigned.reject().result);
    assert!(allocate(&mut host, &assigned, 4, "replacement")
        .result
        .is_err());
    assert_eq!(assigned.snapshot().identity().unwrap().id(), id);
    assert_eq!(host.host(id).unwrap(), "real host");
    host.retire_shared_child(&assigned).result.unwrap();
    host.remove(id).ok().unwrap();
    let repeat = host.retire_shared_child(&assigned);
    assert_eq!(repeat.result.unwrap().unwrap().id(), id);
    assert_eq!(repeat.after.identity().unwrap().id(), id);
}

#[test]
fn foreign_runtime_and_obsolete_episode_do_not_mutate_or_allocate() {
    let (mut host, parent, mut work, mut groups, mut store, mut values) = setup(730);
    let (mut foreign, foreign_parent, _, _, _, _) = setup(740);
    assert_eq!(parent, foreign_parent);
    let (child, _) = work
        .enqueue_native_child(&mut groups, 0, "late".into())
        .ok()
        .unwrap();
    let (_, actual) = take_request(&mut work);
    assert_eq!(
        allocate(&mut foreign, &actual, 2, "wrong host")
            .result
            .err()
            .unwrap()
            .0,
        Error::InvalidState
    );
    assert_eq!(
        foreign.retire_shared_child(&child).result,
        Err(Error::InvalidState)
    );
    assert!(child.snapshot().pending());
    // Simulate a host incorrectly consuming the inverse without executing it.
    // The admission guard still rejects it after the parent's actual Unload.
    let (ticket, _omitted) = groups.pop(0).unwrap().unwrap();
    groups
        .complete(0, ticket, RestoreOutcome::Succeeded, None)
        .ok()
        .unwrap();
    host.finish_native_execution(parent, &mut store, &values, &work, &groups)
        .unwrap();
    host.retire(parent).unwrap();
    host.leave(parent).unwrap();
    work.withdraw();
    host.settle_execution(parent, &work, &groups).unwrap();
    host.begin_cleanup(parent).unwrap();
    host.release_native_execution(parent, &mut store, &mut values, &mut work, &mut groups)
        .unwrap();
    assert!(allocate(&mut host, &actual, 2, "late").result.is_err());
    assert!(child.snapshot().pending());
    assert_eq!(host.ids(), vec![parent]);
}

#[test]
fn rejected_pair_preserves_inputs_and_both_queues() {
    let (_, _, mut work, mut groups, _, _) = setup(750);
    let mut foreign: Groups = CleanupGroups::new(900);
    assert_eq!(
        work.enqueue_native_child(&mut foreign, 0, "foreign".into())
            .err()
            .unwrap(),
        "foreign"
    );
    assert_eq!(
        work.enqueue_native_child(&mut groups, 99, "missing".into())
            .err()
            .unwrap(),
        "missing"
    );
    assert_eq!(work.child_count(), 0);
    assert!(groups.pop(0).unwrap().is_none());
    work.withdraw();
    assert_eq!(
        work.enqueue_native_child(&mut groups, 0, "closed".into())
            .err()
            .unwrap(),
        "closed"
    );
    let mut unbound: Work = Work::new(901);
    let mut local: Groups = CleanupGroups::new(901);
    assert_eq!(
        unbound
            .enqueue_native_child(&mut local, 0, "unbound".into())
            .err()
            .unwrap(),
        "unbound"
    );
    assert_eq!(unbound.child_count(), 0);
    assert!(local.pop(0).unwrap().is_none());
}

#[test]
fn cloned_observers_and_competing_rejections_share_one_terminal_decision() {
    let (mut host, _, mut work, mut groups, _, _) = setup(760);
    let (child, _) = work
        .enqueue_native_child(&mut groups, 0, "race".into())
        .ok()
        .unwrap();
    let barrier = Arc::new(Barrier::new(9));
    let accepted = std::thread::scope(|scope| {
        let mut threads = Vec::new();
        for _ in 0..8 {
            let child = child.clone();
            let barrier = barrier.clone();
            threads.push(scope.spawn(move || {
                barrier.wait();
                let accepted = child.reject().result;
                for _ in 0..1000 {
                    assert!(child.snapshot().failed());
                }
                accepted as usize
            }));
        }
        barrier.wait();
        threads
            .into_iter()
            .map(|t| t.join().unwrap())
            .sum::<usize>()
    });
    assert_eq!(accepted, 1);
    assert!(child.snapshot().failed());
    let (_, request) = take_request(&mut work);
    assert!(request.snapshot().failed());
    assert!(restore_inverse(&mut host, &mut groups)
        .0
        .snapshot()
        .failed());
}

#[test]
fn assigned_constructor_and_concurrent_observers_keep_the_registered_identity() {
    let (mut host, parent, _, _, _, _) = setup(770);
    let id = host
        .register(
            Some(parent),
            &BTreeMap::new(),
            port(2),
            PluginDefinition::new(vec![], vec![], "external mount".into()),
            "host".into(),
        )
        .ok()
        .unwrap();
    let identity = host.registration(id).unwrap().child_identity().unwrap();
    let (child, initial) = SharedChild::from_identity(identity);
    assert_eq!(initial.identity(), Some(identity));
    std::thread::scope(|scope| {
        for _ in 0..4 {
            let child = child.clone();
            scope.spawn(move || {
                for _ in 0..1000 {
                    assert_eq!(child.snapshot().identity(), Some(identity));
                    assert!(!child.reject().result);
                }
            });
        }
        for _ in 0..10 {
            assert_eq!(
                host.retire_shared_child(&child).result.unwrap(),
                Some(identity)
            );
        }
    });
    assert!(host.kernel().retired(id));
    assert!(!host.kernel().retired(parent));
}

struct ObserveOnDrop {
    child: Option<SharedChild>,
    drops: Arc<AtomicUsize>,
}
impl Drop for ObserveOnDrop {
    fn drop(&mut self) {
        if let Some(child) = &self.child {
            assert!(child.snapshot().cancelled());
            self.drops.fetch_add(1, Ordering::SeqCst);
        }
    }
}
#[test]
fn rejected_captures_are_returned_before_destructors_reenter_the_shared_slot() {
    let (send, receive) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        let drops = Arc::new(AtomicUsize::new(0));
        let mut host = NativeHost::new(780);
        let parent = host
            .register(
                None,
                &BTreeMap::new(),
                port(1),
                PluginDefinition::new(
                    vec![],
                    vec![],
                    ObserveOnDrop {
                        child: None,
                        drops: drops.clone(),
                    },
                ),
                (),
            )
            .ok()
            .unwrap();
        let store = NativeServices::<()>::new(780);
        let (mut work, mut groups, _): (Work<()>, Groups, _) =
            host.begin_native_execution(parent, &store, 781).unwrap();
        let (child, _) = work.enqueue_native_child(&mut groups, 0, ()).ok().unwrap();
        host.retire_shared_child(&child).result.unwrap();
        let rejected = host
            .register_shared_child(
                &child,
                &BTreeMap::new(),
                port(2),
                PluginDefinition::new(
                    vec![],
                    vec![],
                    ObserveOnDrop {
                        child: Some(child.clone()),
                        drops: drops.clone(),
                    },
                ),
                (),
            )
            .result
            .err()
            .unwrap();
        assert_eq!(drops.load(Ordering::SeqCst), 0);
        drop(rejected);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        send.send(()).unwrap();
    });
    receive
        .recv_timeout(Duration::from_secs(10))
        .expect("the shared lock must be released before dropping rejected captures");
    worker.join().unwrap();
}
