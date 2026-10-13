use cordis_kernel::cleanup_groups::CleanupGroups;
use cordis_kernel::cleanup_journal::RestoreOutcome;
use cordis_kernel::effect_work::{EffectOutput, EffectRequest, EffectRun};
use cordis_kernel::lifecycle_state::LifecycleState;
use cordis_kernel::setup_work::SetupWork;
use cordis_kernel::{Binding, Error};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

type Work<P = String> = SetupWork<String, EffectRequest<P>>;
type Groups = CleanupGroups<String>;
fn begin<P>(domain: u64) -> (LifecycleState, usize, Work<P>, Groups) {
    let mut state = LifecycleState::new(domain);
    let id = state.insert(None, vec![], vec![]).unwrap();
    let (mut work, groups): (Work<P>, Groups) = state.begin_execution(id, domain + 1).unwrap();
    let receipt = work.issue_root(()).unwrap().run(|()| Ok::<(), ()>(()));
    work.complete_root(receipt).ok().unwrap().unwrap();
    (state, id, work, groups)
}
fn dispatch<P>(work: &mut Work<P>, groups: &Groups) -> EffectRun<P> {
    let item = work.take_group().unwrap();
    assert!(!work.is_idle());
    let reply = item.run(|request| request.activate(groups));
    work.complete_request(reply).ok().unwrap().ok().unwrap()
}
fn pending(
    run: EffectRun<String>,
) -> (
    EffectRun<String>,
    cordis_kernel::effect_work::EffectReply<String, String>,
) {
    run.call((), |payload, ()| (payload, EffectOutput::Pending))
        .ok()
        .unwrap()
}
#[test]
fn allocation_pairs_actual_payload_bindings_and_fifo_dispatch() {
    let (mut state, owner, mut work, mut groups) = begin::<String>(900);
    let bindings = vec![Binding {
        provider: 19,
        key: 7,
        realm: 3,
    }];
    let a = work
        .enqueue_effect(
            &mut groups,
            0,
            902,
            bindings.clone(),
            "first iterator".into(),
        )
        .unwrap();
    let b = work
        .enqueue_effect(&mut groups, 0, 903, vec![], "second iterator".into())
        .unwrap();
    assert_eq!(groups.len(), 3);
    assert_eq!(
        state.settle_execution(owner, &work, &groups),
        Err(Error::InvalidState)
    );
    let mut first = dispatch(&mut work, &groups);
    let mut second = dispatch(&mut work, &groups);
    assert_eq!((first.id(), first.get().as_str()), (a, "first iterator"));
    assert_eq!((second.id(), second.get().as_str()), (b, "second iterator"));
    assert!(first.admit(&mut groups, Some(&bindings)));
    assert!(second.admit(&mut groups, Some(&[])));
    let (mut first, reply) = first
        .call(42, |payload, input| {
            assert_eq!(payload, "first iterator");
            (
                format!("{payload}/{input}"),
                EffectOutput::<String, String>::Ready(Ok(Some("actual inverse".into()))),
            )
        })
        .ok()
        .unwrap();
    let report = first.land(&mut groups, reply).ok().unwrap().unwrap();
    assert!(report.continue_iteration);
    assert_eq!(first.get(), "first iterator/42");
    assert!(groups.get(b).unwrap().is_pending());
    groups.cancel(a);
    let (ticket, inverse) = groups.pop(a).unwrap().unwrap();
    assert_eq!(inverse, "actual inverse");
    groups
        .complete(a, ticket, RestoreOutcome::Succeeded, None)
        .unwrap();
    assert!(groups.remove(a));
}
#[test]
fn cancellation_rejects_new_acquisition_but_keeps_actual_pending_inverse() {
    let (_, _, mut work, mut groups) = begin::<String>(910);
    let id = work
        .enqueue_effect(&mut groups, 0, 912, vec![], "iterator".into())
        .unwrap();
    let mut run = dispatch(&mut work, &groups);
    assert!(run.admit(&mut groups, Some(&[])));
    let (mut run, reply) = pending(run);
    assert!(run.land(&mut groups, reply).ok().unwrap().is_none());
    groups.cancel(id);
    assert!(!groups.accepts_acquisition(id));
    assert!(groups.get(id).unwrap().is_pending());
    assert!(!groups.remove(id));
    assert!(work
        .enqueue_effect(&mut groups, id, 913, vec![], "new effect".into())
        .is_err());
    assert_eq!(
        work.enqueue_owned_child(&mut groups, id, "new child".into(), "new inverse".into()),
        Err(("new child".into(), "new inverse".into()))
    );
    groups
        .register(id, "in-flight registered inverse".into())
        .unwrap();
    assert!(run.admit(&mut groups, None));
    let (mut run, reply) = run
        .call((), |payload, ()| {
            (
                payload,
                EffectOutput::<String, String>::Ready(Ok(Some("landed inverse".into()))),
            )
        })
        .ok()
        .unwrap();
    let report = run.land(&mut groups, reply).ok().unwrap().unwrap();
    assert!(!report.continue_iteration);
    assert!(!run.admit(&mut groups, Some(&[])));
    for expected in ["landed inverse", "in-flight registered inverse"] {
        let (ticket, inverse) = groups.pop(id).unwrap().unwrap();
        assert_eq!(inverse, expected);
        groups
            .complete(id, ticket, RestoreOutcome::Succeeded, None)
            .unwrap();
    }
    assert!(groups.remove(id));
}
#[test]
fn replies_cannot_cross_groups_and_only_one_call_is_admitted() {
    let (_, _, mut work, mut groups) = begin::<String>(920);
    work.enqueue_effect(&mut groups, 0, 922, vec![], "a".into())
        .unwrap();
    work.enqueue_effect(&mut groups, 0, 923, vec![], "b".into())
        .unwrap();
    let mut a = dispatch(&mut work, &groups);
    let mut b = dispatch(&mut work, &groups);
    assert!(a.admit(&mut groups, Some(&[])));
    assert!(b.admit(&mut groups, Some(&[])));
    let (a, reply_a) = pending(a);
    let (mut b, reply_b) = pending(b);
    let calls = AtomicUsize::new(0);
    let (mut a, argument, _) = a
        .call(17, |payload, _| {
            calls.fetch_add(1, Ordering::SeqCst);
            (payload, EffectOutput::<String, String>::Pending)
        })
        .err()
        .unwrap();
    assert_eq!(argument, 17);
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert!(!a.admit(&mut groups, Some(&[])));
    let reply_a = b.land(&mut groups, reply_a).err().unwrap();
    let reply_b = a.land(&mut groups, reply_b).err().unwrap();
    assert!(a.land(&mut groups, reply_a).is_ok());
    assert!(b.land(&mut groups, reply_b).is_ok());
    assert!(a.admit(&mut groups, Some(&[])));
    let (mut a, reply) = pending(a);
    assert!(a.land(&mut groups, reply).is_ok());
}
#[test]
fn foreign_lifecycle_with_equal_numeric_groups_and_domains_rejects_request_and_reply() {
    let (_, _, mut work, mut groups) = begin::<String>(930);
    let mut foreign = LifecycleState::new(999);
    let owner = foreign.insert(None, vec![], vec![]).unwrap();
    let (mut other_work, mut other_groups): (Work, Groups) =
        foreign.begin_execution(owner, 931).unwrap();
    work.enqueue_effect(&mut groups, 0, 932, vec![], "actual".into())
        .unwrap();
    other_work
        .enqueue_effect(&mut other_groups, 0, 932, vec![], "foreign".into())
        .unwrap();
    let receipt = work.take_group().unwrap().run(|request| {
        let request = request.activate(&other_groups).err().unwrap();
        request.activate(&groups).ok().unwrap()
    });
    let mut run = work.complete_request(receipt).ok().unwrap();
    assert!(!run.admit(&mut other_groups, Some(&[])));
    assert!(run.admit(&mut groups, Some(&[])));
    let (mut run, reply) = pending(run);
    let reply = run.land(&mut other_groups, reply).err().unwrap();
    assert!(run.land(&mut groups, reply).is_ok());
    assert!(work
        .enqueue_effect(&mut other_groups, 0, 933, vec![], "wrong origin".into())
        .is_err());
    assert_eq!(other_groups.len(), 2);
}
#[test]
fn rejected_allocation_preserves_noncopy_inputs_without_orphan_groups() {
    struct Payload(Arc<AtomicUsize>);
    impl Drop for Payload {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    let (_, _, mut work, mut groups) = begin::<Payload>(940);
    let drops = Arc::new(AtomicUsize::new(0));
    for (source, domain) in [(0, 941), (99, 942)] {
        let rejected = work
            .enqueue_effect(&mut groups, source, domain, vec![], Payload(drops.clone()))
            .err()
            .unwrap();
        assert_eq!(groups.len(), 1);
        assert_eq!(work.group_count(), 0);
        assert_eq!(
            drops.load(Ordering::SeqCst),
            if source == 0 { 0 } else { 1 }
        );
        drop(rejected);
    }
    work.withdraw();
    assert!(work
        .enqueue_effect(&mut groups, 0, 942, vec![], Payload(drops.clone()))
        .is_err());
    assert_eq!(drops.load(Ordering::SeqCst), 3);
    assert_eq!(groups.len(), 1);
}
#[test]
fn result_error_and_exhaustion_end_iteration_without_inventing_inverse() {
    for error in [false, true] {
        let (_, _, mut work, mut groups) = begin::<String>(950);
        let id = work
            .enqueue_effect(&mut groups, 0, 952, vec![], "actual iterator".into())
            .unwrap();
        let mut run = dispatch(&mut work, &groups);
        assert!(run.admit(&mut groups, Some(&[])));
        let (mut run, reply) = run
            .call(error, |payload, error| {
                (
                    payload,
                    EffectOutput::<String, String>::Ready(if error {
                        Err("actual failure".into())
                    } else {
                        Ok(None)
                    }),
                )
            })
            .ok()
            .unwrap();
        let report = run.land(&mut groups, reply).ok().unwrap().unwrap();
        assert!(!report.continue_iteration);
        assert_eq!(report.error, error.then(|| "actual failure".to_string()));
        assert!(groups.get(id).unwrap().is_empty());
        assert!(!run.admit(&mut groups, Some(&[])));
    }
}
#[test]
fn cancellation_before_dispatch_does_not_execute_the_iterator() {
    let (_, _, mut work, mut groups) = begin::<String>(960);
    let id = work
        .enqueue_effect(&mut groups, 0, 962, vec![], "never called".into())
        .unwrap();
    groups.cancel(id);
    let mut run = dispatch(&mut work, &groups);
    assert!(!run.admit(&mut groups, Some(&[])));
    let calls = AtomicUsize::new(0);
    assert!(run
        .call((), |payload, ()| {
            calls.fetch_add(1, Ordering::SeqCst);
            (payload, EffectOutput::<String, String>::Pending)
        })
        .is_err());
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert!(groups.remove(id));
    assert!(work.is_idle());
}
