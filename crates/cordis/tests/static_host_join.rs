use cordis::runtime::static_host::{
    with_child_join_guard, StaticChildControl, StaticEpisode, StaticPlugin,
};
use cordis::{Context, Plugin, ServiceHandle, ServiceKey};
use std::collections::BTreeSet;
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Wake, Waker};

fn publication() -> (ServiceHandle<u64>, StaticChildControl, StaticEpisode) {
    let key = ServiceKey::new("guarded-publication");
    let anchor = ServiceKey::<()>::new("owner-anchor");
    let retained = Arc::new(Mutex::new(None));
    let capture = retained.clone();
    let mut plugin = StaticPlugin::new(Plugin::new("owner", move |setup| {
        *capture.lock().unwrap() = Some(setup.publish(key, 17_u64)?);
        Ok(())
    }))
    .unwrap();
    let context = Context::new();
    let mut start = plugin
        .begin_with_dynamic_host(
            3,
            1,
            context.clone(),
            vec![],
            context.port(anchor),
            Arc::new(|| {}),
        )
        .unwrap();
    assert_eq!(
        start
            .setup
            .as_mut()
            .poll(&mut TaskContext::from_waker(Waker::noop())),
        Poll::Ready(Ok(()))
    );
    let control = start
        .episode
        .drain_child_requests()
        .unwrap()
        .remove(0)
        .control;
    let handle = retained.lock().unwrap().take().unwrap();
    (handle, control, start.episode)
}
fn joined(handle: &ServiceHandle<u64>) -> Poll<Result<(), String>> {
    Pin::new(&mut handle.join()).poll(&mut TaskContext::from_waker(Waker::noop()))
}

#[test]
fn forbidden_join_rejects_without_claiming_restoration_or_poisoning_an_external_join() {
    let (handle, control, episode) = publication();
    control.complete_mount(Ok(8)).unwrap();
    let blocked = BTreeSet::from([8]);
    assert_eq!(
        with_child_join_guard(&blocked, || joined(&handle)),
        Poll::Ready(Err("ReentrantServiceJoin".into()))
    );
    assert!(!handle.finished());
    assert!(handle.errors().is_empty());
    assert!(joined(&handle).is_pending());
    control.removed().unwrap();
    assert_eq!(
        with_child_join_guard(&blocked, || joined(&handle)),
        Poll::Ready(Ok(()))
    );
    assert!(handle.finished());
    let mut cleanup = episode.cleanup().unwrap();
    assert_eq!(
        cleanup
            .as_mut()
            .poll(&mut TaskContext::from_waker(Waker::noop())),
        Poll::Ready(Ok(()))
    );
}

#[test]
fn nested_join_guards_restore_the_callers_wait_targets_even_after_panic() {
    let (handle, control, _) = publication();
    control.complete_mount(Ok(9)).unwrap();
    with_child_join_guard(&BTreeSet::from([9]), || {
        assert!(with_child_join_guard(&BTreeSet::new(), || joined(&handle)).is_pending());
        let caught = std::panic::catch_unwind(|| {
            with_child_join_guard(&BTreeSet::new(), || panic!("future panicked"));
        });
        assert!(caught.is_err());
        assert_eq!(
            joined(&handle),
            Poll::Ready(Err("ReentrantServiceJoin".into()))
        );
    });
    assert!(joined(&handle).is_pending());
    control.removed().unwrap();
}

#[test]
fn allocation_wakes_an_existing_join_to_recheck_its_new_wait_edge() {
    struct Count(AtomicUsize);
    impl Wake for Count {
        fn wake(self: Arc<Self>) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    let (handle, control, _) = publication();
    let count = Arc::new(Count(AtomicUsize::new(0)));
    let waker = Waker::from(count.clone());
    let mut future = handle.join();
    assert!(Pin::new(&mut future)
        .poll(&mut TaskContext::from_waker(&waker))
        .is_pending());
    control.complete_mount(Ok(10)).unwrap();
    assert_eq!(count.0.load(Ordering::SeqCst), 1);
    assert_eq!(
        with_child_join_guard(&BTreeSet::from([10]), || {
            Pin::new(&mut future).poll(&mut TaskContext::from_waker(&waker))
        }),
        Poll::Ready(Err("ReentrantServiceJoin".into()))
    );
    assert!(!handle.finished());
    control.removed().unwrap();
    assert_eq!(
        count.0.load(Ordering::SeqCst),
        1,
        "rejected waits unregister their waker"
    );
}
