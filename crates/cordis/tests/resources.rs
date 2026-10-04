use cordis::resources::ReversibleStore;
use cordis::{Context, Plugin, Runtime};
use cordis_kernel::resources::Store;
use std::future::Future;
use std::pin::pin;
use std::task::{Context as TaskContext, Poll, Waker};
fn run<T>(f: impl Future<Output = T>) -> T {
    let waker = Waker::noop();
    let mut cx = TaskContext::from_waker(waker);
    let mut f = pin!(f);
    match f.as_mut().poll(&mut cx) {
        Poll::Ready(v) => v,
        Poll::Pending => panic!("unexpected external wait"),
    }
}
#[test]
fn independent_transactions_preserve_each_others_effects() {
    let store = ReversibleStore::new(vec![1, 2]);
    let first = store.transaction();
    let second = store.transaction();
    first.write(0, 3).unwrap();
    first.write(0, 4).unwrap();
    second.write(1, 5).unwrap();
    assert!(second.write(0, 99).is_err());
    first.rollback().unwrap();
    assert_eq!((store.read(0), store.read(1)), (Some(1), Some(5)));
    second.rollback().unwrap();
    assert_eq!((store.read(0), store.read(1)), (Some(1), Some(2)));
    assert!(first.write(0, 100).is_err());
    first.rollback().unwrap();
}
#[test]
fn out_of_order_inverse_is_rejected_without_losing_token() {
    let mut store = Store::new(vec![10]);
    let first = store.write(1, 0, 20).unwrap();
    let last = store.write(1, 0, 30).unwrap();
    let first = match store.undo(first) {
        Err(inverse) => inverse,
        Ok(()) => panic!("accepted stale inverse"),
    };
    assert_eq!(store.read(0), Some(30));
    assert!(store.undo(last).is_ok());
    assert!(store.undo(first).is_ok());
    assert_eq!(store.read(0), Some(10));
}
#[test]
fn plugin_failure_and_disposal_restore_registered_resources() {
    let store = ReversibleStore::new(vec![7]);
    let copy = store.clone();
    let mut runtime = Runtime::new();
    let id = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("owner", move |setup| {
                let tx = setup.reversible(&copy);
                tx.write(0, 11)?;
                tx.write(0, 13)?;
                Ok(())
            }),
        )
        .unwrap();
    run(runtime.settle()).unwrap();
    assert_eq!(store.read(0), Some(13));
    runtime.dispose(id).unwrap();
    run(runtime.settle()).unwrap();
    assert_eq!(store.read(0), Some(7));
    let copy = store.clone();
    runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("failed", move |setup| {
                setup.reversible(&copy).write(0, 99)?;
                Err("init fails".into())
            }),
        )
        .unwrap();
    assert!(run(runtime.settle()).is_err());
    assert_eq!(store.read(0), Some(7));
}
