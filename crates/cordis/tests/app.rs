#![cfg(feature = "tokio")]
use cordis::{App, AppError, Context, Phase, Plugin, RuntimeError, ServiceKey};
use std::future::Future;
use std::pin::pin;
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc, Mutex,
};
use std::task::{Context as TaskContext, Poll, Waker};
use std::time::Duration;
use tokio::sync::Notify;

async fn soon<T>(future: impl Future<Output = T>) -> T {
    tokio::time::timeout(Duration::from_secs(5), future)
        .await
        .expect("driver stopped making progress")
}
fn provider(key: ServiceKey<u64>, value: u64) -> Plugin {
    Plugin::new("provider", move |ctx| {
        ctx.provide(key, value)?;
        Ok(())
    })
    .provides(key)
}

#[test]
fn construction_requires_an_explicit_executor() {
    assert!(matches!(App::new(), Err(AppError::NoExecutor)));
}

#[tokio::test]
async fn readiness_is_distinct_from_settling_and_provider_replacement_reloads() {
    let app = App::new().unwrap();
    let key = ServiceKey::<u64>::of();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let output = seen.clone();
    let consumer = soon(app.plugin(Plugin::with_dependencies("consumer", key).setup(
        move |_, value| {
            output.lock().unwrap().push(*value);
            Ok(())
        },
    )))
    .await
    .unwrap();
    let mut ready = pin!(consumer.ready());
    soon(consumer.settled()).await.unwrap();
    assert!(ready
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
        .is_pending());
    assert_eq!(
        soon(app.snapshot()).await.unwrap().plugins[0].phase,
        Phase::Inactive
    );
    let first = soon(app.plugin(provider(key, 1))).await.unwrap();
    soon(ready).await.unwrap();
    soon(first.dispose()).await.unwrap();
    let next = soon(app.plugin(provider(key, 2))).await.unwrap();
    soon(next.ready()).await.unwrap();
    soon(consumer.ready()).await.unwrap();
    assert_eq!(*seen.lock().unwrap(), [1, 2]);
    soon(app.shutdown()).await.unwrap();
    soon(app.shutdown()).await.unwrap();
    assert!(matches!(
        soon(consumer.ready()).await,
        Err(AppError::Runtime(RuntimeError::Retired(_)))
    ));
}

#[tokio::test]
async fn dropping_a_dispose_waiter_does_not_cancel_async_cleanup() {
    let app = App::new().unwrap();
    let entered = Arc::new(Notify::new());
    let release = Arc::new(Notify::new());
    let done = Arc::new(AtomicBool::new(false));
    let (inside, gate, finished) = (entered.clone(), release.clone(), done.clone());
    let plugin = soon(app.plugin(Plugin::new("resource", move |ctx| {
        let (inside, gate, finished) = (inside.clone(), gate.clone(), finished.clone());
        ctx.on_cleanup_async(move || async move {
            inside.notify_one();
            gate.notified().await;
            finished.store(true, Ordering::SeqCst);
            Ok(())
        });
        Ok(())
    })))
    .await
    .unwrap();
    soon(plugin.ready()).await.unwrap();
    drop(plugin.dispose());
    soon(entered.notified()).await;
    assert!(!done.load(Ordering::SeqCst));
    release.notify_one();
    soon(plugin.dispose()).await.unwrap();
    assert!(done.load(Ordering::SeqCst));
    soon(app.shutdown()).await.unwrap();
}

#[tokio::test]
async fn shutdown_failure_preserves_resources_for_explicit_retry() {
    let app = App::new().unwrap();
    let tries = Arc::new(AtomicUsize::new(0));
    let attempts = tries.clone();
    let plugin = soon(app.plugin(Plugin::new("retry", move |ctx| {
        let attempts = attempts.clone();
        ctx.on_cleanup_retryable(move || {
            if attempts.fetch_add(1, Ordering::SeqCst) == 0 {
                Err("first attempt failed".into())
            } else {
                Ok(())
            }
        });
        Ok(())
    })))
    .await
    .unwrap();
    soon(plugin.ready()).await.unwrap();
    assert!(matches!(
        soon(app.shutdown()).await,
        Err(AppError::Shutdown(_))
    ));
    assert_eq!(tries.load(Ordering::SeqCst), 1);
    assert_eq!(soon(app.snapshot()).await.unwrap().plugins.len(), 1);
    assert!(matches!(
        soon(app.plugin(Plugin::new("late", |_| Ok(())))).await,
        Err(AppError::Closed)
    ));
    soon(plugin.retry_cleanup()).await.unwrap();
    soon(app.shutdown()).await.unwrap();
    assert_eq!(tries.load(Ordering::SeqCst), 2);
}

#[tokio::test]
async fn provider_stays_alive_through_consumer_cleanup() {
    let app = App::new().unwrap();
    let key = ServiceKey::<AtomicBool>::new("alive");
    let provider = soon(
        app.plugin(
            Plugin::new("provider", move |ctx| {
                let alive = ctx.provide(key, AtomicBool::new(true))?;
                ctx.on_cleanup(move || {
                    alive.store(false, Ordering::SeqCst);
                    Ok(())
                });
                Ok(())
            })
            .provides(key),
        ),
    )
    .await
    .unwrap();
    let observed = Arc::new(AtomicBool::new(false));
    let output = observed.clone();
    let consumer = soon(app.plugin(Plugin::with_dependencies("consumer", key).setup(
        move |ctx, alive| {
            let output = output.clone();
            ctx.on_cleanup(move || {
                assert!(alive.load(Ordering::SeqCst));
                output.store(true, Ordering::SeqCst);
                Ok(())
            });
            Ok(())
        },
    )))
    .await
    .unwrap();
    soon(consumer.ready()).await.unwrap();
    soon(provider.dispose()).await.unwrap();
    assert!(observed.load(Ordering::SeqCst));
    soon(app.shutdown()).await.unwrap();
}

#[tokio::test]
async fn handles_are_bound_to_their_application_and_scopes_are_preserved() {
    let a = App::new().unwrap();
    let b = App::new().unwrap();
    let key = ServiceKey::<u64>::of();
    let first = soon(a.plugin(provider(key, 1))).await.unwrap();
    let second = soon(b.plugin(provider(key, 2))).await.unwrap();
    assert_eq!(first.id(), second.id());
    soon(second.ready()).await.unwrap();
    soon(first.dispose()).await.unwrap();
    assert_eq!(*soon(b.get(key)).await.unwrap().unwrap(), 2);
    let scope = Context::new().isolate(key);
    soon(b.plugin_in(scope.clone(), provider(key, 3)))
        .await
        .unwrap();
    let isolated = soon(b.plugin_in(
        scope,
        Plugin::with_dependencies("isolated", key).setup(|_, value| {
            assert_eq!(*value, 3);
            Ok(())
        }),
    ))
    .await
    .unwrap();
    soon(isolated.ready()).await.unwrap();
    soon(a.shutdown()).await.unwrap();
    soon(b.shutdown()).await.unwrap();
}

#[tokio::test]
async fn update_retains_declarations_and_restarts_consumers() {
    let app = App::new().unwrap();
    let key = ServiceKey::<u64>::new("updated");
    let provider = soon(app.plugin(provider(key, 1))).await.unwrap();
    let values = Arc::new(Mutex::new(Vec::new()));
    let output = values.clone();
    let consumer = soon(app.plugin(Plugin::with_dependencies("reader", key).setup(
        move |_, value| {
            output.lock().unwrap().push(*value);
            Ok(())
        },
    )))
    .await
    .unwrap();
    soon(consumer.ready()).await.unwrap();
    soon(provider.update_async(move |ctx| async move {
        ctx.provide(key, 2)?;
        Ok(())
    }))
    .await
    .unwrap();
    soon(consumer.ready()).await.unwrap();
    assert_eq!(*values.lock().unwrap(), [1, 2]);
    soon(app.shutdown()).await.unwrap();
}

#[tokio::test]
async fn setup_failure_is_reported_by_handle_and_shutdown() {
    let app = App::new().unwrap();
    let failed = soon(app.plugin(Plugin::new("failed", |_| Err("failure".into()))))
        .await
        .unwrap();
    assert!(matches!(
        soon(failed.ready()).await,
        Err(AppError::Runtime(RuntimeError::Setup { .. }))
    ));
    assert!(matches!(
        soon(app.shutdown()).await,
        Err(AppError::Shutdown(_))
    ));
    soon(app.shutdown()).await.unwrap();
}

#[tokio::test]
async fn shutdown_waiter_survives_dropping_all_command_senders() {
    let app = App::new().unwrap();
    let gate = Arc::new(Notify::new());
    let inner = gate.clone();
    let plugin = soon(app.plugin(Plugin::new("resource", move |ctx| {
        let inner = inner.clone();
        ctx.on_cleanup_async(move || async move {
            inner.notified().await;
            Ok(())
        });
        Ok(())
    })))
    .await
    .unwrap();
    soon(plugin.ready()).await.unwrap();
    let mut shutdown = pin!(app.shutdown());
    drop(plugin);
    drop(app);
    assert!(matches!(
        shutdown
            .as_mut()
            .poll(&mut TaskContext::from_waker(Waker::noop())),
        Poll::Pending
    ));
    tokio::task::yield_now().await;
    gate.notify_one();
    soon(shutdown).await.unwrap();
}

#[tokio::test]
async fn one_shot_cleanup_failures_survive_pending_waits_and_shutdown() {
    let app = App::new().unwrap();
    let entered = Arc::new(Notify::new());
    let release = Arc::new(Notify::new());
    let (inside, gate) = (entered.clone(), release.clone());
    let plugin = soon(app.plugin(Plugin::new("one-shot failure", move |ctx| {
        let (inside, gate) = (inside.clone(), gate.clone());
        ctx.on_cleanup_async(move || async move {
            inside.notify_one();
            gate.notified().await;
            Ok(())
        });
        // LIFO: this fails before the earlier inverse blocks.
        ctx.on_cleanup(|| Err("one-shot failure".into()));
        Ok(())
    })))
    .await
    .unwrap();
    soon(plugin.ready()).await.unwrap();
    let disposal = plugin.dispose();
    soon(entered.notified()).await;
    assert_eq!(
        soon(app.cleanup_errors()).await.unwrap(),
        vec![RuntimeError::Cleanup {
            plugin: plugin.id(),
            error: "one-shot failure".into(),
        }]
    );
    let shutdown = app.shutdown();
    // Let shutdown start while the earlier inverse is still outstanding.
    soon(app.snapshot()).await.unwrap();
    release.notify_one();
    assert!(matches!(soon(disposal).await, Err(AppError::Cleanup(errors)) if errors.len() == 1));
    let failure = soon(shutdown).await.unwrap_err();
    assert!(matches!(failure, AppError::Shutdown(error) if error.cleanup.len() == 1));
    assert!(soon(app.snapshot()).await.unwrap().plugins.is_empty());
    assert!(soon(app.cleanup_errors()).await.unwrap().is_empty());
    soon(app.shutdown()).await.unwrap();
}

#[tokio::test]
async fn scoped_children_sync_updates_and_typed_recipe_updates_share_one_runtime() {
    let app = App::new().unwrap();
    let key = ServiceKey::<u64>::new("scoped value");
    let scoped = app.scoped(app.context().isolate(key));
    let provider = soon(scoped.plugin(provider(key, 1))).await.unwrap();
    soon(provider.ready()).await.unwrap();
    let parent = soon(scoped.plugin(Plugin::new("parent", |_| Ok(()))))
        .await
        .unwrap();
    let values = Arc::new(Mutex::new(Vec::new()));
    let observed = values.clone();
    let child = soon(parent.plugin(Plugin::with_dependencies("child", key).setup(
        move |_, value| {
            observed.lock().unwrap().push(*value);
            Ok(())
        },
    )))
    .await
    .unwrap();
    soon(child.ready()).await.unwrap();
    assert_eq!(child.context().port(key), scoped.context().port(key));
    assert_eq!(
        soon(child.snapshot()).await.unwrap().unwrap().parent,
        Some(parent.id())
    );
    assert!(soon(app.get(key)).await.unwrap().is_none());
    assert_eq!(*soon(scoped.get(key)).await.unwrap().unwrap(), 1);
    assert_eq!(
        *soon(app.get_in(scoped.context().clone(), key))
            .await
            .unwrap()
            .unwrap(),
        1
    );

    soon(provider.update(move |ctx| {
        ctx.provide(key, 2)?;
        Ok(())
    }))
    .await
    .unwrap();
    soon(child.ready()).await.unwrap();
    assert_eq!(*values.lock().unwrap(), [1, 2]);
    let observed = values.clone();
    soon(
        child.update_plugin(Plugin::with_dependencies("new child", key).setup_async(
            move |_, value| {
                let observed = observed.clone();
                async move {
                    observed.lock().unwrap().push(*value + 10);
                    Ok(())
                }
            },
        )),
    )
    .await
    .unwrap();
    assert_eq!(
        soon(child.snapshot()).await.unwrap().unwrap().name,
        "new child"
    );
    assert_eq!(*values.lock().unwrap(), [1, 2, 12]);
    let unknown = ServiceKey::<u64>::new("changed contract");
    assert!(
        matches!(soon(child.update_plugin(Plugin::with_dependencies("invalid", unknown).setup(|_, _| panic!("must not run")))).await,
        Err(AppError::Runtime(RuntimeError::IncompatibleUpdate(id))) if id == child.id())
    );
    assert_eq!(
        soon(child.snapshot()).await.unwrap().unwrap().name,
        "new child"
    );
    soon(parent.dispose()).await.unwrap();
    assert!(soon(child.snapshot()).await.unwrap().is_none());
    assert!(soon(parent.plugin(Plugin::new("late child", |_| Ok(()))))
        .await
        .is_err());
    soon(app.shutdown()).await.unwrap();
}

#[tokio::test]
async fn application_errors_keep_the_cause_and_an_unrelated_waiter_can_still_activate() {
    use cordis::{CallbackError, ServiceReadError, ServiceReadFailure};
    use std::error::Error;
    let app = App::new().unwrap();
    let missing = ServiceKey::<u64>::new("undeclared");
    let failed = soon(
        app.plugin(Plugin::with_dependencies("failed", ()).setup_async(
            move |ctx, ()| async move {
                ctx.require(missing)?;
                Ok(())
            },
        )),
    )
    .await
    .unwrap();
    let error = soon(failed.ready()).await.unwrap_err();
    let runtime = error
        .source()
        .unwrap()
        .downcast_ref::<RuntimeError>()
        .unwrap();
    let callback = runtime
        .source()
        .unwrap()
        .downcast_ref::<CallbackError>()
        .unwrap();
    let read = callback
        .source()
        .unwrap()
        .downcast_ref::<ServiceReadError>()
        .unwrap();
    assert_eq!(read.reason, ServiceReadFailure::Undeclared);
    assert_eq!(read.plugin, failed.id());
    let key = ServiceKey::<u64>::new("waiting for provider");
    let waiting = soon(app.plugin(Plugin::with_dependencies("waiting", key).setup(|_, _| Ok(()))))
        .await
        .unwrap();
    let mut ready = pin!(waiting.ready());
    soon(waiting.settled()).await.unwrap();
    assert!(ready
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
        .is_pending());
    soon(app.plugin(provider(key, 3))).await.unwrap();
    soon(ready).await.unwrap();
    let error = soon(app.shutdown()).await.unwrap_err();
    let AppError::Shutdown(error) = error else {
        panic!("expected shutdown error")
    };
    assert_eq!(error.setup.len(), 1);
    assert!(
        matches!(&error.setup[0], RuntimeError::Setup { error, .. } if error.service_read().is_some())
    );
}

#[tokio::test]
async fn disposal_reports_the_cleanup_that_blocks_it_even_with_an_unrelated_failure() {
    let app = App::new().unwrap();
    let unrelated = soon(app.plugin(Plugin::new("unrelated", |ctx| {
        ctx.on_cleanup_retryable(|| Err("unrelated failure".into()));
        Ok(())
    })))
    .await
    .unwrap();
    soon(unrelated.ready()).await.unwrap();
    assert!(soon(unrelated.dispose()).await.is_err());
    let key = ServiceKey::<u64>::new("retained");
    let provider = soon(app.plugin(provider(key, 1))).await.unwrap();
    let attempts = Arc::new(AtomicUsize::new(0));
    let inner = attempts.clone();
    let consumer = soon(app.plugin(Plugin::with_dependencies("consumer", key).setup(
        move |ctx, _| {
            let inner = inner.clone();
            ctx.on_cleanup_retryable(move || {
                if inner.fetch_add(1, Ordering::SeqCst) == 0 {
                    Err("dependent failure".into())
                } else {
                    Ok(())
                }
            });
            Ok(())
        },
    )))
    .await
    .unwrap();
    soon(consumer.ready()).await.unwrap();
    assert!(matches!(soon(provider.dispose()).await,
        Err(AppError::Runtime(RuntimeError::Cleanup { plugin, error })) if plugin == consumer.id() && error.message() == "dependent failure"));
    soon(consumer.retry_cleanup()).await.unwrap();
    soon(provider.dispose()).await.unwrap();
    assert_eq!(attempts.load(Ordering::SeqCst), 2);
    // This application's unrelated retained failure remains visible at shutdown.
    assert!(soon(app.shutdown()).await.is_err());
}
