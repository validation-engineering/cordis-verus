use cordis::{
    CallbackError, CallbackErrorKind, Context, Effect, Inverse, Plugin, Runtime, RuntimeError,
    ServiceKey, ServiceReadError, ServiceReadFailure,
};
use std::{
    error::Error,
    future::Future,
    pin::pin,
    sync::{Arc, Mutex},
    task::{Context as TaskContext, Poll, Waker},
};

fn finish<T>(future: impl Future<Output = T>) -> T {
    match pin!(future)
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
    {
        Poll::Ready(value) => value,
        Poll::Pending => panic!("unexpected pending"),
    }
}
fn cause(error: &RuntimeError) -> &CallbackError {
    error.source().unwrap().downcast_ref().unwrap()
}
fn assert_read(error: &CallbackError, owner: usize, key: ServiceKey<u64>) {
    assert_eq!(error.kind(), CallbackErrorKind::ServiceRead);
    let read = error
        .source()
        .unwrap()
        .downcast_ref::<ServiceReadError>()
        .unwrap();
    assert_eq!(read, error.service_read().unwrap());
    assert_eq!(read.plugin, owner);
    assert_eq!(read.reason, ServiceReadFailure::Undeclared);
    assert_eq!(read.port, Context::new().port(key));
    assert!(read.location.file().ends_with("structured_errors.rs"));
    assert!(read.provider.is_none());
}

#[test]
fn sync_and_async_typed_setup_keep_service_error_sources_until_shutdown() {
    for asynchronous in [false, true] {
        let mut runtime = Runtime::new();
        let key = ServiceKey::<u64>::new("undeclared");
        let plugin = if asynchronous {
            Plugin::with_dependencies("async", ()).setup_async(move |ctx, ()| async move {
                ctx.get(key)?;
                Ok(())
            })
        } else {
            Plugin::with_dependencies("sync", ()).setup(move |ctx, ()| {
                ctx.require(key)?;
                Ok(())
            })
        };
        let owner = runtime.mount(&Context::new(), None, plugin).unwrap();
        let error = finish(runtime.join(owner)).unwrap_err();
        assert_read(cause(&error), owner, key);
        assert_eq!(runtime.setup_error(owner).unwrap(), cause(&error));
        let shutdown = finish(runtime.shutdown()).unwrap_err();
        assert_eq!(shutdown.setup.len(), 1);
        assert_read(cause(&shutdown.setup[0]), owner, key);
    }
}

#[test]
fn cleanup_and_effect_joins_retain_all_original_causes() {
    let mut runtime = Runtime::new();
    let key = ServiceKey::<u64>::new("undeclared cleanup read");
    let saved = Arc::new(Mutex::new(None));
    let output = saved.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("effects", move |ctx| {
                let episode = ctx.to_async();
                let effect = Effect::new()
                    .inverse(Inverse::new(|| {
                        Err(CallbackError::new(std::io::Error::new(
                            std::io::ErrorKind::PermissionDenied,
                            "denied",
                        )))
                    }))
                    .inverse(Inverse::new(move || {
                        episode.require(key)?;
                        Ok(())
                    }));
                *output.lock().unwrap() = Some(ctx.effect(effect)?);
                Ok(())
            }),
        )
        .unwrap();
    finish(runtime.settle()).unwrap();
    runtime.dispose(owner).unwrap();
    finish(runtime.settle()).unwrap();
    let handle = saved.lock().unwrap().take().unwrap();
    let joined = finish(handle.join()).unwrap_err();
    assert_eq!(joined.kind(), CallbackErrorKind::Multiple);
    assert_eq!(joined.errors().len(), 2);
    assert_read(&joined.errors()[0], owner, key);
    let external = joined.errors()[1]
        .source()
        .unwrap()
        .downcast_ref::<std::io::Error>()
        .unwrap();
    assert_eq!(external.kind(), std::io::ErrorKind::PermissionDenied);
    let shutdown = finish(runtime.shutdown()).unwrap_err();
    assert_eq!(shutdown.cleanup.len(), 2);
    assert_eq!(cause(&shutdown.cleanup[0]), &joined.errors()[0]);
    assert_eq!(cause(&shutdown.cleanup[1]), &joined.errors()[1]);
}

#[test]
fn panic_and_cooperative_cancellation_have_distinct_categories() {
    for asynchronous in [false, true] {
        let mut runtime = Runtime::new();
        let plugin = if asynchronous {
            Plugin::new_async("panic", |_| async { panic!("poll panic") })
        } else {
            Plugin::new("panic", |_| panic!("factory panic"))
        };
        runtime.mount(&Context::new(), None, plugin).unwrap();
        let error = finish(runtime.settle()).unwrap_err();
        assert_eq!(cause(&error).kind(), CallbackErrorKind::Panic);
    }
    let mut runtime = Runtime::new();
    runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("active cancellation", |_| Err(cordis::CANCELLED.into())),
        )
        .unwrap();
    let error = finish(runtime.settle()).unwrap_err();
    // The reserved category does not make cancellation legal in an active episode.
    assert_eq!(cause(&error).kind(), CallbackErrorKind::Cancelled);
}

#[test]
fn static_host_keeps_native_causes_until_the_external_protocol_boundary() {
    use cordis::runtime::static_host::StaticPlugin;
    let key = ServiceKey::<u64>::new("undeclared");
    let mut plugin = StaticPlugin::new(Plugin::with_dependencies("typed", ()).setup(
        move |ctx, ()| {
            ctx.require(key)?;
            Ok(())
        },
    ))
    .unwrap();
    let start = plugin.begin(42, 8, Context::new(), vec![]).unwrap();
    let error = finish(start.setup).unwrap_err();
    assert_read(&error, 42, key);
    assert_eq!(error.service_read().unwrap().generation, 8);
    finish(start.episode.cleanup().unwrap()).unwrap();
}
