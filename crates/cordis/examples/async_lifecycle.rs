//! Run with: cargo run -p cordis --example async_lifecycle
use cordis::{Context, Effect, Inverse, Plugin, Runtime, ServiceKey};
use std::future::{poll_fn, Future};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Wake, Waker};

struct WakeThread(std::thread::Thread);
impl Wake for WakeThread {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.0.unpark();
    }
}
fn block_on<F: Future>(future: F) -> F::Output {
    let waker = Waker::from(Arc::new(WakeThread(std::thread::current())));
    let mut cx = TaskContext::from_waker(&waker);
    let mut future = std::pin::pin!(future);
    loop {
        match future.as_mut().poll(&mut cx) {
            Poll::Ready(value) => return value,
            Poll::Pending => std::thread::park(),
        }
    }
}
async fn yield_once() {
    let mut yielded = false;
    poll_fn(move |cx| {
        if yielded {
            Poll::Ready(())
        } else {
            yielded = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    })
    .await
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let service = ServiceKey::<String>::new("connection");
    let log = Arc::new(Mutex::new(Vec::new()));
    let output = log.clone();
    let provider = runtime.mount(
        &context,
        None,
        Plugin::new_async("connection", move |ctx| {
            let log = output.clone();
            async move {
                yield_once().await;
                ctx.provide(service, "connected".to_owned())?;
                ctx.on_cleanup(move || {
                    log.lock().unwrap().push("close connection");
                    Ok(())
                })?;
                Ok(())
            }
        })
        .provides(service),
    )?;
    let output = log.clone();
    runtime.mount(
        &context,
        None,
        Plugin::new("consumer", move |ctx| {
            let connection = ctx.get(service)?;
            let first_log = output.clone();
            let second_log = output.clone();
            ctx.effect(
                Effect::new()
                    .step(move |_| async move {
                        yield_once().await;
                        assert_eq!(&*connection, "connected");
                        Ok(Inverse::new(move || {
                            first_log.lock().unwrap().push("release first stage");
                            Ok(())
                        }))
                    })
                    .step(move |_| async move {
                        yield_once().await;
                        Ok(Inverse::new_async(move || async move {
                            yield_once().await;
                            second_log.lock().unwrap().push("release second stage");
                            Ok(())
                        }))
                    }),
            )?;
            ctx.mount(Plugin::new("owned child", move |child| {
                assert_eq!(&*child.get(service)?, "connected");
                Ok(())
            }))?;
            Ok(())
        })
        .requires(service),
    )?;
    block_on(runtime.settle())?;
    runtime.dispose(provider)?;
    block_on(runtime.settle())?;
    assert_eq!(
        *log.lock().unwrap(),
        vec![
            "release second stage",
            "release first stage",
            "close connection"
        ]
    );
    println!("{:?}", log.lock().unwrap());
    Ok(())
}
