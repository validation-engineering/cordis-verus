use cordis::{Context, Plugin, Runtime, ServiceKey};
use std::future::Future;
use std::sync::Arc;
use std::task::{Context as TaskContext, Poll, Wake, Waker};

struct ThreadWake(std::thread::Thread);
impl Wake for ThreadWake {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }
}
fn block_on<F: Future>(future: F) -> F::Output {
    let waker = Waker::from(Arc::new(ThreadWake(std::thread::current())));
    let mut cx = TaskContext::from_waker(&waker);
    let mut future = std::pin::pin!(future);
    loop {
        match future.as_mut().poll(&mut cx) {
            Poll::Ready(value) => return value,
            Poll::Pending => std::thread::park(),
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let greeting = ServiceKey::<String>::new("greeting");

    // Consumers can mount before their required provider exists.
    runtime.mount(
        &context,
        None,
        Plugin::new("consumer", move |ctx| {
            let greeting = ctx.get(greeting)?;
            println!("consumer: {greeting}");
            ctx.on_cleanup_async(move || async move {
                println!("consumer cleanup still sees: {greeting}");
                Ok(())
            });
            Ok(())
        })
        .requires(greeting),
    )?;
    block_on(runtime.settle())?;

    runtime.mount(
        &context,
        None,
        Plugin::new("provider", move |ctx| {
            ctx.provide(greeting, "hello from verified Cordis".to_owned())?;
            ctx.on_cleanup(|| {
                println!("provider cleanup follows the consumer");
                Ok(())
            });
            Ok(())
        })
        .provides(greeting),
    )?;
    block_on(runtime.settle())?;
    runtime.dispose_all()?;
    block_on(runtime.settle())?;
    Ok(())
}
