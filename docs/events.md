# Events and lifecycle ownership

Cordis provides typed synchronous events, asynchronous all-settled events, and
around middleware. Dispatch snapshots the listener registry and releases its
lock before running filters, callbacks, futures, destructors, or wake methods.
The event adapter is ordinary Rust; these concurrency guarantees are tested,
not Verus theorems about arbitrary callbacks.

| Channel | Dispatch | Result and failures |
| --- | --- | --- |
| `Event<T, R>` | `emit`, `emit_filtered` | Registration order; return values ignored; panics propagate. |
| `Event<T, Option<R>>` | `bail`, `bail_filtered` | First `Some`, including `Some(false)`, stops dispatch. |
| `AsyncEvent<T, R, E>` | `parallel`, `parallel_filtered`, `emit` | All eligible factories start, then futures are polled concurrently. Every result settles; callback errors and factory/poll panics are aggregated. |
| `AsyncEvent<T, Option<R>, E>` | `serial`, `serial_filtered` | Await one callback at a time; first `Some` or error stops dispatch without constructing later callbacks. |
| `Waterfall<T, R, E>` | `run`, `run_filtered` | Middleware wraps `next.call()`, transforms its result, or short-circuits. Panics propagate. |
| `AsyncWaterfall<T, R, E>` | `run`, `run_filtered` | Async around middleware with the same continuation contract; panics propagate. |

`EventScope::Relevant(port)` selects a service/realm identity;
`EventScope::Custom(id)` selects an application context. Global listeners always
run, including with custom predicates. A global dispatch selects every listener.
`EventOptions` controls prepending and once registration. Once claims are atomic
across concurrent and reentrant dispatches. A short circuit does not consume
later once listeners.

## Choose the ownership contract

`on` / `once` / `on_with_options` return an ordinary subscription. `dispose` and
`off` remove it from future snapshots. A callback already in a snapshot can
still run. Dropping an ordinary subscription does not remove it. This is useful
when snapshot semantics are desired and callback resources outlive dispatches.

`on_owned` / `on_owned_with_options` return an `OwnedSubscription`:

- `close()` stops admission immediately and removes the listener. Even an old
  snapshot skips it if it has not already acquired an invocation permit.
- `drain()` closes immediately and returns a future that waits for admitted
  invocations. It includes the destruction of their callback futures and
  listener closure captures. Closed, unstarted snapshots release these captures
  immediately instead of retaining them until the dispatch progresses.
- `in_flight()` reports outstanding callback/continuation leases, including
  concurrent callback teardown; `is_closed()` reports closure.
- Dropping the last handle closes the registration. Dropping a clone does not.
- Dropping a drain future unregisters its wake notification, keeps admission
  closed, and does not cancel callbacks. Another drain can be awaited later.

Admission and closure share one mutex, giving their race a definite order. A
callback which entered first remains counted until it returns or its future is
cancelled. No user callback or wake method executes while the registry or
admission mutex is held. Drain notifications are also removed and dropped after
releasing the admission mutex. Each concurrent closer holds a teardown lease,
so another drain cannot finish before a closure destructor running in that
closer. Closing drops closure captures synchronously; application destructors
can block even though close does not wait for admitted callbacks.

Use `on_in(owner, scope, callback)` or `on_in_with_options` to attach the owned
subscription to a plugin episode. Both `Setup` and `AsyncSetup` implement
`EventOwner`. The listener remains dormant while its cleanup is installed, then
starts admitting invocations. A stale or cancelled owner cannot leave an active
listener behind. The episode retains its own subscription handle, so dropping
the returned handle keeps the registration until owner cleanup.

```rust
use cordis::{Context, Plugin, Runtime};
use cordis::events::{AsyncEvent, EventScope};

let requests = AsyncEvent::<String>::new();
let mut runtime = Runtime::new();
runtime.mount(&Context::new(), None, Plugin::new("handler", move |setup| {
    requests.on_in(setup, EventScope::Global, |request| async move {
        println!("{request}");
        Ok(())
    })?;
    Ok(())
}))?;
# Ok::<(), cordis::RuntimeError>(())
```

When a dependent consumer unloads, this cleanup drains its admitted handlers
before finishing the consumer episode. The kernel's committed-binding guard
then permits the provider's cleanup. Declare every service dependency with
`Plugin::requires`; reading arbitrary external resources is outside that guard.
For resources created in the same episode, register their cleanup before the
listener: the default group's LIFO cleanup order drains the listener first.
Independent effect groups have concurrent cleanup and need explicit ordering
when they share a resource.

## Cancellation and middleware

Async dispatch does not spawn detached tasks. `parallel` invokes callback
factories immediately; its returned future owns the listener futures even
before its first poll. `serial` and async waterfall construct callbacks when
polled. Poll dispatches to completion or drop them to cancel. Owned permits are
released in either case, including unwinding from callback or future destructor
panics. A process abort or a second panic during unwinding cannot be recovered.

`Next` is single-use. Cloning `AsyncNext` shares the same atomic continuation
claim; a second call yields `WaterfallError::NextCalledTwice`. A callback may
ignore `next` to short-circuit. Calling async `next` claims it immediately, even
if the returned future is later dropped without polling. An owned callback's continuation retains the same invocation lease:
if the callback stores `AsyncNext` externally and returns, drain still waits
until the continuation is dropped or its returned future completes or is dropped.
Later listeners acquire their own admission permits when invoked. Keeping an
unused continuation forever therefore keeps its originating episode alive.

Never await `subscription.drain()` inside that subscription's own callback:
the drain includes the callback and would wait for itself. `close()` is safe
there. Likewise, an owner cannot finish unloading while a retained pending
dispatch still needs that owner to finish unloading. Complete or cancel that
dispatch to break the dependency. There is no forced timeout that releases a
provider while an admitted callback may still use it.

Detached work spawned by a callback is not part of the callback's future and
therefore is not drained. Attach its lifetime separately using an owner cleanup
that joins it. The event adapter drains callback closure captures that it owns; extra copies
of captured resources kept by application code and arbitrary external I/O remain
application-managed resources. Async error types implement `Display`, and
implement `std::error::Error` with source chaining when their callback error
type does.
