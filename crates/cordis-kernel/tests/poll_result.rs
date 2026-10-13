use cordis_kernel::effect_work::EffectOutput;
use cordis_kernel::poll_result::{normalize_effect_poll, normalize_poll};
use std::task::Poll;

#[test]
fn pending_end_and_error_do_not_invoke_the_inverse_mapper() {
    for input in [
        Ok(Poll::Pending),
        Ok(Poll::Ready(None)),
        Ok(Poll::Ready(Some(Err("callback")))),
        Err("panic"),
    ] {
        let output: EffectOutput<(), &str> = normalize_effect_poll(
            input,
            |_: ()| panic!("no inverse was returned"),
            |panic| panic,
        );
        match (input, output) {
            (Ok(Poll::Pending), EffectOutput::Pending)
            | (Ok(Poll::Ready(None)), EffectOutput::Ready(Ok(None))) => {}
            (Ok(Poll::Ready(Some(Err(a)))), EffectOutput::Ready(Err(b)))
            | (Err(a), EffectOutput::Ready(Err(b))) => assert_eq!(a, b),
            _ => panic!("changed actual poll outcome"),
        }
    }
}
#[test]
fn actual_noncopy_inverse_is_mapped_once() {
    let inverse = Box::new(42_u64);
    let identity = (&*inverse) as *const u64;
    let mut calls = 0;
    let output = normalize_effect_poll(
        Ok::<_, &str>(Poll::Ready(Some(Ok::<_, &str>(inverse)))),
        |inverse| {
            calls += 1;
            inverse
        },
        |panic| panic,
    );
    let EffectOutput::Ready(Ok(Some(inverse))) = output else {
        panic!("lost inverse")
    };
    assert_eq!((&*inverse) as *const u64, identity);
    assert_eq!(calls, 1);
}
#[test]
fn future_poll_preserves_its_actual_receipt_and_panic_is_failure() {
    let value = Box::new("receipt");
    let output = normalize_poll(Ok::<_, &str>(Poll::Ready(value)), |panic| panic);
    assert_eq!(output, Poll::Ready(Ok(Box::new("receipt"))));
    assert_eq!(
        normalize_poll::<(), _, _, _>(Ok::<_, &str>(Poll::Pending), |_| "panic"),
        Poll::Pending
    );
    assert_eq!(
        normalize_poll::<(), _, _, _>(Err("caught"), |error| error),
        Poll::Ready(Err("caught"))
    );
}
