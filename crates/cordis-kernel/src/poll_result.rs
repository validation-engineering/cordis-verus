//! Interpret the actual Rust Poll/result, including caught panics, under a
//! checked contract. The enum declaration describes Rust's existing variants;
//! it provides no assumed poll, catch_unwind or callback implementation.
use crate::effect_work::EffectOutput;
use std::task::Poll;
use vstd::prelude::*;

verus! {
#[verifier::reject_recursive_types(T)]
#[verifier::external_type_specification]
pub struct ExPoll<T>(std::task::Poll<T>);

/// Pending is never converted to completion. A panic may only become failure.
/// A checked caller supplies the panic formatter's contract, not a success flag.
pub fn normalize_poll<T,P,E,H:FnOnce(P)->E>(actual:Result<Poll<T>,P>,panic_error:H)
    ->(out:Poll<Result<T,E>>)
    requires actual.is_err() ==> panic_error.requires((actual->Err_0,)),
    ensures match actual {
        Ok(Poll::Pending)=>out==Poll::Pending,
        Ok(Poll::Ready(value))=>out==Poll::Ready(Ok(value)),
        Err(panic)=>match out {Poll::Ready(Err(error))=>panic_error.ensures((panic,),error),_=>false},
    },
{
    match actual {
        Ok(Poll::Pending)=>Poll::Pending,
        Ok(Poll::Ready(value))=>Poll::Ready(Ok(value)),
        Err(panic)=>Poll::Ready(Err(panic_error(panic))),
    }
}

/// The actual yielded inverse is mapped once and retained. There is no
/// expected result argument and no callback invocation on Pending/end/error.
pub fn normalize_effect_poll<T,I,E,P,F:FnOnce(T)->I,H:FnOnce(P)->E>(
    actual:Result<Poll<Option<Result<T,E>>>,P>,map_inverse:F,panic_error:H)
    ->(out:EffectOutput<I,E>)
    requires actual.is_err() ==> panic_error.requires((actual->Err_0,)),
        match actual {Ok(Poll::Ready(Some(Ok(inverse))))=>map_inverse.requires((inverse,)),_=>true},
    ensures match actual {
        Ok(Poll::Pending)=>out is Pending,
        Ok(Poll::Ready(None))=>out is Ready && out->Ready_0==Ok(None),
        Ok(Poll::Ready(Some(Err(error))))=>out is Ready && out->Ready_0==Err(error),
        Ok(Poll::Ready(Some(Ok(inverse))))=>out is Ready && out->Ready_0.is_ok()
            && out->Ready_0->Ok_0.is_some() && map_inverse.ensures((inverse,),out->Ready_0->Ok_0.unwrap()),
        Err(panic)=>out is Ready && out->Ready_0.is_err()
            && panic_error.ensures((panic,),out->Ready_0->Err_0),
    },
{
    match normalize_poll(actual,panic_error) {
        Poll::Pending=>EffectOutput::Pending,
        Poll::Ready(Err(error))=>EffectOutput::Ready(Err(error)),
        Poll::Ready(Ok(None))=>EffectOutput::Ready(Ok(None)),
        Poll::Ready(Ok(Some(Err(error))))=>EffectOutput::Ready(Err(error)),
        Poll::Ready(Ok(Some(Ok(inverse))))=>EffectOutput::Ready(Ok(Some(map_inverse(inverse)))),
    }
}
} // verus!
