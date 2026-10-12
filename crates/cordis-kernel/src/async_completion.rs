//! A completion carries the actual awaited Future output and its owned origin.
//! This proves result provenance if the Future returns, not eventual return or
//! the correctness of external effects performed by an arbitrary Future.
use core::future::Future;
#[cfg(verus_keep_ghost)]
use vstd::future::FutureAdditionalSpecFns;
use vstd::prelude::*;

verus! {

/// Only `await_completion` constructs this value. The receiver cannot change
/// its captured origin or awaited output. Wrapping a Future does not establish
/// that the supplied origin belongs to that callback or authenticate its I/O.
pub struct Completion<A,R> { argument:A, result:R }
impl<A,R> Completion<A,R> {
    pub closed spec fn argument(&self)->A {self.argument}
    pub closed spec fn result(&self)->R {self.result}
    pub fn argument_ref(&self)->(out:&A) ensures *out==self.argument(), {&self.argument}
    pub fn into_parts(self)->(out:(A,R))
        ensures out.0==self.argument(),out.1==self.result(),
    {(self.argument,self.result)}
}

/// Arguments/origin and result stay paired even if independent Futures finish
/// in a different order. No ghost expected result is accepted from the caller.
pub async fn await_completion<A,F:Future>(argument:A,future:F)->(out:Completion<A,F::Output>)
    ensures future.awaited(),out.argument()==argument,out.result()==future@,
{
    let result=future.await;
    Completion {argument,result}
}

/// A checked, nonempty caller establishes the Future's value from executable
/// code; neither an expected response nor a callable-closure premise is input.
pub async fn witnessed_completion(input:u64)->(out:Completion<u64,u64>)
    ensures out.argument()==input,out.result()==input ^ 37u64,
{
    let future=transform(input);
    await_completion(input,future).await
}

async fn transform(input:u64)->(out:u64)
    ensures out==input ^ 37u64,
{input ^ 37u64}

}
