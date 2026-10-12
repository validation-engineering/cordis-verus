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

/// Output of an actual call. The wrapper neither accepts nor constructs a
/// caller-supplied expected result. External callback effect laws remain the
/// callback implementor's obligation; `requires` must be discharged by checked
/// callers that depend on those laws.
pub struct Called<R> { result:R }
impl<R> Called<R> {
    pub closed spec fn value(&self)->R {self.result}
    pub fn into_result(self)->(out:R) ensures out==self.value(), {self.result}
}

pub fn invoke<A,C:FnOnce(A)->R,R>(argument:A,callback:C)->(out:Called<R>)
    requires callback.requires((argument,)),
    ensures callback.ensures((argument,),out.value()),
{
    let result=callback(argument);
    Called {result}
}

/// The factory runs before this value is returned; only polling its returned
/// Future is deferred. This keeps factory panics and side effects in the same
/// phase as a direct host call.
pub struct Awaiting<O,F:Future> {origin:O,future:F}
impl<O,F:Future> Awaiting<O,F> {
    pub closed spec fn origin(&self)->O {self.origin}
    pub closed spec fn pending(&self)->F {self.future}
    pub async fn complete(self)->(out:Completion<O,F::Output>)
        ensures out.argument()==self.origin(),self.pending().awaited(),out.result()==self.pending()@,
    {
        await_completion(self.origin,self.future).await
    }
}

pub fn invoke_future<O,A,C:FnOnce(A)->F,F:Future>(origin:O,argument:A,callback:C)->(out:Awaiting<O,F>)
    requires callback.requires((argument,)),
    ensures out.origin()==origin,callback.ensures((argument,),out.pending()),
{
    let called=invoke(argument,callback);
    Awaiting {origin,future:called.into_result()}
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
    let call=invoke_future(input,future,forward_future);
    call.complete().await
}

fn forward_future<F:Future>(future:F)->(out:F)
    ensures out==future,
{future}

pub fn witnessed_invocation(input:u64)->(out:u64)
    ensures out==input ^ 37u64,
{
    let operation=|n:u64| -> (out:u64) ensures out==n ^ 37u64, {n ^ 37u64};
    invoke(input,operation).into_result()
}

async fn transform(input:u64)->(out:u64)
    ensures out==input ^ 37u64,
{input ^ 37u64}

}
