//! Own the real forward and inverse Futures. Cancellation drops only the
//! caller's borrow. The inverse factory is unreachable until the stored forward
//! operation has returned (success or failure). A failed inverse can be rebuilt.
use std::task::Poll;
use vstd::prelude::*;
verus! {
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn polled<F,E,C:FnOnce(&mut F)->Poll<Result<(),E>>>(callback:C,before:F,after:F,result:Poll<Result<(),E>>)->bool {
    exists|f:&mut F| *f==before && *final(f)==after && callback.ensures((f,),result)
}
fn poll<F,E,C:FnOnce(&mut F)->Poll<Result<(),E>>>(future:&mut F,callback:C)->(out:Poll<Result<(),E>>)
    requires forall|f:&mut F| callback.requires((f,)),
    ensures polled(callback,*old(future),*final(future),out),
{reveal(polled);callback(future)}
#[verifier::prophetic]
pub open spec fn restored_from<F,R:FnMut()->Result<F,E>,E,I:FnOnce(&mut F)->Poll<Result<(),E>>>(
    factory:R,saved:Option<F>,callback:I,result:Poll<Result<(),E>>)->bool {
    match saved {
        Some(before)=>exists|after:F| polled(callback,before,after,result),
        None=> (match result {Poll::Ready(Err(error))=>factory.ensures((),Err(error)),_=>false})
            || exists|before:F,after:F| factory.ensures((),Ok(before)) && polled(callback,before,after,result),
    }
}
pub struct Landing<F,E> {pub before:F,pub after:F,pub result:Result<(),E>}
pub struct Reversible<F,R,E> {
    forward:Option<F>,result:Option<Result<(),E>>,started:bool,rollback:R,restoring:Option<F>,landing:Ghost<Option<Landing<F,E>>>,
}
impl<F,R,E> Reversible<F,R,E> {
    pub closed spec fn forward(&self)->Option<F> {self.forward}
    pub closed spec fn result(&self)->Option<Result<(),E>> {self.result}
    pub closed spec fn started(&self)->bool {self.started}
    pub closed spec fn factory(&self)->R {self.rollback}
    pub closed spec fn inverse(&self)->Option<F> {self.restoring}
    pub closed spec fn landing(&self)->Option<Landing<F,E>> {self.landing@}
    pub open spec fn wf(&self)->bool {
        &&& self.forward().is_some()==self.result().is_none()
        &&& !self.started() ==> self.forward().is_some() && self.inverse().is_none()
        &&& self.inverse().is_some() ==> self.started() && self.result().is_some()
        &&& self.landing().is_some()==self.result().is_some()
        &&& self.landing().is_some() ==> self.landing().unwrap().result==self.result().unwrap()
    }
    pub fn new(forward:F,rollback:R)->(out:Self)
        ensures out.wf(),out.forward()==Some(forward),out.factory()==rollback,!out.started(),out.inverse().is_none(),out.result().is_none(),
    {Self {forward:Some(forward),result:None,started:false,rollback,restoring:None,landing:Ghost(None)}}
    /// The cached output is borrowed, so no Clone law for arbitrary errors is
    /// needed. Repeated polling cannot invoke a completed forward Future again.
    pub fn poll_apply<C:FnOnce(&mut F)->Poll<Result<(),E>>>(&mut self,callback:C)->(out:Poll<&Result<(),E>>)
        requires old(self).wf(),forall|f:&mut F| callback.requires((f,)),
        ensures final(self).wf(),final(self).factory()==old(self).factory(),final(self).inverse()==old(self).inverse(),
            old(self).result().is_some() ==> *final(self)==*old(self),
            match out {Poll::Pending=>final(self).result().is_none(),Poll::Ready(result)=>final(self).result()==Some(*result)},
            old(self).result().is_none() ==> final(self).started() && match out {
                Poll::Pending=>final(self).forward().is_some() && polled(callback,old(self).forward().unwrap(),final(self).forward().unwrap(),Poll::Pending),
                Poll::Ready(result)=>final(self).forward().is_none() && final(self).landing().unwrap().before==old(self).forward().unwrap()
                    && polled(callback,old(self).forward().unwrap(),final(self).landing().unwrap().after,Poll::Ready(*result)),
            },
    {
        if self.result.is_none() {
            self.started=true;
            let ghost before=self.forward.unwrap();
            let result=poll(self.forward.as_mut().unwrap(),callback);
            match result {
                Poll::Pending=>return Poll::Pending,
                Poll::Ready(result)=>{
                    self.landing=Ghost(Some(Landing {before,after:self.forward.unwrap(),result}));
                    self.forward=None;self.result=Some(result);
                },
            }
        }
        Poll::Ready(self.result.as_ref().unwrap())
    }
    fn prepare_inverse(&mut self)->(out:Result<(),E>) where R:FnMut()->Result<F,E>,
        requires old(self).wf(),old(self).started(),old(self).result().is_some(),old(self).factory().requires(()),
        ensures final(self).wf(),final(self).forward()==old(self).forward(),final(self).result()==old(self).result(),
            final(self).started()==old(self).started(),final(self).landing()==old(self).landing(),
            old(self).inverse().is_some() ==> *final(self)==*old(self) && out.is_ok(),
            out.is_ok() ==> final(self).inverse().is_some(),
            old(self).inverse().is_none() ==> match out {
                Ok(())=>old(self).factory().ensures((),Ok(final(self).inverse().unwrap())),
                Err(error)=>final(self).inverse().is_none() && old(self).factory().ensures((),Err(error)),
            },
    {
        if self.restoring.is_some() {return Ok(());}
        match (self.rollback)() {Ok(future)=>{self.restoring=Some(future);Ok(())},Err(error)=>Err(error)}
    }
    fn poll_inverse<C:FnOnce(&mut F)->Poll<Result<(),E>>>(&mut self,callback:C)->(out:Poll<Result<(),E>>)
        requires old(self).wf(),old(self).started(),old(self).result().is_some(),old(self).inverse().is_some(),
            forall|f:&mut F| callback.requires((f,)),
        ensures final(self).wf(),final(self).forward()==old(self).forward(),final(self).result()==old(self).result(),
            final(self).started()==old(self).started(),final(self).landing()==old(self).landing(),final(self).factory()==old(self).factory(),
            match out {
                Poll::Pending=>final(self).inverse().is_some() && polled(callback,old(self).inverse().unwrap(),final(self).inverse().unwrap(),out),
                Poll::Ready(_)=>final(self).inverse().is_none() && exists|after:F| polled(callback,old(self).inverse().unwrap(),after,out),
            },
    {
        let result=poll(self.restoring.as_mut().unwrap(),callback);
        if matches!(result,Poll::Ready(_)) {self.restoring=None;}
        result
    }
    pub fn poll_rollback<A:FnOnce(&mut F)->Poll<Result<(),E>>,I:FnOnce(&mut F)->Poll<Result<(),E>>>(&mut self,forward:A,inverse:I)
        ->(out:Poll<Result<(),E>>) where R:FnMut()->Result<F,E>,
        requires old(self).wf(),old(self).factory().requires(()),
            forall|f:&mut F| forward.requires((f,)),forall|f:&mut F| inverse.requires((f,)),
        ensures final(self).wf(),
            !old(self).started() ==> *final(self)==*old(self) && out==Poll::Ready(Ok(())),
            old(self).started() ==> final(self).started(),
            old(self).result().is_some() ==> final(self).result()==old(self).result() && final(self).landing()==old(self).landing(),
            old(self).started() && final(self).result().is_none() ==> out==Poll::Pending && final(self).inverse().is_none() && final(self).factory()==old(self).factory(),
            matches!(out,Poll::Ready(_)) && old(self).started() ==> final(self).result().is_some() && final(self).inverse().is_none(),
            old(self).started() && final(self).result().is_some() ==> restored_from(old(self).factory(),old(self).inverse(),inverse,out),
    {
        if !self.started {return Poll::Ready(Ok(()));}
        if matches!(self.poll_apply(forward),Poll::Pending) {return Poll::Pending;}
        if let Err(error)=self.prepare_inverse() {return Poll::Ready(Err(error));}
        self.poll_inverse(inverse)
    }
}
}
