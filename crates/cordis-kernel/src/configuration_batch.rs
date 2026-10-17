//! The actual ordered update plans, including in-flight Futures, stay owned
//! across host cancellation. Only the real poll result advances the prefix;
//! recovery keeps a failed inverse and selects the last started plan.
use std::task::Poll;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Debug,PartialEq,Eq)]
pub enum StepError<E> {Recovering,Callback(E)}
pub struct Action<K,U> {key:K,payload:U}
impl<K,U> Action<K,U> {
    pub fn new(key:K,payload:U)->(out:Self)
        ensures out.identity()==key,out.value()==payload,
    {Self {key,payload}}
    fn poll<E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(&mut self,callback:C)->(out:Poll<Result<(),E>>)
        requires forall|k:&K,u:&mut U| callback.requires((k,u)),
        ensures final(self).identity()==old(self).identity(),invoked::<K,U,E,C>(callback,old(self).identity(),old(self).value(),final(self).value(),out),
    {reveal(invoked);callback(&self.key,&mut self.payload)}

    pub closed spec fn identity(&self)->K {self.key}
    pub closed spec fn value(&self)->U {self.payload}
    pub fn key(&self)->(out:&K) ensures *out==self.identity(), {&self.key}
    pub fn payload(&self)->(out:&U) ensures *out==self.value(), {&self.payload}
}
pub struct Success<K,U> {pub key:K,pub before:U,pub after:U}
pub struct Batch<K,U> {
    actions:Vec<Action<K,U>>,completed:usize,started:usize,recovering:bool,
    evidence:Ghost<Seq<Success<K,U>>>,
}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn invoked<K,U,E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(
    callback:C,key:K,before:U,after:U,result:Poll<Result<(),E>>)->bool {
    exists|k:&K,u:&mut U| *k==key && *u==before && *final(u)==after && callback.ensures((k,u),result)
}
impl<K,U> Batch<K,U> {
    pub closed spec fn entries(&self)->Seq<Action<K,U>> {self.actions@}
    pub closed spec fn applied(&self)->nat {self.completed as nat}
    pub closed spec fn attempted(&self)->nat {self.started as nat}
    pub closed spec fn restoring(&self)->bool {self.recovering}
    pub closed spec fn successes(&self)->Seq<Success<K,U>> {self.evidence@}
    pub open spec fn wf(&self)->bool {
        &&& self.applied()<=self.attempted()<=self.entries().len()
        &&& self.attempted()<=self.applied()+1
        &&& self.successes().len()==self.applied()
        &&& forall|i:int| 0<=i<self.applied() ==> #[trigger] self.successes()[i].key==self.entries()[i].identity()
    }
    pub open spec fn complete(&self)->bool {!self.restoring() && self.applied()==self.entries().len()}
    pub fn empty()->(out:Self)
        ensures out.wf(),out.entries()==Seq::<Action<K,U>>::empty(),out.applied()==0,out.attempted()==0,!out.restoring(),
    {Self {actions:Vec::new(),completed:0,started:0,recovering:false,evidence:Ghost(Seq::empty())}}
    pub fn new(actions:Vec<Action<K,U>>)->(out:Self)
        ensures out.wf(),out.applied()==0,out.attempted()==0,!out.restoring(),out.entries()==actions@,
    {Self {actions,completed:0,started:0,recovering:false,evidence:Ghost(Seq::empty())}}
    pub fn actions(&self)->(out:&[Action<K,U>]) ensures out@==self.entries(), {self.actions.as_slice()}
    pub fn ready(&self)->(out:bool) ensures out==self.complete(), {!self.recovering && self.completed==self.actions.len()}
    pub fn restored(&self)->(out:bool) ensures out==(self.entries().len()==0), {self.actions.is_empty()}

    /// No caller-supplied success acknowledgement. The closure receives the
    /// stored key and plan themselves; all other plans remain unchanged.
    pub fn poll_apply<E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(&mut self,callback:C)
        ->(out:Poll<Result<bool,StepError<E>>>)
        requires old(self).wf(),forall|k:&K,u:&mut U| callback.requires((k,u)),
        ensures apply_result(*old(self),*final(self),callback,out),final(self).wf(),final(self).entries().len()==old(self).entries().len(),
            forall|i:int| 0<=i<old(self).entries().len() ==> #[trigger] final(self).entries()[i].identity()==old(self).entries()[i].identity(),
            old(self).restoring() ==> *final(self)==*old(self) && out==Poll::Ready(Err(StepError::Recovering)),
            !old(self).restoring() && old(self).complete() ==> *final(self)==*old(self) && out==Poll::Ready(Ok(true)),
            !old(self).restoring() && !old(self).complete() ==> {
                let i=old(self).applied() as int;
                &&& final(self).attempted()==i+1
                &&& forall|j:int| 0<=j<old(self).entries().len() && j!=i ==> #[trigger] final(self).entries()[j]==old(self).entries()[j]
                &&& match out {
                    Poll::Pending=>final(self).applied()==old(self).applied() && !final(self).restoring()
                        && final(self).successes()==old(self).successes()
                        && invoked::<K,U,E,C>(callback,old(self).entries()[i].identity(),old(self).entries()[i].value(),final(self).entries()[i].value(),Poll::Pending),
                    Poll::Ready(Ok(done))=>final(self).applied()==i+1 && !final(self).restoring() && done==final(self).complete()
                        && final(self).successes()==old(self).successes().push(Success {key:old(self).entries()[i].identity(),before:old(self).entries()[i].value(),after:final(self).entries()[i].value()})
                        && invoked::<K,U,E,C>(callback,old(self).entries()[i].identity(),old(self).entries()[i].value(),final(self).entries()[i].value(),Poll::Ready(Ok(()))),
                    Poll::Ready(Err(StepError::Callback(error)))=>final(self).applied()==old(self).applied() && final(self).restoring()
                        && final(self).successes()==old(self).successes()
                        && invoked::<K,U,E,C>(callback,old(self).entries()[i].identity(),old(self).entries()[i].value(),final(self).entries()[i].value(),Poll::Ready(Err(error))),
                    _=>false,
                }
            },
    {
        reveal(apply_result);
        if self.recovering {return Poll::Ready(Err(StepError::Recovering));}
        if self.completed==self.actions.len() {return Poll::Ready(Ok(true));}
        let index=self.completed;
        self.started=index+1;
        let ghost before=self.actions@[index as int];
        let ghost selected=self.entries()[index as int];
        let result=self.actions[index].poll(callback);
        assert(invoked::<K,U,E,C>(callback,selected.identity(),selected.value(),self.entries()[index as int].value(),result));
        assert forall|j:int| 0<=j<self.entries().len() && j!=index implies #[trigger] self.entries()[j]==old(self).entries()[j] by {};
        match result {
            Poll::Pending=>Poll::Pending,
            Poll::Ready(Ok(_unit))=>{
                assert(_unit==());
                assert(Result::<(),E>::Ok(_unit)==Result::<(),E>::Ok(()));
                assert(result==Poll::<Result<(),E>>::Ready(Ok(())));
                assert(invoked::<K,U,E,C>(callback,selected.identity(),selected.value(),self.entries()[index as int].value(),Poll::Ready(Ok(()))));
                self.evidence=Ghost(self.successes().push(Success {key:before.identity(),before:before.value(),after:self.actions@[index as int].value()}));
                self.completed+=1;Poll::Ready(Ok(self.completed==self.actions.len()))
            },
            Poll::Ready(Err(error))=>{self.recovering=true;Poll::Ready(Err(StepError::Callback(error)))},
        }
    }

    /// Discard only unstarted plans. A started plan is removed only after its
    /// own inverse returns success. Pending/failure retains that exact plan.
    pub fn poll_rollback<E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(&mut self,callback:C)
        ->(out:Poll<Result<bool,E>>)
        requires old(self).wf(),forall|k:&K,u:&mut U| callback.requires((k,u)),
        ensures rollback_result(*old(self),*final(self),callback,out),final(self).wf(),final(self).restoring(),
            old(self).attempted()==0 ==> out==Poll::Ready(Ok(true)) && (final(self).entries().len()==0),
            old(self).attempted()>0 ==> {
                let i=(old(self).attempted()-1) as int;
                &&& forall|j:int| 0<=j<i ==> #[trigger] final(self).entries()[j]==old(self).entries()[j]
                &&& match out {
                    Poll::Ready(Ok(done))=>final(self).entries()==old(self).entries().take(i)
                        && final(self).attempted()==i && done==(i==0)
                        && exists|after:U| invoked::<K,U,E,C>(callback,old(self).entries()[i].identity(),old(self).entries()[i].value(),after,Poll::Ready(Ok(()))),
                    Poll::Pending=>final(self).attempted()==old(self).attempted() && final(self).entries().len()==old(self).attempted()
                        && final(self).entries()[i].identity()==old(self).entries()[i].identity()
                        && invoked::<K,U,E,C>(callback,old(self).entries()[i].identity(),old(self).entries()[i].value(),final(self).entries()[i].value(),Poll::Pending),
                    Poll::Ready(Err(error))=>final(self).attempted()==old(self).attempted() && final(self).entries().len()==old(self).attempted()
                        && final(self).entries()[i].identity()==old(self).entries()[i].identity()
                        && invoked::<K,U,E,C>(callback,old(self).entries()[i].identity(),old(self).entries()[i].value(),final(self).entries()[i].value(),Poll::Ready(Err(error))),
                }
            },
    {
        reveal(rollback_result);
        let ghost prior=self.entries();
        self.recovering=true;
        while self.actions.len()>self.started
            invariant self.wf(),self.recovering,self.started==old(self).started,self.completed==old(self).completed,
                self.entries().len()<=prior.len(),self.entries()==prior.take(self.actions.len() as int),self.successes()==old(self).successes(),
            decreases self.actions.len()-self.started,
        {
            let ghost length=self.entries().len();
            let ghost entries=self.entries();
            let _unused=self.actions.pop();
            assert(self.entries().len()==length-1);
            assert forall|j:int| 0<=j<self.entries().len() implies #[trigger] self.entries()[j]==prior[j] by {
                assert(self.entries()[j]==entries[j]);
                assert(entries[j]==prior[j]);
            }
            assert(self.entries() =~= prior.take(self.actions.len() as int));
        }
        if self.started==0 {return Poll::Ready(Ok(true));}
        let index=self.started-1;
        let ghost selected=self.entries()[index as int];
        let result=self.actions[index].poll(callback);
        assert(invoked::<K,U,E,C>(callback,selected.identity(),selected.value(),self.entries()[index as int].value(),result));
        assert forall|j:int| 0<=j<self.entries().len() && j!=index implies #[trigger] self.entries()[j]==old(self).entries()[j] by {};
        match result {
            Poll::Ready(Ok(_unit))=>{
                assert(_unit==());
                assert(Result::<(),E>::Ok(_unit)==Result::<(),E>::Ok(()));
                assert(result==Poll::<Result<(),E>>::Ready(Ok(())));
                assert(invoked::<K,U,E,C>(callback,selected.identity(),selected.value(),self.entries()[index as int].value(),Poll::Ready(Ok(()))));
                let _restored=self.actions.pop();self.started-=1;
                assert(self.entries() =~= old(self).entries().take(index as int));
                if self.completed>self.started {self.completed=self.started;self.evidence=Ghost(self.successes().take(self.started as int));}
                Poll::Ready(Ok(self.started==0))
            },
            Poll::Pending=>Poll::Pending,
            Poll::Ready(Err(error))=>Poll::Ready(Err(error)),
        }
    }
}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn apply_result<K,U,E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(
    a:Batch<K,U>,b:Batch<K,U>,callback:C,out:Poll<Result<bool,StepError<E>>>)->bool {
    &&& (b.wf())
    &&& (b.entries().len()==a.entries().len())
    &&& (forall|i:int| 0<=i<a.entries().len() ==> #[trigger] b.entries()[i].identity()==a.entries()[i].identity())
    &&& (a.restoring() ==> b==a && out==Poll::Ready(Err(StepError::Recovering)))
    &&& (!a.restoring() && a.complete() ==> b==a && out==Poll::Ready(Ok(true)))
    &&& (!a.restoring() && !a.complete() ==> {
                let i=a.applied() as int;
                &&& b.attempted()==i+1
                &&& forall|j:int| 0<=j<a.entries().len() && j!=i ==> #[trigger] b.entries()[j]==a.entries()[j]
                &&& match out {
                    Poll::Pending=>b.applied()==a.applied() && !b.restoring()
                        && b.successes()==a.successes()
                        && invoked::<K,U,E,C>(callback,a.entries()[i].identity(),a.entries()[i].value(),b.entries()[i].value(),Poll::Pending),
                    Poll::Ready(Ok(done))=>b.applied()==i+1 && !b.restoring() && done==b.complete()
                        && b.successes()==a.successes().push(Success {key:a.entries()[i].identity(),before:a.entries()[i].value(),after:b.entries()[i].value()})
                        && invoked::<K,U,E,C>(callback,a.entries()[i].identity(),a.entries()[i].value(),b.entries()[i].value(),Poll::Ready(Ok(()))),
                    Poll::Ready(Err(StepError::Callback(error)))=>b.applied()==a.applied() && b.restoring()
                        && b.successes()==a.successes()
                        && invoked::<K,U,E,C>(callback,a.entries()[i].identity(),a.entries()[i].value(),b.entries()[i].value(),Poll::Ready(Err(error))),
                    _=>false,
                }
            })
}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn rollback_result<K,U,E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(
    a:Batch<K,U>,b:Batch<K,U>,callback:C,out:Poll<Result<bool,E>>)->bool {
    &&& (b.wf())
    &&& (b.restoring())
    &&& (a.attempted()==0 ==> out==Poll::Ready(Ok(true)) && (b.entries().len()==0))
    &&& (a.attempted()>0 ==> {
                let i=(a.attempted()-1) as int;
                &&& forall|j:int| 0<=j<i ==> #[trigger] b.entries()[j]==a.entries()[j]
                &&& match out {
                    Poll::Ready(Ok(done))=>b.entries()==a.entries().take(i)
                        && b.attempted()==i && done==(i==0)
                        && exists|after:U| invoked::<K,U,E,C>(callback,a.entries()[i].identity(),a.entries()[i].value(),after,Poll::Ready(Ok(()))),
                    Poll::Pending=>b.attempted()==a.attempted() && b.entries().len()==a.attempted()
                        && b.entries()[i].identity()==a.entries()[i].identity()
                        && invoked::<K,U,E,C>(callback,a.entries()[i].identity(),a.entries()[i].value(),b.entries()[i].value(),Poll::Pending),
                    Poll::Ready(Err(error))=>b.attempted()==a.attempted() && b.entries().len()==a.attempted()
                        && b.entries()[i].identity()==a.entries()[i].identity()
                        && invoked::<K,U,E,C>(callback,a.entries()[i].identity(),a.entries()[i].value(),b.entries()[i].value(),Poll::Ready(Err(error))),
                }
            })
}

}
