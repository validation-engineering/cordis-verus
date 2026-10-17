//! Own the actual accepted snapshot, revision, candidate and recovery payload.
//! The owned update batch gates commit and recovery using actual poll results.
//! Parsing, tree planning, lifecycle orchestration and persistence remain adapters.
//! Cancellation leaves the pending values in this owner; only commit advances
//! the revision. Capacity is checked before exposing a pending transaction.
use crate::configuration_batch::{Action, Batch, StepError};
use std::task::Poll;
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum TransactionError {Pending,Idle,Capacity,NotReady}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Structure {Remove,SettleRemoved,Mount,SettleMounted,Updates,Adopt,Ready,Undo,RecoverRemove,RecoverSettleRemoved,RecoverMount,RecoverSettleMounted,Recovered}
#[derive(Debug,PartialEq,Eq)]
pub enum StructureError<E> {NotReady,Callback(E)}
impl Structure {
    pub open spec fn successor(self)->Option<Structure> {
        match self {
            Structure::Remove=>Some(Structure::SettleRemoved),Structure::SettleRemoved=>Some(Structure::Mount),
            Structure::Mount=>Some(Structure::SettleMounted),Structure::SettleMounted=>Some(Structure::Updates),
            Structure::Adopt=>Some(Structure::Ready),Structure::RecoverRemove=>Some(Structure::RecoverSettleRemoved),
            Structure::RecoverSettleRemoved=>Some(Structure::RecoverMount),Structure::RecoverMount=>Some(Structure::RecoverSettleMounted),
            Structure::RecoverSettleMounted=>Some(Structure::Recovered),_=>None,
        }
    }
    fn next(self)->(out:Option<Structure>) ensures out==self.successor(), {
        match self {
            Structure::Remove=>Some(Structure::SettleRemoved),Structure::SettleRemoved=>Some(Structure::Mount),
            Structure::Mount=>Some(Structure::SettleMounted),Structure::SettleMounted=>Some(Structure::Updates),
            Structure::Adopt=>Some(Structure::Ready),Structure::RecoverRemove=>Some(Structure::RecoverSettleRemoved),
            Structure::RecoverSettleRemoved=>Some(Structure::RecoverMount),Structure::RecoverMount=>Some(Structure::RecoverSettleMounted),
            Structure::RecoverSettleMounted=>Some(Structure::Recovered),_=>None,
        }
    }
    fn boundary(self)->(out:bool) ensures out==matches!(self,Structure::Updates|Structure::Ready|Structure::Recovered),
    {matches!(self,Structure::Updates|Structure::Ready|Structure::Recovered)}
}
/// A save plan retains the accepted revision and actual adapter runtime domain.
/// Domain uniqueness belongs to the runtime allocator; equal numeric domains
/// alone do not authenticate independently constructed owners.
#[derive(Debug)]
pub struct SaveStamp {domain:u64,revision:u64}
impl SaveStamp {
    pub closed spec fn domain(&self)->u64 {self.domain}
    pub closed spec fn revision(&self)->u64 {self.revision}
}
pub struct Pending<S,R> {pub candidate:S,pub recovery:R}
#[verifier::opaque]
#[verifier::prophetic]
pub open spec fn structural_call<S,R,E,C:FnOnce(Structure,&S,&mut Pending<S,R>)->Poll<Result<(),E>>>(
    callback:C,phase:Structure,accepted:S,before:Pending<S,R>,after:Pending<S,R>,result:Poll<Result<(),E>>)->bool {
    exists|a:&S,p:&mut Pending<S,R>| *a==accepted && *p==before && *final(p)==after && callback.ensures((phase,a,p),result)
}
#[verifier::opaque]
#[verifier::prophetic]
pub open spec fn reconstructed<S,R,C:FnOnce(&mut R)->S>(callback:C,before:R,after:R,result:S)->bool {
    exists|r:&mut R| *r==before && *final(r)==after && callback.ensures((r,),result)
}
impl<S,R> Pending<S,R> {
    fn reconstruct<C:FnOnce(&mut R)->S>(&mut self,callback:C)->(out:S)
        requires forall|r:&mut R| callback.requires((r,)),
        ensures final(self).candidate==old(self).candidate,reconstructed::<S,R,C>(callback,old(self).recovery,final(self).recovery,out),
    {reveal(reconstructed);callback(&mut self.recovery)}
    fn poll_structure<E,C:FnOnce(Structure,&S,&mut Self)->Poll<Result<(),E>>>(&mut self,phase:Structure,accepted:&S,callback:C)->(out:Poll<Result<(),E>>)
        requires forall|s:Structure,a:&S,p:&mut Self| callback.requires((s,a,p)),
        ensures structural_call::<S,R,E,C>(callback,phase,*accepted,*old(self),*final(self),out),
    {reveal(structural_call);callback(phase,accepted,self)}
}
pub struct Rejected<S,R,K,U> {pub error:TransactionError,pub pending:Pending<S,R>,pub updates:Vec<Action<K,U>>}
#[allow(dead_code)]
pub struct Configuration<S,R,K,U> {current:S,revision:u64,pending:Option<Pending<S,R>>,updates:Batch<K,U>,structure:Option<Structure>,forward:Ghost<Seq<Structure>>,restoration:Ghost<Seq<Structure>>}
pub open spec fn forward_stages()->Seq<Structure> {seq![Structure::Remove,Structure::SettleRemoved,Structure::Mount,Structure::SettleMounted,Structure::Adopt]}
pub open spec fn recovery_stages()->Seq<Structure> {seq![Structure::RecoverRemove,Structure::RecoverSettleRemoved,Structure::RecoverMount,Structure::RecoverSettleMounted]}
impl<S,R,K,U> Configuration<S,R,K,U> {
    pub closed spec fn accepted(&self)->S {self.current}
    pub closed spec fn version(&self)->u64 {self.revision}
    pub closed spec fn staged(&self)->Option<Pending<S,R>> {self.pending}
    pub closed spec fn structural_phase(&self)->Option<Structure> {self.structure}
    pub closed spec fn forward_steps(&self)->Seq<Structure> {self.forward@}
    pub closed spec fn recovery_steps(&self)->Seq<Structure> {self.restoration@}
    pub open spec fn protocol(&self)->bool {
        &&& self.forward_steps().len()<=5 && self.forward_steps()==forward_stages().take(self.forward_steps().len() as int)
        &&& self.recovery_steps().len()<=4 && self.recovery_steps()==recovery_stages().take(self.recovery_steps().len() as int)
        &&& match self.structural_phase() {
            None=>self.forward_steps().len()==0 && self.recovery_steps().len()==0,
            Some(phase)=>match phase {
                Structure::Remove=>self.forward_steps().len()==0 && self.recovery_steps().len()==0,
                Structure::SettleRemoved=>self.forward_steps().len()==1 && self.recovery_steps().len()==0,
                Structure::Mount=>self.forward_steps().len()==2 && self.recovery_steps().len()==0,
                Structure::SettleMounted=>self.forward_steps().len()==3 && self.recovery_steps().len()==0,
                Structure::Updates|Structure::Adopt=>self.forward_steps().len()==4 && self.recovery_steps().len()==0,
                Structure::Ready=>self.forward_steps().len()==5 && self.recovery_steps().len()==0,
                Structure::Undo|Structure::RecoverRemove=>self.recovery_steps().len()==0,
                Structure::RecoverSettleRemoved=>self.recovery_steps().len()==1,
                Structure::RecoverMount=>self.recovery_steps().len()==2,
                Structure::RecoverSettleMounted=>self.recovery_steps().len()==3,
                Structure::Recovered=>self.recovery_steps().len()==4,
            },
        }
    }
    pub closed spec fn batch(&self)->Batch<K,U> {self.updates}
    pub closed spec fn wf(&self)->bool {
        self.protocol() && self.batch().wf() && (self.staged().is_some() ==> self.version()<u64::MAX)
            && (self.staged().is_none() ==> self.batch().entries().len()==0 && self.structural_phase().is_none())
    }
    /// Public logical consequences of the private owner invariant.
    pub proof fn state_facts(&self)
        requires self.wf(),
        ensures self.protocol(),self.batch().wf(),
            self.staged().is_some() ==> self.version()<u64::MAX,
            self.staged().is_none() ==> self.batch().entries().len()==0 && self.structural_phase().is_none(),
    {}
    pub fn updates(&self)->(out:&Batch<K,U>) ensures *out==self.batch(), {&self.updates}
    pub fn poll_update<E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(&mut self,callback:C)
        ->(out:Poll<Result<bool,StepError<E>>>)
        requires old(self).wf(),forall|k:&K,u:&mut U| callback.requires((k,u)),
        ensures update_result(*old(self),*final(self),callback,out),final(self).wf(),final(self).accepted()==old(self).accepted(),final(self).version()==old(self).version(),final(self).staged()==old(self).staged(),
            final(self).batch().entries().len()==old(self).batch().entries().len(),
            forall|i:int| 0<=i<old(self).batch().entries().len() ==> #[trigger] final(self).batch().entries()[i].identity()==old(self).batch().entries()[i].identity(),
            out==Poll::Ready(Ok(true)) ==> final(self).batch().complete(),
            old(self).structural_phase().is_none() || old(self).structural_phase()==Some(Structure::Updates) ==>
                (matches!(out,Poll::Pending|Poll::Ready(Err(_))) ==> !final(self).batch().complete()),
    {
        reveal(update_result);
        if self.structure.is_some() && self.structure!=Some(Structure::Updates) {
            return Poll::Ready(Err(StepError::Recovering));
        }
        let result=self.updates.poll_apply(callback);
        if matches!(result,Poll::Ready(Ok(true))) && self.structure.is_some() {self.structure=Some(Structure::Adopt);}
        result
    }
    pub fn poll_rollback<E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(&mut self,callback:C)
        ->(out:Poll<Result<bool,E>>)
        requires old(self).wf(),forall|k:&K,u:&mut U| callback.requires((k,u)),
        ensures crate::configuration_batch::rollback_result(old(self).batch(),final(self).batch(),callback,out),final(self).wf(),final(self).accepted()==old(self).accepted(),final(self).version()==old(self).version(),final(self).staged()==old(self).staged(),
            final(self).batch().restoring(),
            out==Poll::Ready(Ok(true)) ==> final(self).batch().entries().len()==0,
            matches!(out,Poll::Pending|Poll::Ready(Err(_))) ==> final(self).batch().entries().len()>0,
    {
        let structural=self.structure.is_some();
        let recovering=matches!(self.structure,Some(Structure::RecoverRemove|Structure::RecoverSettleRemoved|Structure::RecoverMount|Structure::RecoverSettleMounted|Structure::Recovered));
        if structural && !recovering {self.structure=Some(Structure::Undo);}
        let result=self.updates.poll_rollback(callback);
        if matches!(result,Poll::Ready(Ok(true))) && structural && !recovering {self.structure=Some(Structure::RecoverRemove);}
        result
    }
    pub fn new(current:S)->(out:Self)
        ensures out.wf(),out.accepted()==current,out.version()==0,out.staged().is_none(),out.batch().entries().len()==0,
    {Self {current,revision:0,pending:None,updates:Batch::empty(),structure:None,forward:Ghost(Seq::empty()),restoration:Ghost(Seq::empty())}}
    pub fn current(&self)->(out:&S) ensures *out==self.accepted(), {&self.current}
    pub fn revision(&self)->(out:u64) ensures out==self.version(), {self.revision}
    pub fn save_stamp(&self,domain:u64)->(out:Option<SaveStamp>)
        requires self.wf(),
        ensures out.is_some()==self.staged().is_none(),
            out.is_some() ==> out.unwrap().domain()==domain && out.unwrap().revision()==self.version(),
    {
        if self.pending.is_some() {None} else {Some(SaveStamp {domain,revision:self.revision})}
    }
    /// Equal configuration bytes do not make an old reviewed plan current again
    /// after a committed revision changes and later changes back (ABA).
    pub fn accepts_save(&self,domain:u64,stamp:&SaveStamp)->(out:bool)
        requires self.wf(),
        ensures out==(self.staged().is_none() && domain==stamp.domain() && self.version()==stamp.revision()),
    {self.pending.is_none() && domain==stamp.domain && self.revision==stamp.revision}
    pub fn pending(&self)->(out:Option<&Pending<S,R>>)
        ensures out.is_some()==self.staged().is_some(),out.is_some() ==> *out.unwrap()==self.staged().unwrap(),
    {self.pending.as_ref()}
    /// Lend only staged work. Even replacing all host recovery bookkeeping
    /// cannot publish the candidate or advance the accepted revision.
    pub fn pending_mut(&mut self)->(out:Option<&mut Pending<S,R>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).batch()==old(self).batch(),final(self).accepted()==old(self).accepted(),final(self).version()==old(self).version(),
            match out {Some(p)=>old(self).staged()==Some(*p) && final(self).staged()==Some(*final(p)),None=>old(self).staged().is_none() && final(self).staged().is_none()},
    {self.pending.as_mut()}
    /// Read the accepted snapshot while lending only the staged transaction.
    pub fn work(&mut self)->(out:(&S,Option<&mut Pending<S,R>>))
        requires old(self).wf(),
        ensures final(self).wf(),final(self).batch()==old(self).batch(),*out.0==old(self).accepted(),final(self).accepted()==old(self).accepted(),final(self).version()==old(self).version(),
            match out.1 {Some(p)=>old(self).staged()==Some(*p) && final(self).staged()==Some(*final(p)),None=>old(self).staged().is_none() && final(self).staged().is_none()},
    {(&self.current,self.pending.as_mut())}
    pub fn check_begin(&self)->(out:Result<(),TransactionError>)
        ensures out.is_ok()==(self.staged().is_none() && self.version()<u64::MAX),
            out.is_err() ==> out==Err(if self.staged().is_some() {TransactionError::Pending} else {TransactionError::Capacity}),
    {
        if self.pending.is_some() {Err(TransactionError::Pending)}
        else if self.revision==u64::MAX {Err(TransactionError::Capacity)} else {Ok(())}
    }
    pub fn begin(&mut self,candidate:S,recovery:R,updates:Vec<Action<K,U>>)->(out:Result<(),Rejected<S,R,K,U>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).accepted()==old(self).accepted(),final(self).version()==old(self).version(),
            out.is_ok()==(old(self).staged().is_none() && old(self).version()<u64::MAX),
            out.is_ok() ==> final(self).structural_phase().is_none() && final(self).staged()==Some(Pending {candidate,recovery}) && final(self).batch().applied()==0 && final(self).batch().attempted()==0 && !final(self).batch().restoring()
                && final(self).batch().entries()==updates@,
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.pending==(Pending {candidate,recovery}) && out->Err_0.updates==updates
                && out->Err_0.error==if old(self).staged().is_some() {TransactionError::Pending} else {TransactionError::Capacity},
    {
        if let Err(error)=self.check_begin() {return Err(Rejected {error,pending:Pending {candidate,recovery},updates});}
        self.pending=Some(Pending {candidate,recovery});self.updates=Batch::new(updates);self.structure=None;self.forward=Ghost(Seq::empty());self.restoration=Ghost(Seq::empty());Ok(())
    }
    /// Production loader entry: structural work must finish before updates,
    /// adoption and commit. The simpler begin() remains the update-only API.
    pub fn begin_structural(&mut self,candidate:S,recovery:R,updates:Vec<Action<K,U>>)->(out:Result<(),Rejected<S,R,K,U>>)
        requires old(self).wf(),
        ensures out.is_ok()==(old(self).staged().is_none() && old(self).version()<u64::MAX),final(self).wf(),final(self).accepted()==old(self).accepted(),final(self).version()==old(self).version(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> final(self).staged()==Some(Pending {candidate,recovery})
                && final(self).batch().entries()==updates@ && final(self).structural_phase()==Some(Structure::Remove),
    {
        let result=self.begin(candidate,recovery,updates);
        if result.is_ok() {self.structure=Some(Structure::Remove);}
        result
    }
    pub fn structure(&self)->(out:Option<Structure>) ensures out==self.structural_phase(), {self.structure}
    /// Invoke the real structural work with the actual accepted and staged
    /// payloads. Pending/error preserve the phase; only its successful return
    /// selects the next phase. No public acknowledgement flag is accepted.
    pub fn poll_structure<E,C:FnOnce(Structure,&S,&mut Pending<S,R>)->Poll<Result<(),E>>>(&mut self,callback:C)
        ->(out:Poll<Result<bool,StructureError<E>>>)
        requires old(self).wf(),forall|s:Structure,a:&S,p:&mut Pending<S,R>| callback.requires((s,a,p)),
        ensures structure_result(*old(self),*final(self),callback,out),final(self).wf(),final(self).accepted()==old(self).accepted(),final(self).version()==old(self).version(),final(self).batch()==old(self).batch(),
            matches!(out,Poll::Pending|Poll::Ready(Err(_))) ==> final(self).structural_phase()==old(self).structural_phase(),
            final(self).structural_phase()!=old(self).structural_phase() ==> old(self).structural_phase().is_some()
                && old(self).structural_phase().unwrap().successor()==final(self).structural_phase()
                && old(self).staged().is_some() && final(self).staged().is_some()
                && structural_call::<S,R,E,C>(callback,old(self).structural_phase().unwrap(),old(self).accepted(),old(self).staged().unwrap(),final(self).staged().unwrap(),Poll::Ready(Ok(()))),
            final(self).forward_steps()!=old(self).forward_steps() ==> old(self).structural_phase().is_some()
                && final(self).forward_steps()==old(self).forward_steps().push(old(self).structural_phase().unwrap())
                && final(self).structural_phase()!=old(self).structural_phase(),
            final(self).recovery_steps()!=old(self).recovery_steps() ==> old(self).structural_phase().is_some()
                && final(self).recovery_steps()==old(self).recovery_steps().push(old(self).structural_phase().unwrap())
                && final(self).structural_phase()!=old(self).structural_phase(),
            out==Poll::Ready(Ok(true)) ==> (final(self).structural_phase()==Some(Structure::Updates) || final(self).structural_phase()==Some(Structure::Ready) || final(self).structural_phase()==Some(Structure::Recovered)),
    {
        reveal(structure_result);
        let phase=match self.structure {Some(phase)=>phase,None=>return Poll::Ready(Err(StructureError::NotReady))};
        let next=match phase.next() {Some(next)=>next,None=>return if matches!(phase,Structure::Ready|Structure::Recovered) {
            Poll::Ready(Ok(true))} else {Poll::Ready(Err(StructureError::NotReady))}};
        let pending=match &mut self.pending {Some(p)=>p,None=>return Poll::Ready(Err(StructureError::NotReady))};
        match pending.poll_structure(phase,&self.current,callback) {
            Poll::Pending=>Poll::Pending,
            Poll::Ready(Err(error))=>Poll::Ready(Err(StructureError::Callback(error))),
            Poll::Ready(Ok(_unit))=>{
                assert(_unit==());
                proof {
                    if matches!(phase,Structure::Remove|Structure::SettleRemoved|Structure::Mount|Structure::SettleMounted|Structure::Adopt) {
                        self.forward=Ghost(self.forward@.push(phase));
                        assert(self.forward@ =~= forward_stages().take(self.forward@.len() as int));
                    } else {
                        self.restoration=Ghost(self.restoration@.push(phase));
                        assert(self.restoration@ =~= recovery_stages().take(self.restoration@.len() as int));
                    }
                }
                self.structure=Some(next);Poll::Ready(Ok(next.boundary()))
            },
        }
    }
    /// Only the exact owned batch's successful prefix can authorize commit.
    /// Return user payloads for destruction after the accepted-state mutation.
    pub fn commit(&mut self)->(out:Result<(S,R,Batch<K,U>),TransactionError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_ok()==(old(self).staged().is_some() && old(self).batch().complete() && (old(self).structural_phase().is_none() || old(self).structural_phase()==Some(Structure::Ready))),
            out.is_err() ==> *final(self)==*old(self) && out==Err(if old(self).staged().is_none() {TransactionError::Idle} else {TransactionError::NotReady}),
            out.is_ok() && old(self).structural_phase().is_some() ==> old(self).forward_steps()==forward_stages(),
            out.is_ok() ==> final(self).version()==old(self).version()+1 && final(self).staged().is_none()
                && final(self).accepted()==old(self).staged().unwrap().candidate
                && out->Ok_0==(old(self).accepted(),old(self).staged().unwrap().recovery,old(self).batch())
                && out->Ok_0.2.successes().len()==out->Ok_0.2.entries().len(),
    {
        if self.pending.is_none() {return Err(TransactionError::Idle);}
        if !self.updates.ready() || (self.structure.is_some() && self.structure!=Some(Structure::Ready)) {return Err(TransactionError::NotReady);}
        let pending=self.pending.take().unwrap();
        let mut candidate=pending.candidate;let recovery=pending.recovery;
        let mut updates=Batch::empty();core::mem::swap(&mut updates,&mut self.updates);
        core::mem::swap(&mut self.current,&mut candidate);self.revision+=1;self.structure=None;self.forward=Ghost(Seq::empty());self.restoration=Ghost(Seq::empty());Ok((candidate,recovery,updates))
    }
    /// The actual rebuilt snapshot can be accepted only after every started
    /// update's inverse succeeded. A failed/pending inverse keeps all inputs.
    pub fn recover(&mut self,mut recovered:S)->(out:Result<(S,Pending<S,R>),S>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).version()==old(self).version(),
            out.is_ok()==(old(self).staged().is_some() && old(self).batch().entries().len()==0 && (old(self).structural_phase().is_none() || old(self).structural_phase()==Some(Structure::Recovered))),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==recovered,
            out.is_ok() && old(self).structural_phase().is_some() ==> old(self).recovery_steps()==recovery_stages(),
            out.is_ok() ==> final(self).accepted()==recovered && final(self).staged().is_none()
                && out->Ok_0==(old(self).accepted(),old(self).staged().unwrap()),
    {
        if self.pending.is_none() || !self.updates.restored() || (self.structure.is_some() && self.structure!=Some(Structure::Recovered)) {return Err(recovered);}
        let pending=self.pending.take().unwrap();self.updates=Batch::empty();self.structure=None;self.forward=Ghost(Seq::empty());self.restoration=Ghost(Seq::empty());
        core::mem::swap(&mut self.current,&mut recovered);Ok((recovered,pending))
    }
    /// Production recovery extracts the result from the retained, successfully
    /// rebuilt recovery payload; no caller-selected snapshot is input.
    pub fn recover_with<C:FnOnce(&mut R)->S>(&mut self,callback:C)->(out:Result<(S,Pending<S,R>),TransactionError>)
        requires old(self).wf(),forall|r:&mut R| callback.requires((r,)),
        ensures final(self).wf(),final(self).version()==old(self).version(),
            out.is_ok()==(old(self).staged().is_some() && old(self).batch().entries().len()==0
                && (old(self).structural_phase().is_none() || old(self).structural_phase()==Some(Structure::Recovered))),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> final(self).staged().is_none() && out->Ok_0.0==old(self).accepted()
                && out->Ok_0.1.candidate==old(self).staged().unwrap().candidate
                && reconstructed::<S,R,C>(callback,old(self).staged().unwrap().recovery,out->Ok_0.1.recovery,final(self).accepted()),
            out.is_ok() && old(self).structural_phase().is_some() ==> old(self).recovery_steps()==recovery_stages(),
    {
        if self.pending.is_none() {return Err(TransactionError::Idle);}
        if !self.updates.restored() || (self.structure.is_some() && self.structure!=Some(Structure::Recovered)) {return Err(TransactionError::NotReady);}
        let mut pending=self.pending.take().unwrap();
        let mut recovered=pending.reconstruct(callback);
        core::mem::swap(&mut self.current,&mut recovered);
        self.updates=Batch::empty();self.structure=None;self.forward=Ghost(Seq::empty());self.restoration=Ghost(Seq::empty());
        Ok((recovered,pending))
    }
    /// An unchanged effective plan can refresh its source representation. This
    /// is an explicit metadata transition, not a lifecycle commit or stutter.
    pub fn refresh(&mut self,mut current:S)->(out:Result<S,S>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).batch()==old(self).batch(),final(self).version()==old(self).version(),final(self).staged()==old(self).staged(),
            out.is_ok()==old(self).staged().is_none(),
            out.is_ok() ==> final(self).accepted()==current && out->Ok_0==old(self).accepted(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==current,
    {
        if self.pending.is_some() {return Err(current);}
        core::mem::swap(&mut self.current,&mut current);Ok(current)
    }
}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn update_result<S,R,K,U,E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(
    a:Configuration<S,R,K,U>,b:Configuration<S,R,K,U>,callback:C,out:Poll<Result<bool,StepError<E>>>)->bool {
    if a.structural_phase().is_some() && a.structural_phase()!=Some(Structure::Updates) {
        a==b && out==Poll::Ready(Err(StepError::Recovering))
    } else {crate::configuration_batch::apply_result(a.batch(),b.batch(),callback,out)}
}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn structure_result<S,R,K,U,E,C:FnOnce(Structure,&S,&mut Pending<S,R>)->Poll<Result<(),E>>>(
    a:Configuration<S,R,K,U>,b:Configuration<S,R,K,U>,callback:C,out:Poll<Result<bool,StructureError<E>>>)->bool {
    if a.structural_phase().is_some() && a.structural_phase().unwrap().successor().is_some() && a.staged().is_some() {
        b.staged().is_some() && match out {
            Poll::Pending=>structural_call(callback,a.structural_phase().unwrap(),a.accepted(),a.staged().unwrap(),b.staged().unwrap(),Poll::Pending),
            Poll::Ready(Err(StructureError::Callback(error)))=>structural_call(callback,a.structural_phase().unwrap(),a.accepted(),a.staged().unwrap(),b.staged().unwrap(),Poll::Ready(Err(error))),
            Poll::Ready(Ok(_))=>structural_call(callback,a.structural_phase().unwrap(),a.accepted(),a.staged().unwrap(),b.staged().unwrap(),Poll::Ready(Ok(()))),
            _=>false,
        }
    } else {a==b}
}

}
