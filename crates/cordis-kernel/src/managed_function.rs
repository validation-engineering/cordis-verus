//! Heterogeneous native functions. The interpreter, not a callback, owns the
//! operation arguments, selected continuation and successful-prefix inverses.
//! Scalar computations are extensible through the verified ScalarEffect trait.
use super::{
    access,
    effect::{EffectError, ScalarEffect},
    joint,
    payload::SharedPayload,
    registration,
    slot::ServiceSlot,
    Branch,
};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
use crate::lifecycle_state::services::NativeEpisode;
use crate::{
    cleanup_groups::payload as cleanup, execution::Execution,
    lifecycle_state::registration::RegisteredPlugin, Port,
};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
pub enum Effect<E,T:?Sized> {Scalar(E),Replace(Arc<T>)}
pub struct Call<E,T:?Sized> {pub key:u64,pub effect:Effect<E,T>,pub branch:Branch}
pub struct Function<E,T:?Sized> {code:Vec<Call<E,T>>}
impl<E,T:?Sized> Call<E,T> {
    pub open spec fn valid(&self,pc:int,len:nat)->bool {
        (super::program::Instruction {operation:super::Operation::Add(0),branch:self.branch}).valid(pc,len)
    }
    fn check(&self,pc:usize,len:usize)->(out:bool) ensures out==self.valid(pc as int,len as nat),
    {(super::program::Instruction {operation:super::Operation::Add(0),branch:self.branch}).check(pc,len)}
}
impl<E,T:?Sized> Function<E,T> {
    pub closed spec fn code(&self)->Seq<Call<E,T>> {self.code@}
    pub closed spec fn valid(&self)->bool {forall|i:int|0<=i<self.code().len() ==> #[trigger] self.code()[i].valid(i,self.code().len())}
    pub fn new(code:Vec<Call<E,T>>)->(out:Result<Self,Vec<Call<E,T>>>)
        ensures out.is_ok()==(forall|i:int|0<=i<code.len() ==> #[trigger] code@[i].valid(i,code.len() as nat)),
            out.is_ok() ==> out->Ok_0.valid() && out->Ok_0.code()==code@,out.is_err() ==> out->Err_0==code,
    {
        let mut i=0;
        while i<code.len()
            invariant i<=code.len(),forall|j:int|0<=j<i ==> #[trigger] code@[j].valid(j,code.len() as nat),
            decreases code.len()-i,
        {if !code[i].check(i,code.len()) {assert(!code@[i as int].valid(i as int,code.len() as nat));return Err(code);}i+=1;}
        Ok(Self {code})
    }
    pub fn check(&self)->(out:bool) ensures out==self.valid(),
    {
        let mut i=0;
        while i<self.code.len()
            invariant i<=self.code.len(),forall|j:int|0<=j<i ==> #[trigger] self.code()[j].valid(j,self.code().len()),
            decreases self.code.len()-i,
        {if !self.code[i].check(i,self.code.len()) {assert(!self.code()[i as int].valid(i as int,self.code().len()));return false;}i+=1;}
        true
    }
    pub proof fn shape(&self)
        requires self.valid(),
        ensures forall|i:int|0<=i<self.code().len() ==> #[trigger] self.code()[i].valid(i,self.code().len()),
    {}
    pub open spec fn bound<R>(&self,ports:Seq<Port>,recipe:RegisteredPlugin<R>)->bool {
        ports.len()==self.code().len() && forall|i:int|0<=i<ports.len() ==> {
            let p=#[trigger] ports[i];
            &&& p.key==self.code()[i].key && recipe.dependencies_spec().contains(p)
            &&& exists|j:int|0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j]==p
                && forall|k:int|0<=k<j ==> recipe.dependencies_spec()[k].key!=p.key
        }
    }
    /// Resolve every branch before root issuance, including unreachable calls.
    pub fn bind<R>(&self,recipe:&RegisteredPlugin<R>)->(out:Result<Vec<Port>,usize>)
        ensures out.is_ok() ==> self.bound(out->Ok_0@,*recipe),
            out.is_err() ==> out->Err_0<self.code().len()
                && !exists|j:int|0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j].key==self.code()[out->Err_0 as int].key,
    {
        let mut ports:Vec<Port>=Vec::new();let mut i=0;
        while i<self.code.len()
            invariant i<=self.code.len(),ports.len()==i,
                forall|j:int|0<=j<i ==> (#[trigger] ports@[j]).key==self.code()[j].key && recipe.dependencies_spec().contains(ports@[j])
                    && exists|k:int|0<=k<recipe.dependencies_spec().len() && recipe.dependencies_spec()[k]==ports@[j]
                        && forall|l:int|0<=l<k ==> recipe.dependencies_spec()[l].key!=ports@[j].key,
            decreases self.code.len()-i,
        {
            let port=match recipe.dependency_port(self.code[i].key) {Some(port)=>port,None=>return Err(i)};
            ports.push(port);i+=1;
        }
        Ok(ports)
    }
}
pub type Slot<T,M> = ServiceSlot<SharedPayload<T>,M>;
pub type Action<A,R,T,M,X> = cleanup::Action<A,R,Arc<Slot<T,M>>,T,X>;
pub type Owner<C,G,A,R,T,M,X> = Execution<Slot<T,M>,C,G,Action<A,R,T,M,X>>;
#[derive(Debug)]
pub enum Error {Capture(super::cursor::StartError),Scalar(EffectError),Payload(cleanup::AccessError)}
#[derive(Debug)]
pub enum AdmissionError {Closed,NoNative,Arity,WrongKey {pc:usize},Undeclared {pc:usize}}
pub struct Failure<T:?Sized> {
    pub pc:usize,pub error:Error,pub receipt:Tracked<Option<joint::Receipt>>,
    pub scalar:Ghost<Option<(super::slot::ServiceBinding,super::ValueState)>>,
    pub payload:Ghost<Option<super::payload::restoration::ForwardRejection<T>>>,
}
impl<T:?Sized> Failure<T> {
    #[verifier::opaque]
    pub open spec fn explained<E:ScalarEffect,M>(&self,call:Call<E,T>,port:Port,episode:NativeEpisode<Slot<T,M>>)->bool {
        match (self.error,call.effect) {
            (Error::Capture(super::cursor::StartError::Read(error)),Effect::Scalar(_))=>episode.reversible_read_failed(port,error),
            (Error::Scalar(error),Effect::Scalar(effect))=>self.receipt@.is_some() && self.receipt@.unwrap().wf() && self.scalar@.is_some()
                && access::selected(episode,self.scalar@.unwrap().0) && self.scalar@.unwrap().0.port_spec()==port
                && self.receipt@.unwrap().journal()==self.scalar@.unwrap().0.capture_spec().value_spec().journal_spec()
                && self.receipt@.unwrap().event().key==self.scalar@.unwrap().0.capture_spec().value_spec().object().key
                && self.receipt@.unwrap().event().change is Value
                && super::attempt::effect_rejection(self.receipt@.unwrap().event().change->Value_event,effect.model(),self.scalar@.unwrap().1,error),
            (Error::Payload(error),Effect::Replace(_))=>cleanup::access_failed(Some(episode),true,port,error,self.payload@),
            _=>false,
        }
    }
}

pub enum ResultStep<T:?Sized> {Scalar {write:access::Write,inverse:Ghost<super::Inverse>},Payload(cleanup::Admission<T>)}
pub struct Step<T:?Sized> {pub pc:usize,pub result:ResultStep<T>,pub next:Option<usize>}
impl<T:?Sized> Step<T> {
    pub open spec fn token(&self)->usize {match self.result {ResultStep::Scalar {write,..}=>write.admission.token,ResultStep::Payload(a)=>a.token_spec()}}
    pub open spec fn write(&self)->joint::Receipt {match self.result {ResultStep::Scalar {write,..}=>write.admission.registration().write(),ResultStep::Payload(a)=>a.inverse().after().commit}}
    pub open spec fn insertion(&self)->Option<joint::Receipt> {match self.result {ResultStep::Scalar {write,..}=>write.admission.registration().insertion(),ResultStep::Payload(a)=>a.registration_receipt()}}
    pub open spec fn witnessed(&self,receipts:registration::ReceiptMap,i:int)->bool {
        receipts.contains_key((i,false)) && receipts[(i,false)].same(&self.write())
            && (self.insertion().is_some() ==> receipts.contains_key((i,true)) && receipts[(i,true)].same(&self.insertion().unwrap()))
    }
    #[verifier::opaque]
    pub open spec fn corresponds<E:ScalarEffect,M>(&self,call:Call<E,T>,port:Port,episode:NativeEpisode<Slot<T,M>>)->bool {
        match (self.result,call.effect) {
            (ResultStep::Scalar {write,inverse},Effect::Scalar(effect))=>{
                &&& write.computed(effect.model(),call.branch) && access::selected(episode,write.binding) && write.binding.port_spec()==port
                &&& write.admission.next==self.next && inverse@.recorded()
                &&& write.admission.registration().write().same(&inverse@.origin())
                &&& inverse@.target()==*write.binding.capture_spec().value_spec()
            },
            (ResultStep::Payload(a),Effect::Replace(value))=>a.witnessed() && a.inverse().wf() && a.inverse().after().value==value
                && cleanup::selected(episode,port,a.inverse().owner()) && self.next==call.branch.matched,
            _=>false,
        }
    }
    pub open spec fn in_slot<A,R,M,X>(&self,slot:Option<Action<A,R,T,M,X>>)->bool {
        slot.is_some() && match self.result {
            ResultStep::Scalar {inverse,..}=>slot.unwrap() is Value && slot.unwrap()->Value_0==inverse@,
            ResultStep::Payload(a)=>match slot.unwrap() {
                ChildCleanup::Callback(cleanup::Cleanup::Payload {inverse,retained})=>inverse==a.inverse() && retained.opaque_spec()==Some(inverse.owner()),_=>false,
            },
        }
    }
    proof fn retain(tracked &self,tracked receipts:&mut registration::ReceiptMap,i:int)
        requires registration::witnesses(*old(receipts)),
            match self.result {ResultStep::Scalar {write,..}=>write.admission.registration().certified(),ResultStep::Payload(a)=>a.witnessed()},
        ensures registration::witnesses(*final(receipts)),self.witnessed(*final(receipts),i),
            forall|k:(int,bool)|k.0!=i ==> #[trigger] final(receipts).contains_key(k)==old(receipts).contains_key(k)
                && (old(receipts).contains_key(k) ==> final(receipts)[k]==old(receipts)[k]),
    {
        let ghost prior=*receipts;
        match &self.result {
            ResultStep::Scalar {write,..}=>{write.admission.evidence.borrow().retain(receipts,i);
                assert forall|k:(int,bool)|k.0!=i implies #[trigger] receipts.contains_key(k)==prior.contains_key(k)
                    && (prior.contains_key(k) ==> receipts[k]==prior[k]) by {}},
            ResultStep::Payload(a)=>{a.retain(receipts,i);
                assert forall|k:(int,bool)|k.0!=i implies #[trigger] receipts.contains_key(k)==prior.contains_key(k)
                    && (prior.contains_key(k) ==> receipts[k]==prior[k]) by {}},
        }
    }
}
pub open spec fn next<T:?Sized>(code_len:nat,steps:Seq<Step<T>>)->Option<usize> {if steps.len()==0 {if code_len==0 {None} else {Some(0)}} else {steps.last().next}}
pub open spec fn tokens<T:?Sized>(steps:Seq<Step<T>>)->Seq<usize> {steps.map(|_:int,s:Step<T>|s.token())}
pub open spec fn prefix<E:ScalarEffect,T:?Sized,M>(code:Seq<Call<E,T>>,ports:Seq<Port>,steps:Seq<Step<T>>,episode:NativeEpisode<Slot<T,M>>)->bool {
    ports.len()==code.len() && forall|i:int|0<=i<steps.len() ==> {
        let s=#[trigger] steps[i];
        &&& Some(s.pc)==next(code.len(),steps.take(i)) && s.pc<code.len()
        &&& s.corresponds(code[s.pc as int],ports[s.pc as int],episode)
        &&& s.next.is_some() ==> s.pc<s.next.unwrap()<code.len()
    }
}
pub open spec fn retained<C,G,A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat)->bool {
    owner.cleanup_state().live(id) && owner.cleanup_state().queues()[id].slots().len()==offset+steps.len()
        && forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).token()==offset+i
            && steps[i].in_slot(owner.cleanup_state().queues()[id].slots()[offset+i])
}
pub struct Report<T:?Sized> {pub steps:Vec<Step<T>>,pub failure:Option<Failure<T>>,pub receipts:Tracked<registration::ReceiptMap>}
impl<T:?Sized> Report<T> {
    pub closed spec fn receipts(&self)->registration::ReceiptMap {self.receipts@}
    pub proof fn receipt_witnesses(tracked &self)->(tracked out:&registration::ReceiptMap)
        ensures *out==self.receipts(),
    {self.receipts.borrow()}
    pub open spec fn witnessed(&self)->bool {
        registration::witnesses(self.receipts()) && (forall|i:int|0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).witnessed(self.receipts(),i))
            && (self.failure.is_some() && self.failure.unwrap().receipt@.is_some() ==> self.receipts().contains_key((self.steps.len() as int,false))
                && self.receipts()[(self.steps.len() as int,false)].same(&self.failure.unwrap().receipt@.unwrap()))
    }
    pub open spec fn certified<E:ScalarEffect,M>(&self,code:Seq<Call<E,T>>,ports:Seq<Port>,episode:NativeEpisode<Slot<T,M>>)->bool {
        self.witnessed() && prefix(code,ports,self.steps@,episode)
            && match self.failure {None=>next(code.len(),self.steps@).is_none(),Some(f)=>Some(f.pc)==next(code.len(),self.steps@) && f.pc<code.len() && f.explained(code[f.pc as int],ports[f.pc as int],episode)}
    }
    pub open spec fn ordered(&self)->bool {
        (forall|i:int,j:int|#![trigger self.steps@[i],self.steps@[j]] 0<=i<j<self.steps.len() ==> {
            let earlier=self.steps@[i];let later=self.steps@[j];
            &&& earlier.write().journal()==later.write().journal() ==> later.write().follows(&earlier.write())
            &&& earlier.insertion().is_some() && earlier.insertion().unwrap().journal()==later.write().journal() ==> later.write().follows(&earlier.insertion().unwrap())
        }) && (self.failure.is_some() && self.failure.unwrap().receipt@.is_some() ==> forall|i:int|0<=i<self.steps.len() ==> {
            let earlier=#[trigger] self.steps@[i];let failed=self.failure.unwrap().receipt@.unwrap();
            &&& earlier.write().journal()==failed.journal() ==> failed.follows(&earlier.write())
            &&& earlier.insertion().is_some() && earlier.insertion().unwrap().journal()==failed.journal() ==> failed.follows(&earlier.insertion().unwrap())
        })
    }
    proof fn witnesses_valid(&self)
        requires self.witnessed(),ensures registration::witnesses(self.receipts()),
    {}
    pub fn succeeded(&self)->(out:bool) ensures out==self.failure.is_none(), {self.failure.is_none()}
}
fn append_step<E:ScalarEffect,T:?Sized,M>(steps:&mut Vec<Step<T>>,Tracked(receipts):Tracked<&mut registration::ReceiptMap>,step:Step<T>,Ghost(code):Ghost<Seq<Call<E,T>>>,Ghost(ports):Ghost<Seq<Port>>,Ghost(episode):Ghost<NativeEpisode<Slot<T,M>>>)
    requires prefix(code,ports,old(steps)@,episode),
        (Report {steps:*old(steps),failure:None,receipts:Tracked(*old(receipts))}).witnessed(),
        (Report {steps:*old(steps),failure:None,receipts:Tracked(*old(receipts))}).ordered(),
        step.pc<code.len(),Some(step.pc)==next(code.len(),old(steps)@),step.corresponds(code[step.pc as int],ports[step.pc as int],episode),
        step.next.is_some() ==> step.pc<step.next.unwrap()<code.len(),
        forall|k:(int,bool)|old(receipts).contains_key(k) && #[trigger] old(receipts)[k].journal()==step.write().journal() ==> step.write().follows(&old(receipts)[k]),
    ensures final(steps)@==old(steps)@.push(step),prefix(code,ports,final(steps)@,episode),
        (Report {steps:*final(steps),failure:None,receipts:Tracked(*final(receipts))}).witnessed(),
        (Report {steps:*final(steps),failure:None,receipts:Tracked(*final(receipts))}).ordered(),
{
    let ghost earlier=steps@;let ghost old_receipts=*receipts;
    proof {
        assert(match step.result {ResultStep::Scalar {write,..}=>write.admission.registration().certified(),ResultStep::Payload(a)=>a.witnessed()}) by {reveal(Step::corresponds);}
        assert forall|i:int|0<=i<earlier.len() implies {
            let old_step=#[trigger] earlier[i];
            &&& old_step.write().journal()==step.write().journal() ==> step.write().follows(&old_step.write())
            &&& old_step.insertion().is_some() && old_step.insertion().unwrap().journal()==step.write().journal() ==> step.write().follows(&old_step.insertion().unwrap())
        } by {assert(earlier[i].witnessed(*receipts,i));}
        step.retain(receipts,steps.len() as int);
    }
    steps.push(step);
    proof {
        assert forall|i:int|0<=i<steps.len() implies (#[trigger] steps@[i]).witnessed(*receipts,i) by {
            if i<earlier.len() {
                assert(earlier[i].witnessed(old_receipts,i));assert(receipts.contains_key((i,false)));
                if earlier[i].insertion().is_some() {assert(receipts.contains_key((i,true)));}
            }
        }
    }
}
/// Assemble the authentic failed prefix separately from the interpreter loop.
/// This preserves the same runtime result and keeps the ordering proof local.
fn failed_report<E:ScalarEffect,T:?Sized,M>(steps:Vec<Step<T>>,Tracked(receipts):Tracked<registration::ReceiptMap>,failure:Failure<T>,Ghost(code):Ghost<Seq<Call<E,T>>>,Ghost(ports):Ghost<Seq<Port>>,Ghost(episode):Ghost<NativeEpisode<Slot<T,M>>>)->(out:Report<T>)
    requires prefix(code,ports,steps@,episode),
        (Report {steps,failure:None,receipts:Tracked(receipts)}).witnessed(),
        (Report {steps,failure:None,receipts:Tracked(receipts)}).ordered(),
        Some(failure.pc)==next(code.len(),steps@),failure.pc<code.len(),
        failure.explained(code[failure.pc as int],ports[failure.pc as int],episode),
        failure.receipt@.is_some() ==> failure.receipt@.unwrap().wf(),
        failure.receipt@.is_some() ==> forall|k:(int,bool)|receipts.contains_key(k) && #[trigger] receipts[k].journal()==failure.receipt@.unwrap().journal() ==> failure.receipt@.unwrap().follows(&receipts[k]),
    ensures out.steps==steps,out.failure==Some(failure),out.certified(code,ports,episode),out.ordered(),
{
    let tracked mut retained=receipts;
    proof {if let Some(receipt)=failure.receipt.borrow() {retained.tracked_insert((steps.len() as int,false),receipt.duplicate());}}
    Report {steps,failure:Some(failure),receipts:Tracked(retained)}
}
impl<C,G,A,R,T:?Sized,M,X> Owner<C,G,A,R,T,M,X> {
    fn execute_call<E:ScalarEffect+Copy>(&mut self,id:usize,pc:usize,port:Port,call:&Call<E,T>,Tracked(previous):Tracked<&registration::ReceiptMap>)->(out:Result<Step<T>,Failure<T>>)
        requires old(self).wf(),old(self).value_state().is_some(),registration::witnesses(*previous),old(self).work_state().accepts(),old(self).cleanup_state().acquisition_open(id),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),final(self).status_links()==old(self).status_links(),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).cleanup_state().acquisition_open(id),
            out.is_err() ==> out->Err_0.explained(*call,port,old(self).value_state().unwrap()),
            out.is_ok() ==> forall|k:(int,bool)|previous.contains_key(k) && #[trigger] previous[k].journal()==out->Ok_0.write().journal() ==> out->Ok_0.write().follows(&previous[k]),
            out.is_err() && out->Err_0.receipt@.is_some() ==> forall|k:(int,bool)|previous.contains_key(k) && #[trigger] previous[k].journal()==out->Err_0.receipt@.unwrap().journal() ==> out->Err_0.receipt@.unwrap().follows(&previous[k]),
            out.is_err() ==> final(self).cleanup_state()==old(self).cleanup_state() && out->Err_0.pc==pc
                && (out->Err_0.receipt@.is_some() ==> out->Err_0.receipt@.unwrap().wf()),
            out.is_ok() ==> {
                let s=out->Ok_0;let q=final(self).cleanup_state().queues()[id];let before=old(self).cleanup_state().queues()[id];
                &&& s.pc==pc && s.corresponds(*call,port,old(self).value_state().unwrap()) && final(self).cleanup_state().live(id)
                &&& s.token()==before.slots().len() && q.slots().len()==before.slots().len()+1 && q.slots().take(s.token() as int)==before.slots()
                &&& s.in_slot(q.slots()[s.token() as int]) && q.protocol().waiting()==before.protocol().waiting().push(s.token())
            },
    {
        hide(Execution::wf);
        match &call.effect {
            Effect::Scalar(effect)=>{
                let capture=match self.capture_native_effect(id,port) {Ok(c)=>c,Err(error)=>{
                    let failure=Failure {pc,error:Error::Capture(error),receipt:Tracked(None),scalar:Ghost(None),payload:Ghost(None)};
                    proof {assert(failure.explained(*call,port,old(self).value_state().unwrap())) by {reveal(Failure::explained);}}
                    return Err(failure);
                }};
                let computation=capture.prepare_following(*effect,Tracked(previous));
                proof {computation.provenance();}
                let ghost cause=computation.prepared().cause();
                let ghost input=(computation.capture().binding(),computation.prepared().expected());
                let write=match self.apply_native_effect(id,computation,call.branch) {
                    Ok(write)=>write,
                    Err(error)=>{
                        proof {self.representation();}
                        let tracked receipt=if error==EffectError::Closed {None} else {Some(self.attempts.borrow().latest())};
                        proof {if receipt.is_some() {
                            assert forall|k:(int,bool)|previous.contains_key(k) && #[trigger] previous[k].journal()==receipt.unwrap().journal() implies receipt.unwrap().follows(&previous[k]) by {
                                receipt.unwrap().after_cover(&cause,&previous[k]);
                            }
                        }}
                        let failure=Failure {pc,error:Error::Scalar(error),receipt:Tracked(receipt),scalar:Ghost(Some(input)),payload:Ghost(None)};
                        proof {assert(failure.explained(*call,port,old(self).value_state().unwrap())) by {reveal(Failure::explained);}}
                        return Err(failure);
                    },
                };
                let ghost inverse=self.cleanup_state().queues()[id].slots()[write.admission.token as int].unwrap()->Value_0;
                proof {assert forall|k:(int,bool)|previous.contains_key(k) && #[trigger] previous[k].journal()==write.admission.registration().write().journal() implies write.admission.registration().write().follows(&previous[k]) by {
                    write.admission.registration().write().after_cover(&cause,&previous[k]);
                }}
                let next=write.admission.next;
                let step=Step {pc,result:ResultStep::Scalar {write,inverse:Ghost(inverse)},next};
                proof {assert(step.corresponds(*call,port,old(self).value_state().unwrap())) by {reveal(Step::corresponds);}}
                Ok(step)
            },
            Effect::Replace(value)=>{
                match self.apply_native_payload_following(id,port,value.clone(),Tracked(previous)) {
                    Ok(a)=>{
                        proof {a.inverse().provenance();}
                        let step=Step {pc,result:ResultStep::Payload(a),next:call.branch.matched};
                        proof {assert(step.corresponds(*call,port,old(self).value_state().unwrap())) by {reveal(Step::corresponds);}}
                        Ok(step)
                    },
                    Err((error,_,payload))=>{
                        let failure=Failure {pc,error:Error::Payload(error),receipt:Tracked(None),scalar:Ghost(None),payload};
                        proof {assert(failure.explained(*call,port,old(self).value_state().unwrap())) by {reveal(Failure::explained);}}
                        Err(failure)
                    },
                }
            },
        }
    }
    pub open spec fn function_admission_failure<E>(&self,id:usize,function:Function<E,T>,ports:Seq<Port>,error:AdmissionError)->bool {
        match error {
            AdmissionError::Closed=>!self.work_state().accepts() || !self.cleanup_state().acquisition_open(id),
            AdmissionError::NoNative=>self.value_state().is_none(),
            AdmissionError::Arity=>ports.len()!=function.code().len(),
            AdmissionError::WrongKey {pc}=>pc<ports.len() && pc<function.code().len() && ports[pc as int].key!=function.code()[pc as int].key,
            AdmissionError::Undeclared {pc}=>pc<ports.len() && self.value_state().is_some() && !access::declared(self.value_state().unwrap(),ports[pc as int]),
        }
    }
    /// The complete declaration list is checked before the first effect. The
    /// same implementation is used by stored roots, Children and managed calls.
    pub fn run_function<E:ScalarEffect+Copy>(&mut self,id:usize,function:&Function<E,T>,ports:&[Port])->(out:Result<Report<T>,AdmissionError>)
        requires old(self).wf(),function.valid(),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),final(self).status_links()==old(self).status_links(),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && old(self).function_admission_failure(id,*function,ports@,out->Err_0),
            out.is_ok() ==> old(self).value_state().is_some() && ports.len()==function.code().len()
                && (forall|i:int|0<=i<ports.len() ==> (#[trigger] ports@[i]).key==function.code()[i].key && access::declared(old(self).value_state().unwrap(),ports@[i]))
                && out->Ok_0.certified(function.code(),ports@,old(self).value_state().unwrap()) && out->Ok_0.ordered()
                && retained(out->Ok_0.steps@,*final(self),id,old(self).cleanup_state().queues()[id].slots().len())
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting()+tokens(out->Ok_0.steps@)
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots(),
    {
        hide(Execution::wf);hide(Report::witnessed);hide(Report::ordered);
        if !self.accepts_acquisition(id) {return Err(AdmissionError::Closed);}
        let episode=match self.native() {Some(e)=>e,None=>return Err(AdmissionError::NoNative)};
        if ports.len()!=function.code.len() {return Err(AdmissionError::Arity);}
        let mut check=0;
        while check<ports.len()
            invariant *self==*old(self),self.wf(),self.value_state()==Some(*episode),ports.len()==function.code().len(),check<=ports.len(),forall|i:int|0<=i<check ==> (#[trigger] ports@[i]).key==function.code()[i].key && access::declared(*episode,ports@[i]),
            decreases ports.len()-check,
        {if ports[check].key!=function.code[check].key {return Err(AdmissionError::WrongKey {pc:check});}
            if !episode.declares_service(ports[check]) {return Err(AdmissionError::Undeclared {pc:check});}check+=1;}
        let ghost initial=*self;let ghost values=self.value_state().unwrap();let ghost offset=self.cleanup_state().queues()[id].slots().len();
        let mut steps=Vec::new();let tracked mut receipts=Map::tracked_empty();let mut pc=if function.code.is_empty() {None} else {Some(0usize)};
        proof {
            function.shape();
            assert((Report {steps,failure:None,receipts:Tracked(receipts)}).witnessed()) by {reveal(Report::witnessed);};
            assert((Report {steps,failure:None,receipts:Tracked(receipts)}).ordered()) by {reveal(Report::ordered);};
        }
        while pc.is_some()
            invariant self.wf(),self.work_state().accepts(),self.cleanup_state().acquisition_open(id),self.execution_journal()==initial.execution_journal(),self.status_links()==initial.status_links(),self.capture()==initial.capture(),self.work_state()==initial.work_state(),self.value_state()==Some(values),self.phase_spec()==initial.phase_spec(),
                initial==*old(self),initial.value_state()==Some(values),initial.cleanup_state().live(id),offset==initial.cleanup_state().queues()[id].slots().len(),
                function.valid(),ports.len()==function.code().len(),
                forall|i:int|0<=i<ports.len() ==> (#[trigger] ports@[i]).key==function.code()[i].key && access::declared(values,ports@[i]),
                prefix(function.code(),ports@,steps@,values),pc==next(function.code().len(),steps@),pc.is_some() ==> pc.unwrap()<function.code().len(),
                retained(steps@,*self,id,offset),(Report {steps,failure:None,receipts:Tracked(receipts)}).witnessed(),(Report {steps,failure:None,receipts:Tracked(receipts)}).ordered(),
                self.cleanup_state().queues()[id].slots().take(offset as int)==initial.cleanup_state().queues()[id].slots(),
                self.cleanup_state().queues()[id].protocol().waiting()==initial.cleanup_state().queues()[id].protocol().waiting()+tokens(steps@),
            decreases if pc.is_some() {function.code.len()-pc.unwrap()} else {0},
        {
            let at=pc.unwrap();let ghost prior=*self;let ghost earlier=steps@;
            proof {(Report {steps,failure:None,receipts:Tracked(receipts)}).witnesses_valid();}
            let step=match self.execute_call(id,at,ports[at],&function.code[at],Tracked(&receipts)) {
                Ok(step)=>step,
                Err(failure)=>{
                    return Ok(failed_report::<E,T,M>(steps,Tracked(receipts),failure,Ghost(function.code()),Ghost(ports@),Ghost(values)));
                },
            };
            proof {
                assert(function.code()[at as int].valid(at as int,function.code().len()));
                assert(step.next.is_some() ==> at<step.next.unwrap()<function.code().len()) by {reveal(Step::corresponds);}
                assert forall|i:int|0<=i<earlier.len() implies (#[trigger] earlier[i]).in_slot(self.cleanup_state().queues()[id].slots()[offset+i]) by {
                    assert(self.cleanup_state().queues()[id].slots().take(step.token() as int)[offset+i]==prior.cleanup_state().queues()[id].slots()[offset+i]);
                }
            }
            pc=step.next;append_step::<E,T,M>(&mut steps,Tracked(&mut receipts),step,Ghost(function.code()),Ghost(ports@),Ghost(values));
            proof {
                assert(tokens(steps@) =~= tokens(earlier).push(step.token()));
                assert(self.cleanup_state().queues()[id].slots().take(offset as int) =~= initial.cleanup_state().queues()[id].slots());
            }
        }
        Ok(Report {steps,failure:None,receipts:Tracked(receipts)})
    }
}
}

#[path = "managed_semantics.rs"]
pub mod semantics;

#[path = "managed_root.rs"]
pub mod root;

#[path = "managed_trace.rs"]
pub mod trace;
