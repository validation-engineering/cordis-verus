//! Heterogeneous native functions. The interpreter, not a callback, owns the
//! operation arguments, selected continuation and successful-prefix inverses.
//! Controlled instructions execute atomically in the kernel. Extensible scalar
//! callbacks use the separate guarded prepare/land path and its explicit boundary.
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
pub enum Effect<E,T:?Sized> {Kernel(super::effect::Instruction),Scalar(E),Replace(Arc<T>)}
impl<E:ScalarEffect,T:?Sized> Effect<E,T> {
    pub open spec fn scalar_code(&self)->Option<super::effect::Code> {
        match self {Self::Kernel(i)=>Some(i.model()),Self::Scalar(e)=>Some(e.model()),Self::Replace(_)=>None}
    }
}
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
    pub fn instructions(&self)->(out:&[Call<E,T>]) ensures out@==self.code(), {self.code.as_slice()}
    /// All branches, including unreachable instructions, exclude callbacks.
    pub open spec fn controlled(&self)->bool {
        forall|i:int|0<=i<self.code().len() ==> !(#[trigger] self.code()[i].effect is Scalar)
    }
    pub fn is_controlled(&self)->(out:bool) ensures out==self.controlled(),
    {
        let mut i=0;
        while i<self.code.len()
            invariant i<=self.code.len(),forall|j:int|0<=j<i ==> !(#[trigger] self.code()[j].effect is Scalar),
            decreases self.code.len()-i,
        {if let Effect::Scalar(_)=&self.code[i].effect {return false;}i+=1;}
        true
    }
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
    pub proof fn equal_binding<R>(&self,other:Self,recipe:RegisteredPlugin<R>,ports:Seq<Port>)
        requires self.code()==other.code(),self.bound(ports,recipe),ensures other.bound(ports,recipe),
    {}
    pub proof fn binding_unique<R>(&self,recipe:RegisteredPlugin<R>,left:Seq<Port>,right:Seq<Port>)
        requires self.bound(left,recipe),self.bound(right,recipe),ensures left==right,
    {
        assert forall|i:int|0<=i<left.len() implies left[i]==right[i] by {
            let a=choose|j:int|0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j]==left[i]
                && forall|k:int|0<=k<j ==> recipe.dependencies_spec()[k].key!=left[i].key;
            let b=choose|j:int|0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j]==right[i]
                && forall|k:int|0<=k<j ==> recipe.dependencies_spec()[k].key!=right[i].key;
            if a<b {assert(recipe.dependencies_spec()[a].key!=right[i].key);} else if b<a {assert(recipe.dependencies_spec()[b].key!=left[i].key);}
        }
        assert(left =~= right);
    }
    /// Resolve every branch before root issuance, including unreachable calls.
    pub fn bind<R>(&self,recipe:&RegisteredPlugin<R>)->(out:Result<Vec<Port>,usize>)
        ensures (exists|ports:Seq<Port>|self.bound(ports,*recipe)) ==> out.is_ok(),
            out.is_ok() ==> self.bound(out->Ok_0@,*recipe),
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
            let port=match recipe.dependency_port(self.code[i].key) {Some(port)=>port,None=>{
                proof {
                    if exists|ports:Seq<Port>|self.bound(ports,*recipe) {
                        let ports=choose|ports:Seq<Port>|self.bound(ports,*recipe);
                        assert(recipe.dependencies_spec().contains(ports[i as int]));
                        let j=choose|j:int|0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j]==ports[i as int];
                        assert(recipe.dependencies_spec()[j].key==self.code()[i as int].key);
                    }
                }
                return Err(i)
            }};
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
            (Error::Capture(super::cursor::StartError::Read(error)),effect)=>effect.scalar_code().is_some() && episode.reversible_read_failed(port,error),
            (Error::Scalar(error),effect)=>effect.scalar_code().is_some() && (effect is Kernel ==> error!=EffectError::Interference) && self.receipt@.is_some() && self.receipt@.unwrap().wf() && self.scalar@.is_some()
                && access::selected(episode,self.scalar@.unwrap().0) && self.scalar@.unwrap().0.port_spec()==port
                && self.receipt@.unwrap().journal()==self.scalar@.unwrap().0.capture_spec().value_spec().journal_spec()
                && self.receipt@.unwrap().event().key==self.scalar@.unwrap().0.capture_spec().value_spec().object().key
                && self.receipt@.unwrap().event().change is Value
                && super::attempt::effect_rejection(self.receipt@.unwrap().event().change->Value_event,effect.scalar_code().unwrap(),self.scalar@.unwrap().1,error),
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
    pub open spec fn inserted_into(&self,link:Option<(joint::Journal,nat)>)->bool {
        self.insertion().is_some()==link.is_some() && (self.insertion().is_some() ==> {
            let receipt=self.insertion().unwrap();receipt.journal()==link.unwrap().0 && receipt.event().key==link.unwrap().1
        })
    }
    pub open spec fn registered(&self,groups:Option<(joint::Journal,nat)>,id:usize)->bool {
        self.write().wf() && joint::groups::registration(self.insertion(),groups,id) && (self.insertion().is_some() ==> {
            let receipt=self.insertion().unwrap();
            &&& receipt.event().after->Cleanup_state.occupied.len()==self.token()+1
            &&& receipt.event().after->Cleanup_state.occupied[self.token() as int]
            &&& receipt.journal()==self.write().journal() ==> receipt.follows(&self.write()) && receipt.event().settled==Some(self.write().at())
            &&& receipt.event().change==if receipt.journal()==self.write().journal() {joint::Change::RegisterInverse {write:self.write().at()}}
                else {joint::Change::Cleanup {event:joint::episode::CleanupChange::Register}}
        })
    }
    pub open spec fn witnessed(&self,receipts:registration::ReceiptMap,i:int)->bool {
        receipts.contains_key((i,false)) && receipts[(i,false)].same(&self.write())
            && (self.insertion().is_some() ==> receipts.contains_key((i,true)) && receipts[(i,true)].same(&self.insertion().unwrap()))
    }
    #[verifier::opaque]
    pub open spec fn corresponds<E:ScalarEffect,M>(&self,call:Call<E,T>,port:Port,episode:NativeEpisode<Slot<T,M>>)->bool {
        match (self.result,call.effect) {
            (ResultStep::Scalar {write,inverse},effect)=>{
                &&& effect.scalar_code().is_some() && write.computed(effect.scalar_code().unwrap(),call.branch) && access::selected(episode,write.binding) && write.binding.port_spec()==port
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
pub type Histories<T> = Map<int,super::history::Witness<super::payload::State<T>>>;
#[verifier::opaque]
pub open spec fn histories_recorded<T:?Sized>(steps:Seq<Step<T>>,witnesses:Histories<T>)->bool {
    forall|i:int|0<=i<steps.len() && (#[trigger] steps[i]).result is Payload ==> {
        let inverse=steps[i].result->Payload_0.inverse();
        witnesses.contains_key(i) && witnesses[i].wf() && witnesses[i].source()==inverse.owner().source() && witnesses[i].events()==inverse.after().states
    }
}
pub struct Report<T:?Sized> {pub steps:Vec<Step<T>>,pub failure:Option<Failure<T>>,pub receipts:Tracked<registration::ReceiptMap>,pub histories:Tracked<Histories<T>>}
impl<T:?Sized> Report<T> {
    pub open spec fn queued_sources(&self,link:Option<(joint::Journal,nat)>)->bool {
        forall|i:int|0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).inserted_into(link)
    }

    pub open spec fn registered(&self,groups:Option<(joint::Journal,nat)>,id:usize)->bool {
        forall|i:int|0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).registered(groups,id)
    }
    pub closed spec fn receipts(&self)->registration::ReceiptMap {self.receipts@}
    pub proof fn receipt_witnesses(tracked &self)->(tracked out:&registration::ReceiptMap)
        ensures *out==self.receipts(),
    {self.receipts.borrow()}
    pub open spec fn witnessed(&self)->bool {
        histories_recorded(self.steps@,self.histories@) && registration::witnesses(self.receipts()) && (forall|i:int|0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).witnessed(self.receipts(),i))
            && (self.failure.is_some() && self.failure.unwrap().receipt@.is_some() ==> self.receipts().contains_key((self.steps.len() as int,false))
                && self.receipts()[(self.steps.len() as int,false)].same(&self.failure.unwrap().receipt@.unwrap()))
    }
    pub open spec fn certified<E:ScalarEffect,M>(&self,code:Seq<Call<E,T>>,ports:Seq<Port>,episode:NativeEpisode<Slot<T,M>>)->bool {
        self.witnessed() && prefix(code,ports,self.steps@,episode)
            && match self.failure {None=>next(code.len(),self.steps@).is_none(),Some(f)=>Some(f.pc)==next(code.len(),self.steps@) && f.pc<code.len() && f.explained(code[f.pc as int],ports[f.pc as int],episode)}
    }
    pub open spec fn no_scalar_interference(&self)->bool {
        match self.failure {Some(f)=>match f.error {Error::Scalar(e)=>e!=EffectError::Interference,_=>true},None=>true}
    }
    /// Derive this from the actual interpreter report and the checked complete
    /// program, not from a plugin's claim that its callback is pure.
    pub proof fn controlled_execution<E:ScalarEffect,M>(&self,function:Function<E,T>,ports:Seq<Port>,episode:NativeEpisode<Slot<T,M>>)
        requires function.controlled(),self.certified(function.code(),ports,episode),
        ensures self.no_scalar_interference(),
    {
        reveal(Failure::explained);
        if let Some(f)=self.failure {
            assert(!(function.code()[f.pc as int].effect is Scalar));
        }
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
fn append_step<E:ScalarEffect,T:?Sized,M>(steps:&mut Vec<Step<T>>,Tracked(receipts):Tracked<&mut registration::ReceiptMap>,Tracked(histories):Tracked<&mut Histories<T>>,step:Step<T>,Ghost(code):Ghost<Seq<Call<E,T>>>,Ghost(ports):Ghost<Seq<Port>>,Ghost(episode):Ghost<NativeEpisode<Slot<T,M>>>)
    requires prefix(code,ports,old(steps)@,episode),
        (Report {steps:*old(steps),failure:None,receipts:Tracked(*old(receipts)),histories:Tracked(*old(histories))}).witnessed(),
        (Report {steps:*old(steps),failure:None,receipts:Tracked(*old(receipts)),histories:Tracked(*old(histories))}).ordered(),
        step.pc<code.len(),Some(step.pc)==next(code.len(),old(steps)@),step.corresponds(code[step.pc as int],ports[step.pc as int],episode),
        step.next.is_some() ==> step.pc<step.next.unwrap()<code.len(),
        forall|k:(int,bool)|old(receipts).contains_key(k) && #[trigger] old(receipts)[k].journal()==step.write().journal() ==> step.write().follows(&old(receipts)[k]),
    ensures final(steps)@==old(steps)@.push(step),prefix(code,ports,final(steps)@,episode),
        (Report {steps:*final(steps),failure:None,receipts:Tracked(*final(receipts)),histories:Tracked(*final(histories))}).witnessed(),
        (Report {steps:*final(steps),failure:None,receipts:Tracked(*final(receipts)),histories:Tracked(*final(histories))}).ordered(),
        final(receipts).contains_key((-1int,false))==old(receipts).contains_key((-1int,false)),
        old(receipts).contains_key((-1int,false)) ==> final(receipts)[(-1int,false)]==old(receipts)[(-1int,false)],
{
    proof {reveal(histories_recorded);}
    let ghost earlier=steps@;let ghost old_receipts=*receipts;
    proof {
        assert(match step.result {ResultStep::Scalar {write,..}=>write.admission.registration().certified(),ResultStep::Payload(a)=>a.witnessed()}) by {reveal(Step::corresponds);}
        assert forall|i:int|0<=i<earlier.len() implies {
            let old_step=#[trigger] earlier[i];
            &&& old_step.write().journal()==step.write().journal() ==> step.write().follows(&old_step.write())
            &&& old_step.insertion().is_some() && old_step.insertion().unwrap().journal()==step.write().journal() ==> step.write().follows(&old_step.insertion().unwrap())
        } by {assert(earlier[i].witnessed(*receipts,i));}
        step.retain(receipts,steps.len() as int);
        assert(receipts.contains_key((-1int,false))==old_receipts.contains_key((-1int,false)));
        if old_receipts.contains_key((-1int,false)) {assert(receipts[(-1int,false)]==old_receipts[(-1int,false)]);}
        match &step.result {ResultStep::Payload(a)=>histories.tracked_insert(steps.len() as int,a.history_witness()),_=>{}}
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
fn failed_report<E:ScalarEffect,T:?Sized,M>(steps:Vec<Step<T>>,Tracked(receipts):Tracked<registration::ReceiptMap>,Tracked(histories):Tracked<Histories<T>>,failure:Failure<T>,Ghost(code):Ghost<Seq<Call<E,T>>>,Ghost(ports):Ghost<Seq<Port>>,Ghost(episode):Ghost<NativeEpisode<Slot<T,M>>>)->(out:Report<T>)
    requires prefix(code,ports,steps@,episode),
        (Report {steps,failure:None,receipts:Tracked(receipts),histories:Tracked(histories)}).witnessed(),
        (Report {steps,failure:None,receipts:Tracked(receipts),histories:Tracked(histories)}).ordered(),
        Some(failure.pc)==next(code.len(),steps@),failure.pc<code.len(),
        failure.explained(code[failure.pc as int],ports[failure.pc as int],episode),
        failure.receipt@.is_some() ==> failure.receipt@.unwrap().wf(),
        failure.receipt@.is_some() ==> forall|k:(int,bool)|receipts.contains_key(k) && #[trigger] receipts[k].journal()==failure.receipt@.unwrap().journal() ==> failure.receipt@.unwrap().follows(&receipts[k]),
    ensures out.steps==steps,out.failure==Some(failure),out.certified(code,ports,episode),out.ordered(),out.recovery_history(),
        out.predecessor()==if receipts.contains_key((-1int,false)) {Some(receipts[(-1int,false)])} else {None},
{
    let tracked mut retained=receipts;
    proof {if let Some(receipt)=failure.receipt.borrow() {retained.tracked_insert((steps.len() as int,false),receipt.duplicate());}}
    let report=Report {steps,failure:Some(failure),receipts:Tracked(retained),histories:Tracked(histories)};
    proof {report.establish_recovery(code,ports,episode);}
    report
}
impl<C,G,A,R,T:?Sized,M,X> Owner<C,G,A,R,T,M,X> {
    #[allow(clippy::too_many_arguments)] // Includes the erased receipt and borrowed execution guards.
    fn execute_call<E:ScalarEffect+Copy>(&mut self,id:usize,pc:usize,port:Port,call:&Call<E,T>,Tracked(previous):Tracked<&registration::ReceiptMap>,mode:&mut Option<protected::Context<'_>>,typed:&mut Option<protected_typed::Context<'_,T,M>>)->(out:Result<Step<T>,Failure<T>>)
        requires old(typed).is_some() ==> old(mode).is_none() && old(typed)->Some_0.wf()
                && old(typed)->Some_0.for_call(old(self).value_state().unwrap(),pc,port) && call.effect is Replace,
            old(mode).is_some() ==> old(mode)->Some_0.wf() && old(mode)->Some_0.for_call(old(self).value_state().unwrap(),pc,port) && call.effect is Kernel,
            old(self).wf(),old(self).value_state().is_some(),registration::witnesses(*previous),old(self).work_state().accepts(),old(self).cleanup_state().acquisition_open(id),
        ensures final(typed).is_some()==old(typed).is_some(),
            old(typed).is_some() && old(typed)->Some_0.revisions()[old(typed)->Some_0.routes()[pc as int] as int] as int
                +old(typed)->Some_0.states()[old(typed)->Some_0.routes()[pc as int] as int].depth as int+2<=u64::MAX ==> out.is_ok(),
            final(typed).is_some() ==> final(typed)->Some_0.wf() && final(typed)->Some_0.shape(&old(typed)->Some_0)
                && (out.is_err() ==> final(typed)->Some_0.states()==old(typed)->Some_0.states() && final(typed)->Some_0.revisions()==old(typed)->Some_0.revisions())
                && (out.is_ok() ==> {
                    let s=out->Ok_0;let index=old(typed)->Some_0.routes()[pc as int] as int;
                    &&& s.result is Payload && s.before()==semantics::Value::Payload(old(typed)->Some_0.states()[index])
                    &&& s.result->Payload_0.inverse().before().revision==old(typed)->Some_0.revisions()[index]
                    &&& s.address()==super::service_composition::Address {journal:old(typed)->Some_0.targets()[index].journal_spec(),key:old(typed)->Some_0.targets()[index].key()}
                    &&& final(typed)->Some_0.states()==old(typed)->Some_0.states().update(index,s.after()->Payload_0)
                    &&& final(typed)->Some_0.revisions()==old(typed)->Some_0.revisions().update(index,s.result->Payload_0.inverse().after().revision)
                }),
            old(mode).is_some() && super::effect::operation(call.effect.scalar_code().unwrap())(old(mode)->Some_0.states()[old(mode)->Some_0.index(pc) as int]).is_some() ==> out.is_ok(),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.shape(&old(mode)->Some_0)
                && (out.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states())
                && (out.is_ok() ==> {
                    let s=out->Ok_0;let index=old(mode)->Some_0.index(pc);
                    &&& s.result is Scalar && s.before()==semantics::Value::Scalar(old(mode)->Some_0.states()[index as int])
                    &&& s.address()==super::service_composition::Address {journal:old(mode)->Some_0.targets()[index as int].journal_spec(),key:old(mode)->Some_0.targets()[index as int].object().key}
                    &&& final(mode)->Some_0.states()==old(mode)->Some_0.states().update(index as int,s.after()->Scalar_0)
                }),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            old(self).cleanup_state().live(id) ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                && final(self).cleanup_state().queues()[id].issued()==old(self).cleanup_state().queues()[id].issued()
                && final(self).cleanup_state().queues()[id].protocol().selected()==old(self).cleanup_state().queues()[id].protocol().selected(),
            final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link(),
            final(self).cleanup_state().link()==old(self).cleanup_state().link(),
            final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),final(self).status_links()==old(self).status_links(),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).cleanup_state().acquisition_open(id),
            out.is_err() ==> out->Err_0.explained(*call,port,old(self).value_state().unwrap()),
            out.is_ok() ==> forall|k:(int,bool)|previous.contains_key(k) && #[trigger] previous[k].journal()==out->Ok_0.write().journal() ==> out->Ok_0.write().follows(&previous[k]),
            out.is_err() && out->Err_0.receipt@.is_some() ==> forall|k:(int,bool)|previous.contains_key(k) && #[trigger] previous[k].journal()==out->Err_0.receipt@.unwrap().journal() ==> out->Err_0.receipt@.unwrap().follows(&previous[k]),
            out.is_err() ==> final(self).cleanup_state()==old(self).cleanup_state() && out->Err_0.pc==pc
                && (out->Err_0.receipt@.is_some() ==> out->Err_0.receipt@.unwrap().wf()),
            out.is_ok() ==> {
                let s=out->Ok_0;let q=final(self).cleanup_state().queues()[id];let before=old(self).cleanup_state().queues()[id];
                &&& s.inserted_into(q.link())
                &&& s.registered(final(self).cleanup_state().link(),id)
                &&& s.pc==pc && s.corresponds(*call,port,old(self).value_state().unwrap()) && final(self).cleanup_state().live(id)
                &&& s.token()==before.slots().len() && q.slots().len()==before.slots().len()+1 && q.slots().take(s.token() as int)==before.slots()
                &&& s.in_slot(q.slots()[s.token() as int]) && q.protocol().waiting()==before.protocol().waiting().push(s.token())
            },
    {
        hide(Execution::wf);hide(joint::valid);hide(joint::step);
        match &call.effect {
            Effect::Kernel(instruction)=>{
                let capture=match mode {
                    Some(context)=>context.capture(self,id,pc,port),
                    None=>match self.capture_native_effect(id,port) {Ok(c)=>c,Err(error)=>{
                    let failure=Failure {pc,error:Error::Capture(error),receipt:Tracked(None),scalar:Ghost(None),payload:Ghost(None)};
                    proof {assert(failure.explained(*call,port,old(self).value_state().unwrap())) by {reveal(Failure::explained);}}
                    return Err(failure);
                }},
                };
                proof {capture.provenance();}
                let ghost binding=capture.binding();
                let result=match mode {
                    Some(context)=>context.apply(self,id,pc,capture,*instruction,call.branch,Tracked(previous)),
                    None=>self.apply_native_controlled(id,capture,*instruction,call.branch,Tracked(previous)),
                };
                let write=match result {
                    Ok(write)=>write,
                    Err(error)=>{
                        proof {self.representation();}
                        let tracked receipt=Some(self.attempts.borrow().latest());
                        let ghost input=(binding,self.value_attempts().event().before());
                        let failure=Failure {pc,error:Error::Scalar(error),receipt:Tracked(receipt),scalar:Ghost(Some(input)),payload:Ghost(None)};
                        proof {assert(failure.explained(*call,port,old(self).value_state().unwrap())) by {reveal(Failure::explained);}}
                        return Err(failure);
                    },
                };
                let ghost inverse=self.cleanup_state().queues()[id].slots()[write.admission.token as int].unwrap()->Value_0;
                let next=write.admission.next;
                let step=Step {pc,result:ResultStep::Scalar {write,inverse:Ghost(inverse)},next};
                proof {
                    assert(step.corresponds(*call,port,old(self).value_state().unwrap())) by {reveal(Step::corresponds);}
                    assert(step.registered(self.cleanup_state().link(),id));
                    if mode.is_some() {
                        assert(step.before()==semantics::Value::Scalar(old(mode)->Some_0.states()[old(mode)->Some_0.index(pc) as int]));
                        assert(step.after()==semantics::Value::Scalar(self.value_attempts().event().after()));
                    }
                }
                Ok(step)
            },
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
                proof {
                    assert(step.corresponds(*call,port,old(self).value_state().unwrap())) by {reveal(Step::corresponds);}
                    assert(step.registered(self.cleanup_state().link(),id));
                }
                Ok(step)
            },
            Effect::Replace(value)=>{
                let result=match typed {
                    Some(context)=>context.apply(self,id,pc,port,value.clone(),Tracked(previous)),
                    None=>self.apply_native_payload_following(id,port,value.clone(),Tracked(previous)),
                };
                match result {
                    Ok(a)=>{
                        proof {a.inverse().provenance();a.registration_facts(self.cleanup_state().queues()[id].link(),self.cleanup_state().queues()[id].observation());}
                        let step=Step {pc,result:ResultStep::Payload(a),next:call.branch.matched};
                        proof {
                            assert(step.corresponds(*call,port,old(self).value_state().unwrap())) by {reveal(Step::corresponds);}
                            assert(step.registered(self.cleanup_state().link(),id));
                        }
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
        ensures final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            old(self).cleanup_state().live(id) ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                && final(self).cleanup_state().queues()[id].issued()==old(self).cleanup_state().queues()[id].issued()
                && final(self).cleanup_state().queues()[id].protocol().selected()==old(self).cleanup_state().queues()[id].protocol().selected(),
            final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).cleanup_state().link()==old(self).cleanup_state().link(),final(self).status_links()==old(self).status_links(),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && old(self).function_admission_failure(id,*function,ports@,out->Err_0),
            out.is_ok() ==> old(self).value_state().is_some() && ports.len()==function.code().len()
                && (forall|i:int|0<=i<ports.len() ==> (#[trigger] ports@[i]).key==function.code()[i].key && access::declared(old(self).value_state().unwrap(),ports@[i]))
                && out->Ok_0.queued_sources(final(self).cleanup_state().queues()[id].link())
                && out->Ok_0.registered(final(self).cleanup_state().link(),id)
                && out->Ok_0.certified(function.code(),ports@,old(self).value_state().unwrap()) && out->Ok_0.ordered() && out->Ok_0.recovery_history()
                && retained(out->Ok_0.steps@,*final(self),id,old(self).cleanup_state().queues()[id].slots().len())
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting()+tokens(out->Ok_0.steps@)
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots(),
    {self.run_function_following(id,function,ports,Tracked(None))}

    // Isolate this loop from unrelated solver contexts; resource limits stay unchanged.
    #[verifier::spinoff_prover]
    pub(crate) fn run_function_following<E:ScalarEffect+Copy>(&mut self,id:usize,function:&Function<E,T>,ports:&[Port],Tracked(cause):Tracked<Option<joint::Receipt>>)->(out:Result<Report<T>,AdmissionError>)
        requires old(self).wf(),function.valid(),cause.is_some() ==> cause.unwrap().wf(),
        ensures final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            old(self).cleanup_state().live(id) ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                && final(self).cleanup_state().queues()[id].issued()==old(self).cleanup_state().queues()[id].issued()
                && final(self).cleanup_state().queues()[id].protocol().selected()==old(self).cleanup_state().queues()[id].protocol().selected(),
            out.is_ok() ==> out->Ok_0.after(cause),final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).cleanup_state().link()==old(self).cleanup_state().link(),final(self).status_links()==old(self).status_links(),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && old(self).function_admission_failure(id,*function,ports@,out->Err_0),
            out.is_ok() ==> old(self).value_state().is_some() && ports.len()==function.code().len()
                && (forall|i:int|0<=i<ports.len() ==> (#[trigger] ports@[i]).key==function.code()[i].key && access::declared(old(self).value_state().unwrap(),ports@[i]))
                && out->Ok_0.queued_sources(final(self).cleanup_state().queues()[id].link())
                && out->Ok_0.registered(final(self).cleanup_state().link(),id)
                && out->Ok_0.certified(function.code(),ports@,old(self).value_state().unwrap()) && out->Ok_0.ordered() && out->Ok_0.recovery_history()
                && retained(out->Ok_0.steps@,*final(self),id,old(self).cleanup_state().queues()[id].slots().len())
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting()+tokens(out->Ok_0.steps@)
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots(),
    {
        let mut mode=None;
        self.run_function_with(id,function,ports,Tracked(cause),&mut mode,Ghost(None))
    }

    #[verifier::rlimit(30)]
    pub(crate) fn run_function_with<E:ScalarEffect+Copy>(&mut self,id:usize,function:&Function<E,T>,ports:&[Port],Tracked(cause):Tracked<Option<joint::Receipt>>,mode:&mut Option<protected::Context<'_>>,Ghost(expected):Ghost<Option<Seq<Step<T>>>>)->(out:Result<Report<T>,AdmissionError>)
        requires expected.is_some() ==> old(mode).is_some() && protected::plan(function.code(),expected.unwrap())
                && protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap()),
            old(mode).is_some() ==> old(mode)->Some_0.wf() && old(self).value_state().is_some()
                && old(mode)->Some_0.supports(old(self).value_state().unwrap(),ports@) && protected::kernel_only(function.code()),
            old(self).wf(),function.valid(),cause.is_some() ==> cause.unwrap().wf(),
        ensures expected.is_some() && out.is_ok() ==> out->Ok_0.failure.is_none() && protected::same(out->Ok_0.steps@,expected.unwrap()),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.shape(&old(mode)->Some_0)
                && (out.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states())
                && (out.is_ok() ==> protected::addressed(old(mode)->Some_0.targets(),old(mode)->Some_0.routes(),out->Ok_0.steps@)
                    && protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.steps@)
                    && final(mode)->Some_0.states()==protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.steps@)),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            old(self).cleanup_state().live(id) ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                && final(self).cleanup_state().queues()[id].issued()==old(self).cleanup_state().queues()[id].issued()
                && final(self).cleanup_state().queues()[id].protocol().selected()==old(self).cleanup_state().queues()[id].protocol().selected(),
            out.is_ok() ==> out->Ok_0.after(cause),final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).cleanup_state().link()==old(self).cleanup_state().link(),final(self).status_links()==old(self).status_links(),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && old(self).function_admission_failure(id,*function,ports@,out->Err_0),
            out.is_ok() ==> old(self).value_state().is_some() && ports.len()==function.code().len()
                && (forall|i:int|0<=i<ports.len() ==> (#[trigger] ports@[i]).key==function.code()[i].key && access::declared(old(self).value_state().unwrap(),ports@[i]))
                && out->Ok_0.queued_sources(final(self).cleanup_state().queues()[id].link())
                && out->Ok_0.registered(final(self).cleanup_state().link(),id)
                && out->Ok_0.certified(function.code(),ports@,old(self).value_state().unwrap()) && out->Ok_0.ordered() && out->Ok_0.recovery_history()
                && retained(out->Ok_0.steps@,*final(self),id,old(self).cleanup_state().queues()[id].slots().len())
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting()+tokens(out->Ok_0.steps@)
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots(),
    {
        let mut typed=None;
        self.run_function_in(id,function,ports,Tracked(cause),mode,Ghost(expected),&mut typed)
    }
    #[verifier::rlimit(30)]
    #[verifier::spinoff_prover]
    #[allow(clippy::too_many_arguments)] // Includes the erased receipt and borrowed execution guards.
    pub(crate) fn run_function_in<E:ScalarEffect+Copy>(&mut self,id:usize,function:&Function<E,T>,ports:&[Port],Tracked(cause):Tracked<Option<joint::Receipt>>,mode:&mut Option<protected::Context<'_>>,Ghost(expected):Ghost<Option<Seq<Step<T>>>>,typed:&mut Option<protected_typed::Context<'_,T,M>>)->(out:Result<Report<T>,AdmissionError>)
        requires old(typed).is_some() ==> old(mode).is_none() && old(typed)->Some_0.wf() && old(self).value_state().is_some()
                && old(typed)->Some_0.supports(old(self).value_state().unwrap(),ports@) && protected_typed::typed_only(function.code())
                && old(typed)->Some_0.budget(function.code().len()),
            expected.is_some() ==> old(mode).is_some() && protected::plan(function.code(),expected.unwrap())
                && protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap()),
            old(mode).is_some() ==> old(mode)->Some_0.wf() && old(self).value_state().is_some()
                && old(mode)->Some_0.supports(old(self).value_state().unwrap(),ports@) && protected::kernel_only(function.code()),
            old(self).wf(),function.valid(),cause.is_some() ==> cause.unwrap().wf(),
        ensures final(typed).is_some()==old(typed).is_some(),
            final(typed).is_some() ==> final(typed)->Some_0.wf() && final(typed)->Some_0.shape(&old(typed)->Some_0)
                && (out.is_err() ==> final(typed)->Some_0.states()==old(typed)->Some_0.states() && final(typed)->Some_0.revisions()==old(typed)->Some_0.revisions())
                && (out.is_ok() ==> out->Ok_0.failure.is_none()
                    && protected_typed::addressed(old(typed)->Some_0.targets(),old(typed)->Some_0.routes(),out->Ok_0.steps@)
                    && protected_typed::execution(old(typed)->Some_0.states(),old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out->Ok_0.steps@)
                    && final(typed)->Some_0.states()==protected_typed::after(old(typed)->Some_0.states(),old(typed)->Some_0.routes(),out->Ok_0.steps@)
                    && final(typed)->Some_0.revisions()==protected_typed::clocks(old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out->Ok_0.steps@)),
            expected.is_some() && out.is_ok() ==> out->Ok_0.failure.is_none() && protected::same(out->Ok_0.steps@,expected.unwrap()),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.shape(&old(mode)->Some_0)
                && (out.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states())
                && (out.is_ok() ==> protected::addressed(old(mode)->Some_0.targets(),old(mode)->Some_0.routes(),out->Ok_0.steps@)
                    && protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.steps@)
                    && final(mode)->Some_0.states()==protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.steps@)),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            old(self).cleanup_state().live(id) ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                && final(self).cleanup_state().queues()[id].issued()==old(self).cleanup_state().queues()[id].issued()
                && final(self).cleanup_state().queues()[id].protocol().selected()==old(self).cleanup_state().queues()[id].protocol().selected(),
            out.is_ok() ==> out->Ok_0.after(cause),final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).cleanup_state().link()==old(self).cleanup_state().link(),final(self).status_links()==old(self).status_links(),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && old(self).function_admission_failure(id,*function,ports@,out->Err_0),
            out.is_ok() ==> old(self).value_state().is_some() && ports.len()==function.code().len()
                && (forall|i:int|0<=i<ports.len() ==> (#[trigger] ports@[i]).key==function.code()[i].key && access::declared(old(self).value_state().unwrap(),ports@[i]))
                && out->Ok_0.queued_sources(final(self).cleanup_state().queues()[id].link())
                && out->Ok_0.registered(final(self).cleanup_state().link(),id)
                && out->Ok_0.certified(function.code(),ports@,old(self).value_state().unwrap()) && out->Ok_0.ordered() && out->Ok_0.recovery_history()
                && retained(out->Ok_0.steps@,*final(self),id,old(self).cleanup_state().queues()[id].slots().len())
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting()+tokens(out->Ok_0.steps@)
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots(),
    {
        let mut mixed=None;
        self.run_function_guarded(id,function,ports,Tracked(cause),mode,Ghost(expected),typed,&mut mixed,Ghost(None))
    }
    #[verifier::rlimit(30)]
    #[verifier::spinoff_prover]
    #[allow(clippy::too_many_arguments)] // Includes erased plans and borrowed guards.
    pub(crate) fn run_function_guarded<E:ScalarEffect+Copy>(&mut self,id:usize,function:&Function<E,T>,ports:&[Port],Tracked(cause):Tracked<Option<joint::Receipt>>,mode:&mut Option<protected::Context<'_>>,Ghost(expected):Ghost<Option<Seq<Step<T>>>>,typed:&mut Option<protected_typed::Context<'_,T,M>>,mixed:&mut Option<protected_mixed::Context<'_,T,M>>,Ghost(mixed_expected):Ghost<Option<Seq<Step<T>>>>)->(out:Result<Report<T>,AdmissionError>)
        requires old(mixed).is_some()==mixed_expected.is_some(),
            old(mixed).is_some() ==> old(mode).is_none() && old(typed).is_none() && expected.is_none()
                && old(mixed)->Some_0.wf() && old(self).value_state().is_some()
                && old(mixed)->Some_0.supports(old(self).value_state().unwrap(),ports@,function.code(),mixed_expected.unwrap())
                && old(mixed)->Some_0.payload->Some_0.budget(function.code().len())
                && protected_mixed::plan(function.code(),mixed_expected.unwrap())
                && protected::execution(old(mixed)->Some_0.scalar->Some_0.states(),old(mixed)->Some_0.scalar->Some_0.routes(),protected_mixed::scalars(mixed_expected.unwrap())),
            old(typed).is_some() ==> old(mode).is_none() && old(typed)->Some_0.wf() && old(self).value_state().is_some()
                && old(typed)->Some_0.supports(old(self).value_state().unwrap(),ports@) && protected_typed::typed_only(function.code())
                && old(typed)->Some_0.budget(function.code().len()),
            expected.is_some() ==> old(mode).is_some() && protected::plan(function.code(),expected.unwrap())
                && protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap()),
            old(mode).is_some() ==> old(mode)->Some_0.wf() && old(self).value_state().is_some()
                && old(mode)->Some_0.supports(old(self).value_state().unwrap(),ports@) && protected::kernel_only(function.code()),
            old(self).wf(),function.valid(),cause.is_some() ==> cause.unwrap().wf(),
        ensures final(mixed).is_some()==old(mixed).is_some(),
            final(mixed).is_some() ==> final(mixed)->Some_0.wf() && final(mixed)->Some_0.shape(&old(mixed)->Some_0)
                && (out.is_err() ==> *final(mixed)==*old(mixed))
                && (out.is_ok() ==> out->Ok_0.failure.is_none() && protected_mixed::same(out->Ok_0.steps@,mixed_expected.unwrap())
                    && final(mixed)->Some_0.trace(&old(mixed)->Some_0,out->Ok_0.steps@)),
            final(typed).is_some()==old(typed).is_some(),
            final(typed).is_some() ==> final(typed)->Some_0.wf() && final(typed)->Some_0.shape(&old(typed)->Some_0)
                && (out.is_err() ==> final(typed)->Some_0.states()==old(typed)->Some_0.states() && final(typed)->Some_0.revisions()==old(typed)->Some_0.revisions())
                && (out.is_ok() ==> out->Ok_0.failure.is_none()
                    && protected_typed::addressed(old(typed)->Some_0.targets(),old(typed)->Some_0.routes(),out->Ok_0.steps@)
                    && protected_typed::execution(old(typed)->Some_0.states(),old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out->Ok_0.steps@)
                    && final(typed)->Some_0.states()==protected_typed::after(old(typed)->Some_0.states(),old(typed)->Some_0.routes(),out->Ok_0.steps@)
                    && final(typed)->Some_0.revisions()==protected_typed::clocks(old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out->Ok_0.steps@)),
            expected.is_some() && out.is_ok() ==> out->Ok_0.failure.is_none() && protected::same(out->Ok_0.steps@,expected.unwrap()),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.shape(&old(mode)->Some_0)
                && (out.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states())
                && (out.is_ok() ==> protected::addressed(old(mode)->Some_0.targets(),old(mode)->Some_0.routes(),out->Ok_0.steps@)
                    && protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.steps@)
                    && final(mode)->Some_0.states()==protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.steps@)),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            old(self).cleanup_state().live(id) ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                && final(self).cleanup_state().queues()[id].issued()==old(self).cleanup_state().queues()[id].issued()
                && final(self).cleanup_state().queues()[id].protocol().selected()==old(self).cleanup_state().queues()[id].protocol().selected(),
            out.is_ok() ==> out->Ok_0.after(cause),final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).cleanup_state().link()==old(self).cleanup_state().link(),final(self).status_links()==old(self).status_links(),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && old(self).function_admission_failure(id,*function,ports@,out->Err_0),
            out.is_ok() ==> old(self).value_state().is_some() && ports.len()==function.code().len()
                && (forall|i:int|0<=i<ports.len() ==> (#[trigger] ports@[i]).key==function.code()[i].key && access::declared(old(self).value_state().unwrap(),ports@[i]))
                && out->Ok_0.queued_sources(final(self).cleanup_state().queues()[id].link())
                && out->Ok_0.registered(final(self).cleanup_state().link(),id)
                && out->Ok_0.certified(function.code(),ports@,old(self).value_state().unwrap()) && out->Ok_0.ordered() && out->Ok_0.recovery_history()
                && retained(out->Ok_0.steps@,*final(self),id,old(self).cleanup_state().queues()[id].slots().len())
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting()+tokens(out->Ok_0.steps@)
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots(),
    {
        hide(protected_mixed::Context::landed);hide(protected_mixed::pair);hide(protected_mixed::same);
        hide(Step::corresponds);
        hide(Execution::wf);hide(Report::witnessed);hide(Report::ordered);hide(joint::valid);hide(joint::step);
        if !self.accepts_acquisition(id) {return Err(AdmissionError::Closed);}
        let episode=match self.native() {Some(e)=>e,None=>return Err(AdmissionError::NoNative)};
        if ports.len()!=function.code.len() {return Err(AdmissionError::Arity);}
        let mut check=0;
        while check<ports.len()
            invariant *mixed==*old(mixed),mixed.is_some()==mixed_expected.is_some(),
                mixed.is_some() ==> mixed->Some_0.wf() && mode.is_none() && typed.is_none(),
                *typed==*old(typed),typed.is_some() ==> typed->Some_0.wf() && mode.is_none() && typed->Some_0.supports(self.value_state().unwrap(),ports@) && protected_typed::typed_only(function.code()) && typed->Some_0.budget(function.code().len()),
                *mode==*old(mode),mode.is_some() ==> mode->Some_0.wf(),
                expected.is_some() ==> mode.is_some() && protected::plan(function.code(),expected.unwrap()) && protected::execution(mode->Some_0.states(),mode->Some_0.routes(),expected.unwrap()),*self==*old(self),self.wf(),self.value_state()==Some(*episode),ports.len()==function.code().len(),check<=ports.len(),forall|i:int|0<=i<check ==> (#[trigger] ports@[i]).key==function.code()[i].key && access::declared(*episode,ports@[i]),
            decreases ports.len()-check,
        {if ports[check].key!=function.code[check].key {return Err(AdmissionError::WrongKey {pc:check});}
            if !episode.declares_service(ports[check]) {return Err(AdmissionError::Undeclared {pc:check});}check+=1;}
        let ghost initial=*self;let ghost values=self.value_state().unwrap();let ghost offset=self.cleanup_state().queues()[id].slots().len();
        let mut steps=Vec::new();let tracked mut receipts=Map::tracked_empty();let tracked mut histories=Map::tracked_empty();let mut pc=if function.code.is_empty() {None} else {Some(0usize)};
        let ghost preceding=cause;
        proof {
            if mixed.is_some() {mixed->Some_0.begin();reveal(protected_mixed::same);assert(mixed_expected.unwrap().take(0) =~= Seq::empty());}
            if typed.is_some() {protected_typed::empty::<T>(typed->Some_0.states(),typed->Some_0.revisions(),typed->Some_0.routes());protected_typed::address_empty::<T>(typed->Some_0.targets(),typed->Some_0.routes());}
            if mode.is_some() {protected::empty::<T>(mode->Some_0.states(),mode->Some_0.routes());}
            if expected.is_some() {assert(expected.unwrap().take(0) =~= Seq::empty());}
            episode::empty_after::<T>(preceding);
            if let Some(ref receipt)=cause {receipts.tracked_insert((-1int,false),receipt.duplicate());}
            function.shape();
            assert((Report {steps,failure:None,receipts:Tracked(receipts),histories:Tracked(histories)}).witnessed()) by {reveal(Report::witnessed);reveal(histories_recorded);};
            assert((Report {steps,failure:None,receipts:Tracked(receipts),histories:Tracked(histories)}).ordered()) by {reveal(Report::ordered);};
        }
        while pc.is_some()
            invariant mixed.is_some()==old(mixed).is_some(),mixed.is_some()==mixed_expected.is_some(),
                mixed.is_some() ==> mode.is_none() && typed.is_none() && expected.is_none() && old(mixed)->Some_0.wf() && mixed->Some_0.wf()
                    && mixed->Some_0.trace(&old(mixed)->Some_0,steps@) && mixed->Some_0.shape(&old(mixed)->Some_0)
                    && mixed->Some_0.supports(values,ports@,function.code(),mixed_expected.unwrap())
                    && protected_mixed::plan(function.code(),mixed_expected.unwrap())
                    && protected::execution(old(mixed)->Some_0.scalar->Some_0.states(),old(mixed)->Some_0.scalar->Some_0.routes(),protected_mixed::scalars(mixed_expected.unwrap()))
                    && steps.len()<=mixed_expected.unwrap().len() && protected_mixed::same(steps@,mixed_expected.unwrap().take(steps.len() as int))
                    && pc==next(function.code().len(),mixed_expected.unwrap().take(steps.len() as int))
                    && steps.len()<=function.code().len() && (pc.is_some() ==> steps.len()<=pc.unwrap())
                    && mixed->Some_0.payload->Some_0.budget((function.code().len()-steps.len()) as nat),
                typed.is_some()==old(typed).is_some(),
                typed.is_some() ==> mode.is_none() && old(typed)->Some_0.wf() && typed->Some_0.wf() && typed->Some_0.shape(&old(typed)->Some_0)
                    && typed->Some_0.supports(values,ports@) && old(typed)->Some_0.supports(values,ports@) && protected_typed::typed_only(function.code())
                    && steps.len()<=function.code().len() && (pc.is_some() ==> steps.len()<=pc.unwrap())
                    && typed->Some_0.budget((function.code().len()-steps.len()) as nat)
                    && protected_typed::addressed(old(typed)->Some_0.targets(),old(typed)->Some_0.routes(),steps@)
                    && protected_typed::execution(old(typed)->Some_0.states(),old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),steps@)
                    && typed->Some_0.states()==protected_typed::after(old(typed)->Some_0.states(),old(typed)->Some_0.routes(),steps@)
                    && typed->Some_0.revisions()==protected_typed::clocks(old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),steps@),
                expected.is_some() ==> mode.is_some() && protected::plan(function.code(),expected.unwrap())
                && protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap())
                && steps.len()<=expected.unwrap().len() && protected::same(steps@,expected.unwrap().take(steps.len() as int))
                && pc==next(function.code().len(),expected.unwrap().take(steps.len() as int))
                && mode->Some_0.states()==protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap().take(steps.len() as int)),
                mode.is_some()==old(mode).is_some(),
                mode.is_some() ==> old(mode)->Some_0.wf() && mode->Some_0.wf() && mode->Some_0.shape(&old(mode)->Some_0)
                    && mode->Some_0.supports(values,ports@) && protected::kernel_only(function.code())
                    && protected::addressed(old(mode)->Some_0.targets(),old(mode)->Some_0.routes(),steps@)
                    && protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),steps@)
                    && mode->Some_0.states()==protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),steps@),
                self.wf(),self.work_state().accepts(),self.cleanup_state().acquisition_open(id),self.execution_journal()==initial.execution_journal(),self.status_links()==initial.status_links(),self.capture()==initial.capture(),self.work_state()==initial.work_state(),self.value_state()==Some(values),self.phase_spec()==initial.phase_spec(),
                self.cleanup_state().frame(&initial.cleanup_state(),id),
                self.cleanup_state().queues().dom()==initial.cleanup_state().queues().dom(),self.cleanup_state().domain_ids()==initial.cleanup_state().domain_ids(),
                self.cleanup_state().queues()[id].issued()==initial.cleanup_state().queues()[id].issued(),
                self.cleanup_state().queues()[id].protocol().selected()==initial.cleanup_state().queues()[id].protocol().selected(),
                initial==*old(self),initial.value_state()==Some(values),initial.cleanup_state().live(id),offset==initial.cleanup_state().queues()[id].slots().len(),
                function.valid(),ports.len()==function.code().len(),
                forall|i:int|0<=i<ports.len() ==> (#[trigger] ports@[i]).key==function.code()[i].key && access::declared(values,ports@[i]),
                prefix(function.code(),ports@,steps@,values),pc==next(function.code().len(),steps@),pc.is_some() ==> pc.unwrap()<function.code().len(),
                episode::same_cause((Report {steps,failure:None,receipts:Tracked(receipts),histories:Tracked(histories)}).predecessor(),preceding),
                episode::writes_after(steps@,preceding),preceding==cause,
                self.cleanup_state().link()==initial.cleanup_state().link(),self.cleanup_state().queues()[id].link()==initial.cleanup_state().queues()[id].link(),
                forall|i:int|0<=i<steps.len() ==> (#[trigger] steps@[i]).inserted_into(initial.cleanup_state().queues()[id].link()),
                forall|i:int|0<=i<steps.len() ==> (#[trigger] steps@[i]).registered(initial.cleanup_state().link(),id),
                retained(steps@,*self,id,offset),(Report {steps,failure:None,receipts:Tracked(receipts),histories:Tracked(histories)}).witnessed(),(Report {steps,failure:None,receipts:Tracked(receipts),histories:Tracked(histories)}).ordered(),
                self.cleanup_state().queues()[id].slots().take(offset as int)==initial.cleanup_state().queues()[id].slots(),
                self.cleanup_state().queues()[id].protocol().waiting()==initial.cleanup_state().queues()[id].protocol().waiting()+tokens(steps@),
            decreases if pc.is_some() {function.code.len()-pc.unwrap()} else {0},
        {
            let at=pc.unwrap();let ghost prior=*self;let ghost earlier=steps@;let ghost typed_before=*typed;let ghost mixed_before=*mixed;
            proof {if mixed.is_some() {
                mixed->Some_0.ready(&old(mixed)->Some_0,function.code(),ports@,values,steps@,mixed_expected.unwrap(),at,(function.code().len()-steps.len()) as nat);
            }}
            proof {if typed.is_some() {
                typed->Some_0.supports_at(values,ports@,at);old(typed)->Some_0.supports_at(values,ports@,at);
                protected_typed::typed_at(function.code(),at);
                typed->Some_0.call_facts(at);old(typed)->Some_0.call_facts(at);
                let index=typed->Some_0.routes()[at as int] as int;
                typed->Some_0.budget_at((function.code().len()-steps.len()) as nat,index);
            }}
            proof {if mode.is_some() {mode->Some_0.call_facts(at);old(mode)->Some_0.call_facts(at);}}
            proof {if expected.is_some() {
                let source=expected.unwrap();protected::plan_position(function.code(),source,steps.len() as int);
                protected::input_at(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),source,steps.len() as int);
                let s=source[steps.len() as int];assert(s.pc==at);protected::plan_step(function.code(),source,steps.len() as int);
                assert(replay::transport::step(function.code(),s));
                assert(function.code()[at as int].effect is Kernel);
                assert(super::effect::operation(function.code()[at as int].effect.scalar_code().unwrap())(mode->Some_0.states()[mode->Some_0.index(at) as int]).is_some());
            }}
            proof {(Report {steps,failure:None,receipts:Tracked(receipts),histories:Tracked(histories)}).witnesses_valid();}
            let outcome=match mixed {
                Some(context)=>context.execute(self,id,at,ports[at],&function.code[at],Tracked(&receipts)),
                None=>self.execute_call(id,at,ports[at],&function.code[at],Tracked(&receipts),mode,typed),
            };
            let step=match outcome {
                Ok(step)=>step,
                Err(failure)=>{
                    let report=failed_report::<E,T,M>(steps,Tracked(receipts),Tracked(histories),failure,Ghost(function.code()),Ghost(ports@),Ghost(values));
                    proof {report.establish_after(preceding);}
                    return Ok(report);
                },
            };
            proof {
                assert(function.code()[at as int].valid(at as int,function.code().len()));
                assert(step.next.is_some() ==> at<step.next.unwrap()<function.code().len()) by {reveal(Step::corresponds);}
                assert forall|i:int|0<=i<earlier.len() implies (#[trigger] earlier[i]).in_slot(self.cleanup_state().queues()[id].slots()[offset+i]) by {
                    assert(self.cleanup_state().queues()[id].slots().take(step.token() as int)[offset+i]==prior.cleanup_state().queues()[id].slots()[offset+i]);
                }
            }
            proof {
                if preceding.is_some() && step.write().journal()==preceding.unwrap().journal() {assert(receipts[(-1int,false)].same(&preceding.unwrap()));}
                episode::append_after(steps@,step,preceding);
            }
            proof {if mixed.is_some() {
                step.interpretation(function.code()[at as int],ports@[at as int],values);
                mixed->Some_0.supports_frame(&mixed_before->Some_0,values,ports@,function.code(),mixed_expected.unwrap());
                if step.result is Payload {assert(step.result->Payload_0.inverse().wf()) by {reveal(Step::corresponds);}}
                mixed->Some_0.record(&mixed_before->Some_0,&old(mixed)->Some_0,steps@,step,(function.code().len()-steps.len()) as nat);
                protected_mixed::same_append(function.code(),steps@,mixed_expected.unwrap(),step);
            }}
            proof {if typed.is_some() {
                typed->Some_0.supports_frame(&typed_before->Some_0,values,ports@);
                protected_typed::append(old(typed)->Some_0.states(),old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),steps@,step);
                protected_typed::address_append(old(typed)->Some_0.targets(),old(typed)->Some_0.routes(),steps@,step);
                assert(step.result->Payload_0.inverse().wf()) by {reveal(Step::corresponds);}
                typed->Some_0.consumed(&typed_before->Some_0,(function.code().len()-steps.len()) as nat,typed_before->Some_0.routes()[at as int] as int,step);
            }}
            proof {if mode.is_some() {protected::append(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),steps@,step);}}
            proof {if expected.is_some() {
                let source=expected.unwrap();protected::plan_position(function.code(),source,steps.len() as int);protected::plan_step(function.code(),source,steps.len() as int);let s=source[steps.len() as int];
                step.interpretation(function.code()[at as int],ports@[at as int],values);
                assert(replay::transport::step(function.code(),step));
                assert(step.pc==s.pc && step.before()==s.before());
                replay::transport::paired(function.code(),s,step);
                assert(step.after()==s.after());
                protected::take_append(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),source,steps.len() as int);
                assert forall|j:int|0<=j<steps.len()+1 implies {
                    let a=#[trigger] steps@.push(step)[j];let b=source.take(steps.len() as int+1)[j];
                    &&& a.pc==b.pc && a.before()==b.before() && a.after()==b.after() && a.outcome()==b.outcome() && a.next==b.next
                } by {}
                assert(protected::same(steps@.push(step),source.take(steps.len() as int+1)));
                assert(next(function.code().len(),source.take(steps.len() as int+1))==step.next);
            }}
            pc=step.next;append_step::<E,T,M>(&mut steps,Tracked(&mut receipts),Tracked(&mut histories),step,Ghost(function.code()),Ghost(ports@),Ghost(values));
            proof {
                assert(tokens(steps@) =~= tokens(earlier).push(step.token()));
                assert(self.cleanup_state().queues()[id].slots().take(offset as int) =~= initial.cleanup_state().queues()[id].slots());
            }
        }
        proof {if mixed.is_some() {
            protected_mixed::plan_at(function.code(),mixed_expected.unwrap(),steps.len() as int);
            assert(mixed_expected.unwrap().take(steps.len() as int) =~= mixed_expected.unwrap());
        }}
        proof {if expected.is_some() {
            protected::plan_position(function.code(),expected.unwrap(),steps.len() as int);
            assert(expected.unwrap().take(steps.len() as int) =~= expected.unwrap());
        }}
        let report=Report {steps,failure:None,receipts:Tracked(receipts),histories:Tracked(histories)};
        proof {report.establish_recovery(function.code(),ports@,values);report.establish_after(preceding);}
        Ok(report)
    }
}
}

pub mod semantics;

pub mod root;

pub mod trace;

pub mod recovery;

pub mod episode;

pub mod cleanup_path;

pub mod interleaving;

pub mod replay;

pub(crate) mod protected;

pub(crate) mod protected_typed;

pub(crate) mod protected_mixed;
