//! Finite bodies over multiple declared services. Every instruction resolves
//! its real Begin-bound slot at execution, retains the selected allocation and
//! registers its inverse before moving to the computed continuation. Other
//! writers and replacements may interleave between these actual object steps.
use super::access::{self, Write};
#[cfg(verus_keep_ghost)]
use super::joint;
use super::program::Instruction;
use super::slot::ServiceSlot;
#[cfg(verus_keep_ghost)]
use super::{Outcome, ValueState};
use crate::execution::Execution;
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
use crate::lifecycle_state::services::NativeEpisode;
use crate::Port;
#[cfg(verus_keep_ghost)]
use crate::{dependent_grammar as d, fresh_grammar as f, guarded_components as c};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Call {pub port:Port,pub instruction:Instruction}
pub struct Program {code:Vec<Call>}
impl Program {
    pub closed spec fn code(&self)->Seq<Call> {self.code@}
    pub closed spec fn valid(&self)->bool {forall|i:int| 0<=i<self.code().len() ==> #[trigger] self.code()[i].instruction.valid(i,self.code().len())}
    pub open spec fn accesses(&self)->Set<Port> {self.code().map(|_:int,c:Call|c.port).to_set()}
    pub open spec fn declared<T,M>(&self,episode:NativeEpisode<ServiceSlot<T,M>>)->bool {
        forall|i:int| 0<=i<self.code().len() ==> access::declared(episode,#[trigger] self.code()[i].port)
    }
    pub fn new(code:Vec<Call>)->(out:Result<Self,Vec<Call>>)
        ensures out.is_ok()==(forall|i:int| 0<=i<code.len() ==> #[trigger] code@[i].instruction.valid(i,code.len() as nat)),
            out.is_ok() ==> out->Ok_0.valid() && out->Ok_0.code()==code@,
            out.is_err() ==> out->Err_0==code,
    {
        let mut i=0;
        while i<code.len()
            invariant i<=code.len(),forall|j:int| 0<=j<i ==> #[trigger] code@[j].instruction.valid(j,code.len() as nat),
            decreases code.len()-i,
        {if !code[i].instruction.check(i,code.len()) {return Err(code);}i+=1;}
        Ok(Self {code})
    }
    /// Export the finite control-flow shape without exposing the stored vector.
    pub proof fn shape(&self)
        requires self.valid(),
        ensures forall|i:int| 0<=i<self.code().len() ==> #[trigger] self.code()[i].instruction.valid(i,self.code().len()),
    {}
    fn missing<T,M>(&self,episode:&NativeEpisode<ServiceSlot<T,M>>)->(out:Option<usize>)
        ensures out.is_none()==self.declared(*episode),
            out.is_some() ==> out.unwrap()<self.code().len() && !access::declared(*episode,self.code()[out.unwrap() as int].port),
    {
        let mut i=0;
        while i<self.code.len()
            invariant i<=self.code.len(),forall|j:int| 0<=j<i ==> access::declared(*episode,#[trigger] self.code()[j].port),
            decreases self.code.len()-i,
        {if !episode.declares_service(self.code[i].port) {return Some(i);}i+=1;}
        None
    }
    /// Full carrier membership of this stored body, including both branches
    /// and failure domains. Lifting aliasing service observations is separate.
    pub proof fn component(&self,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,pc:usize)
        requires self.valid(),forall|i:int| 0<=i<self.code().len() ==> keys.contains(#[trigger] self.code()[i].port),
        ensures c::component(super::library(),programs(self.code()),actor,keys,provisions,pc),
    {
        super::primitive_theory();self.member(actor,keys,provisions,pc);
        c::member_is_component(|_:Port,a:ValueState,b:ValueState|a==b,super::library(),programs(self.code()),actor,keys,provisions,pc);
    }
    proof fn member(&self,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,pc:usize)
        requires self.valid(),forall|i:int| 0<=i<self.code().len() ==> keys.contains(#[trigger] self.code()[i].port),
        ensures f::member(super::library(),programs(self.code()),actor,keys,provisions,pc),
        decreases if pc<self.code().len() {self.code().len()-pc} else {0},
    {
        let ps=programs(self.code());
        if pc<self.code().len() {
            let instruction=self.code()[pc as int].instruction;
            assert(instruction.valid(pc as int,self.code().len()));
            if instruction.branch.matched.is_some() {self.member(actor,keys,provisions,instruction.branch.matched.unwrap());}
            if instruction.branch.unmatched.is_some() {self.member(actor,keys,provisions,instruction.branch.unmatched.unwrap());}
            assert forall|out:Outcome| instruction.branch.selected(out).is_some() implies
                f::members(super::library(),ps).contains((actor,keys,provisions,instruction.branch.selected(out).unwrap())) by { }
        }
        f::constructor_member(super::library(),ps,actor,keys,provisions,pc);
    }
}
pub open spec fn node(code:Seq<Call>,pc:usize)->d::Node<Port,(Port,super::Operation),(),ValueState,Outcome,usize> {
    if pc<code.len() {d::Node::Operation {operation:(code[pc as int].port,code[pc as int].instruction.operation),argument:(),
        select:|out:Outcome|code[pc as int].instruction.branch.selected(out)}} else {d::Node::Unit}
}
pub open spec fn programs(code:Seq<Call>)->f::Programs<(Port,super::Operation),(),ValueState,Outcome,usize> {
    |_:usize| |pc:usize| f::Node::Dependent {node:node(code,pc)}
}
#[derive(Debug)]
pub enum AdmissionError {NoNativeOwner,Closed,Undeclared {pc:usize,port:Port}}
pub struct Step {pub pc:usize,pub write:Write}
pub struct Failure {pub pc:usize,pub error:access::Error,#[allow(dead_code)] rejection:Ghost<Option<access::Rejection>>}
impl Failure {
    pub closed spec fn position(&self)->usize {self.pc}
    pub closed spec fn error_spec(&self)->access::Error {self.error}
    pub closed spec fn rejection(&self)->Option<access::Rejection> {self.rejection@}
    pub open spec fn certified<T,M>(&self,code:Seq<Call>,episode:NativeEpisode<ServiceSlot<T,M>>)->bool {
        self.position()<code.len() && match self.error_spec() {
            access::Error::Value(error) if error!=super::ValueError::Closed=>self.rejection().is_some()
                && self.rejection().unwrap().certified(episode,code[self.position() as int].port,code[self.position() as int].instruction.operation,error),
            _=>self.rejection().is_none(),
        }
    }
}
pub struct Report {pub steps:Vec<Step>,pub failure:Option<Failure>,pub receipts:Tracked<super::registration::ReceiptMap>}
pub open spec fn tokens(steps:Seq<Step>)->Seq<usize> {steps.map(|_:int,step:Step|step.write.admission.token)}
proof fn append_tokens(steps:Seq<Step>,step:Step)
    ensures tokens(steps.push(step))==tokens(steps).push(step.write.admission.token),
{assert(tokens(steps.push(step)) =~= tokens(steps).push(step.write.admission.token));}

pub open spec fn next(code:Seq<Call>,steps:Seq<Step>)->Option<usize> {
    if steps.len()==0 {if code.len()==0 {None} else {Some(0)}} else {steps.last().write.admission.next}
}
#[verifier::opaque]
pub open spec fn prefix<T,M>(code:Seq<Call>,steps:Seq<Step>,episode:NativeEpisode<ServiceSlot<T,M>>)->bool {
    forall|i:int| 0<=i<steps.len() ==> {
        let step=#[trigger] steps[i];
        &&& step.pc<code.len() && Some(step.pc)==next(code,steps.take(i))
        &&& access::selected(episode,step.write.binding) && step.write.binding.port_spec()==code[step.pc as int].port
        &&& step.write.corresponds(code[step.pc as int].instruction.operation,code[step.pc as int].instruction.branch)
    }
}
pub open spec fn retained<T,M,C,G,Cb,X>(steps:Seq<Step>,execution:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize,offset:nat)->bool {
    execution.cleanup_state().live(id) && execution.cleanup_state().queues()[id].slots().len()==offset+steps.len()
        && forall|i:int| 0<=i<steps.len() ==> (#[trigger] steps[i]).write.recorded(execution,id)
            && steps[i].write.admission.token==offset+i
}
proof fn empty_prefix<T,M>(code:Seq<Call>,episode:NativeEpisode<ServiceSlot<T,M>>)
    ensures prefix(code,Seq::empty(),episode),
{reveal(prefix);}
proof fn append_prefix<T,M>(code:Seq<Call>,steps:Seq<Step>,episode:NativeEpisode<ServiceSlot<T,M>>,step:Step)
    requires prefix(code,steps,episode),step.pc<code.len(),Some(step.pc)==next(code,steps),
        access::selected(episode,step.write.binding),step.write.binding.port_spec()==code[step.pc as int].port,
        step.write.corresponds(code[step.pc as int].instruction.operation,code[step.pc as int].instruction.branch),
    ensures prefix(code,steps.push(step),episode),
{
    reveal(prefix);
    let extended=steps.push(step);
    assert forall|i:int| 0<=i<extended.len() implies {
        let current=#[trigger] extended[i];
        &&& current.pc<code.len() && Some(current.pc)==next(code,extended.take(i))
        &&& access::selected(episode,current.write.binding) && current.write.binding.port_spec()==code[current.pc as int].port
        &&& current.write.corresponds(code[current.pc as int].instruction.operation,code[current.pc as int].instruction.branch)
    } by {if i<steps.len() {assert(extended.take(i)==steps.take(i));} else {assert(extended.take(i)==steps);}}
}
proof fn append_retained<T,M,C,G,Cb,X>(steps:Seq<Step>,before:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,after:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize,offset:nat,step:Step)
    requires retained(steps,before,id,offset),step.write.recorded(after,id),step.write.admission.token==offset+steps.len(),
        after.cleanup_state().domain_ids()==before.cleanup_state().domain_ids(),after.cleanup_state().queues()[id].link()==before.cleanup_state().queues()[id].link(),
        after.cleanup_state().queues()[id].slots().len()==before.cleanup_state().queues()[id].slots().len()+1,
        after.cleanup_state().queues()[id].slots().take(before.cleanup_state().queues()[id].slots().len() as int)==before.cleanup_state().queues()[id].slots(),
        before.cleanup_state().wf(),after.cleanup_state().wf(),
    ensures retained(steps.push(step),after,id,offset),
{
    assert forall|i:int| 0<=i<steps.push(step).len() implies (#[trigger] steps.push(step)[i]).write.recorded(after,id)
        && steps.push(step)[i].write.admission.token==offset+i by {
        if i<steps.len() {
            assert(steps[i].write.recorded(before,id));
            assert(after.cleanup_state().queues()[id].slots()[steps[i].write.admission.token as int]==before.cleanup_state().queues()[id].slots()[steps[i].write.admission.token as int]);
        }
    }
}
/// Recorded calls occupy authentic prefixes of this actual source history.
#[verifier::opaque]
pub open spec fn recorded(steps:Seq<Step>,frames:Seq<joint::Frame>)->bool {
    forall|i:int| 0<=i<steps.len() ==> {
        let receipt=(#[trigger] steps[i]).write.admission.registration().write();
        &&& receipt.at()<frames.len() && frames[receipt.at() as int].event==receipt.event()
        &&& frames.take(receipt.events().len() as int)==receipt.events()
    }
}
proof fn extend_recorded(steps:Seq<Step>,before:Seq<joint::Frame>,after:Seq<joint::Frame>)
    requires recorded(steps,before),before.len()<=after.len(),after.take(before.len() as int)==before,
    ensures recorded(steps,after),
{
    reveal(recorded);
    assert forall|i:int| 0<=i<steps.len() implies {
        let receipt=(#[trigger] steps[i]).write.admission.registration().write();
        &&& receipt.at()<after.len() && after[receipt.at() as int].event==receipt.event()
        &&& after.take(receipt.events().len() as int)==receipt.events()
    } by {
        let receipt=steps[i].write.admission.registration().write();
        assert(after[receipt.at() as int]==before[receipt.at() as int]);
        assert(after.take(receipt.events().len() as int) =~= before.take(receipt.events().len() as int));
    }
}
/// Interpretation of one recorded call on the actual allocation carrier.
#[verifier::opaque]
pub open spec fn interpreted(step:Step,call:Call)->bool {
    let receipt=step.write.admission.registration().write();
    let result=d::run(access::library(),d::Node::Operation {operation:(receipt.event().key,call.instruction.operation),argument:(),
        select:|out:Outcome|call.instruction.branch.selected(out)},access::objects(joint::state_at(receipt.events(),receipt.at())));
    result.is_some() && result.unwrap().state==access::objects(receipt.events().last().state) && result.unwrap().next==step.write.admission.next
}
impl Step {
    proof fn production(&self,call:Call)
        requires self.write.corresponds(call.instruction.operation,call.instruction.branch),
        ensures interpreted(*self,call),
    {reveal(interpreted);self.write.semantics();}
}

impl Report {
    /// Preserve the actual rejected instruction when returning its successful
    /// prefix. Keep this result-transfer contract independent of trace unfolding.
    fn failed(steps:Vec<Step>,failure:Failure,receipts:Tracked<super::registration::ReceiptMap>)->(out:Self)
        ensures out.steps==steps,out.failure==Some(failure),out.receipts()==receipts@,
    {Self {steps,failure:Some(failure),receipts}}
    pub closed spec fn receipts(&self)->super::registration::ReceiptMap {self.receipts@}
    pub(crate) fn receipt_witnesses(&self)->(out:Tracked<&super::registration::ReceiptMap>)
        ensures *out@==self.receipts(),
    {Tracked(self.receipts.borrow())}
    pub open spec fn witnessed(&self)->bool {
        super::registration::witnesses(self.receipts())
            && (forall|i:int| 0<=i<self.steps.len() ==>
                super::registration::recorded_in(self.receipts(),i,(#[trigger] self.steps@[i]).write.admission.registration())
                    && self.steps@[i].write.admission.registration().certified())
            && (self.failure.is_some() && self.failure.unwrap().rejection().is_some() ==>
                self.receipts().contains_key((self.steps.len() as int,false))
                    && self.receipts()[(self.steps.len() as int,false)].same(&self.failure.unwrap().rejection().unwrap().receipt))
    }
    pub open spec fn certified<T,M>(&self,code:Seq<Call>,episode:NativeEpisode<ServiceSlot<T,M>>)->bool {
        self.witnessed() && prefix(code,self.steps@,episode) && match self.failure {
            None=>next(code,self.steps@).is_none(),
            Some(failure)=>next(code,self.steps@)==Some(failure.position()) && failure.certified(code,episode),
        }
    }
    pub open spec fn failure_ordered(&self)->bool {
        self.failure.is_some() && self.failure.unwrap().rejection().is_some() && self.steps.len()>0 ==> {
            let receipt=self.failure.unwrap().rejection().unwrap().receipt;let prior=self.steps@.last().write.admission.registration().completion();
            receipt.journal()==prior.journal() ==> receipt.follows(&prior)
        }
    }
    pub fn succeeded(&self)->(out:bool) ensures out==self.failure.is_none(), {self.failure.is_none()}
    pub proof fn production<T,M>(&self,code:Seq<Call>,episode:NativeEpisode<ServiceSlot<T,M>>)
        requires self.certified(code,episode),
        ensures forall|i:int| 0<=i<self.steps.len() ==> interpreted(#[trigger] self.steps@[i],code[self.steps@[i].pc as int]),
    {
        reveal(prefix);
        assert forall|i:int| 0<=i<self.steps.len() implies interpreted(#[trigger] self.steps@[i],code[self.steps@[i].pc as int]) by {
            self.steps@[i].production(code[self.steps@[i].pc as int]);
        }
    }
    /// A body whose successful calls use one Journal has one ordered history.
    /// Foreign-Journal calls have separate traces, not a synthetic total order.
    pub open spec fn ordered(&self)->bool {
        forall|i:int| 0<i<self.steps.len() && self.steps@[i].write.admission.registration().write().journal()==self.steps@[i-1].write.admission.registration().write().journal()
            ==> (#[trigger] self.steps@[i]).write.admission.registration().write().follows(&self.steps@[i-1].write.admission.registration().write())
    }
    proof fn order_at(&self,i:int,j:int)
        requires self.ordered(),0<=i<j<self.steps.len(),
            forall|k:int| i<=k<=j ==> (#[trigger] self.steps@[k]).write.admission.registration().write().journal()==self.steps@[i].write.admission.registration().write().journal(),
        ensures self.steps@[j].write.admission.registration().write().follows(&self.steps@[i].write.admission.registration().write()),
        decreases j-i,
    {
        if j>i+1 {
            self.order_at(i,j-1);
            let middle=self.steps@[j-1].write.admission.registration().write();let first=self.steps@[i].write.admission.registration().write();
            assert(middle.covers(&first));self.steps@[j].write.admission.registration().write().after_cover(&middle,&first);
        }
    }
    /// Every successful local step occurs in the last actual write's history.
    /// Allocation, slot replacement, lifecycle and other writers remain in it.
    #[verifier::rlimit(20)]
    pub proof fn source_trace<T,M>(&self,code:Seq<Call>,episode:NativeEpisode<ServiceSlot<T,M>>)->(frames:Seq<joint::Frame>)
        requires self.certified(code,episode),self.ordered(),self.steps.len()>0,
            forall|i:int| 0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).write.admission.registration().write().journal()==self.steps@.last().write.admission.registration().write().journal(),
        ensures joint::valid(frames),frames==self.steps@.last().write.admission.registration().completion().events(),
            self.steps@.last().write.admission.registration().completion().covers(&self.steps@.last().write.admission.registration().write()),
            recorded(self.steps@,frames),
            forall|i:int,j:int| #![trigger self.steps@[i],self.steps@[j]] 0<=i<j<self.steps.len()
                ==> self.steps@[i].write.admission.registration().write().at()<self.steps@[j].write.admission.registration().write().at(),
    {reveal(prefix);self.ordered_trace()}
    /// Keep the sequence-prefix calculation separate from validity of the
    /// complete joint history; expanding both together makes solver work grow
    /// with unrelated variants of the common state.
    proof fn trace_at(&self,i:int,end:joint::Receipt)
        requires self.ordered(),0<=i<self.steps.len(),end.covers(&self.steps@.last().write.admission.registration().write()),
            self.steps@[i].write.admission.registration().write().events().len()>0,
            forall|j:int| 0<=j<self.steps.len() ==> (#[trigger] self.steps@[j]).write.admission.registration().write().journal()==self.steps@.last().write.admission.registration().write().journal(),
        ensures {
            let receipt=self.steps@[i].write.admission.registration().write();let frames=end.events();
            &&& receipt.at()<frames.len() && frames[receipt.at() as int].event==receipt.event()
            &&& receipt.events()==frames.take(receipt.events().len() as int)
        },
    {
        let last=self.steps@.last().write.admission.registration().write();
        let receipt=self.steps@[i].write.admission.registration().write();
        if i<self.steps.len()-1 {self.order_at(i,self.steps.len() as int-1);}
        else {assert(last.events().take(last.events().len() as int) =~= last.events());}
        end.cover_through(&last,&receipt);end.included(&receipt);
    }
    #[verifier::rlimit(20)]
    proof fn ordered_trace(&self)->(frames:Seq<joint::Frame>)
        requires self.ordered(),self.steps.len()>0,
            self.steps@.last().write.admission.registration().certified(),
            forall|i:int| 0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).write.admission.registration().write().events().len()>0,
            forall|i:int| 0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).write.admission.registration().write().journal()==self.steps@.last().write.admission.registration().write().journal(),
        ensures joint::valid(frames),frames==self.steps@.last().write.admission.registration().completion().events(),
            self.steps@.last().write.admission.registration().completion().covers(&self.steps@.last().write.admission.registration().write()),
            recorded(self.steps@,frames),
            forall|i:int,j:int| #![trigger self.steps@[i],self.steps@[j]] 0<=i<j<self.steps.len()
                ==> self.steps@[i].write.admission.registration().write().at()<self.steps@[j].write.admission.registration().write().at(),
    {
        reveal(recorded);
        let last=self.steps@.last().write.admission.registration().write();
        let evidence=self.steps@.last().write.admission.registration();evidence.completion_valid();
        let frames=evidence.completion().events();
        assert forall|i:int| 0<=i<self.steps.len() implies {
            let receipt=(#[trigger] self.steps@[i]).write.admission.registration().write();
            &&& receipt.at()<frames.len() && frames[receipt.at() as int].event==receipt.event()
            &&& receipt.events()==frames.take(receipt.events().len() as int)
        } by {
            self.trace_at(i,evidence.completion());
        }
        assert forall|i:int,j:int| #![trigger self.steps@[i],self.steps@[j]] 0<=i<j<self.steps.len()
            implies self.steps@[i].write.admission.registration().write().at()<self.steps@[j].write.admission.registration().write().at() by {self.order_at(i,j);}
        frames
    }
    /// Include a real rejected final operation and all successful inverses in
    /// the same source trace. Rejection preserves the whole recorded state.
    #[verifier::rlimit(20)]
    pub proof fn failed_trace<T,M>(&self,code:Seq<Call>,episode:NativeEpisode<ServiceSlot<T,M>>)->(frames:Seq<joint::Frame>)
        requires self.certified(code,episode),self.ordered(),self.failure_ordered(),
            self.failure.is_some(),self.failure.unwrap().rejection().is_some(),
            forall|i:int| 0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).write.admission.registration().write().journal()==self.failure.unwrap().rejection().unwrap().receipt.journal(),
        ensures joint::valid(frames),frames==self.failure.unwrap().rejection().unwrap().receipt.events(),
            joint::state_at(frames,(frames.len()-1) as nat)==frames.last().state,
            joint::pending_at(frames,(frames.len()-1) as nat)==frames.last().pending,
            recorded(self.steps@,frames.take(frames.len() as int-1)),
    {
        let failure=self.failure.unwrap();let rejected=failure.rejection().unwrap().receipt;let frames=rejected.events();
        if self.steps.len()>0 {
            let earlier=self.source_trace(code,episode);
            let completion=self.steps@.last().write.admission.registration().completion();
            assert(rejected.follows(&completion));
            let before=frames.take(frames.len() as int-1);
            assert(before.take(earlier.len() as int) =~= earlier);
            extend_recorded(self.steps@,earlier,before);
        } else {reveal(recorded);}
        failure.rejection().unwrap().stutters();
        frames
    }
    /// The actual allocation footprint accumulates captures, not assumptions
    /// that service names denote disjoint mutable state.
    pub open spec fn successful_footprint(&self)->access::Footprint {
        access::Footprint {
            read_slots:self.steps@.map(|_:int,s:Step|joint::Object {domain:s.write.binding.capture_spec().slot().journal_spec().source(),key:s.write.binding.capture_spec().slot().key()}).to_set(),
            read_values:self.steps@.map(|_:int,s:Step|s.write.binding.capture_spec().value_spec().object()).to_set(),
            write_values:self.steps@.map(|_:int,s:Step|s.write.binding.capture_spec().value_spec().object()).to_set(),
        }
    }
    /// Compute effective service writes from real bindings at each write
    /// position. This includes every alias, including aliases outside the
    /// body's declared names and captured objects no longer selected by a slot.
    pub open spec fn affected<K,T,M>(&self,values:Map<K,std::sync::Arc<ServiceSlot<T,M>>>,journal:joint::Journal)->Set<K> {
        values.dom().filter(|key:K|exists|i:int|0<=i<self.steps.len() && {
            let receipt=(#[trigger] self.steps@[i]).write.admission.registration().write();
            receipt.journal()==journal && crate::lifecycle_state::services::slots::affected(values,journal,
                joint::state_at(receipt.events(),receipt.at()),receipt.event().key).contains(key)
        })
    }
    /// Every observed write contributes its aliases to the cumulative range.
    proof fn includes_affected<K,T,M>(&self,values:Map<K,std::sync::Arc<ServiceSlot<T,M>>>,journal:joint::Journal,i:int,key:K)
        requires 0<=i<self.steps.len(),self.steps@[i].write.admission.registration().write().journal()==journal,
            crate::lifecycle_state::services::slots::affected(values,journal,
                joint::state_at(self.steps@[i].write.admission.registration().write().events(),self.steps@[i].write.admission.registration().write().at()),
                self.steps@[i].write.admission.registration().write().event().key).contains(key),
        ensures self.affected(values,journal).contains(key),
    {}
    pub proof fn frame<K,T,M,T2,M2>(&self,code:Seq<Call>,episode:NativeEpisode<ServiceSlot<T,M>>,values:Map<K,std::sync::Arc<ServiceSlot<T2,M2>>>,journal:joint::Journal)
        requires self.certified(code,episode),
        ensures forall|i:int,key:K| #![trigger self.steps@[i], values[key]] 0<=i<self.steps.len() && values.contains_key(key) && !self.affected(values,journal).contains(key)
            && self.steps@[i].write.admission.registration().write().journal()==journal ==> {
                let receipt=self.steps@[i].write.admission.registration().write();
                crate::lifecycle_state::services::slots::projection(values,journal,receipt.events().last().state)[key]
                    ==crate::lifecycle_state::services::slots::projection(values,journal,joint::state_at(receipt.events(),receipt.at()))[key]
            },
    {reveal(prefix);self.frame_recorded(values,journal)}
    proof fn frame_recorded<K,T2,M2>(&self,values:Map<K,std::sync::Arc<ServiceSlot<T2,M2>>>,journal:joint::Journal)
        requires forall|i:int| 0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).write.admission.registration().certified(),
        ensures forall|i:int,key:K| #![trigger self.steps@[i], values[key]] 0<=i<self.steps.len() && values.contains_key(key) && !self.affected(values,journal).contains(key)
            && self.steps@[i].write.admission.registration().write().journal()==journal ==> {
                let receipt=self.steps@[i].write.admission.registration().write();
                crate::lifecycle_state::services::slots::projection(values,journal,receipt.events().last().state)[key]
                    ==crate::lifecycle_state::services::slots::projection(values,journal,joint::state_at(receipt.events(),receipt.at()))[key]
            },
    {
        assert forall|i:int,key:K| #![trigger self.steps@[i], values[key]] 0<=i<self.steps.len() && values.contains_key(key) && !self.affected(values,journal).contains(key)
            && self.steps@[i].write.admission.registration().write().journal()==journal implies {
                let receipt=self.steps@[i].write.admission.registration().write();
                crate::lifecycle_state::services::slots::projection(values,journal,receipt.events().last().state)[key]
                    ==crate::lifecycle_state::services::slots::projection(values,journal,joint::state_at(receipt.events(),receipt.at()))[key]
            } by {
            let receipt=self.steps@[i].write.admission.registration().write();
            if crate::lifecycle_state::services::slots::affected(values,journal,joint::state_at(receipt.events(),receipt.at()),receipt.event().key).contains(key) {
                self.includes_affected(values,journal,i,key);assert(false);
            }
            assert(!crate::lifecycle_state::services::slots::affected(values,journal,joint::state_at(receipt.events(),receipt.at()),receipt.event().key).contains(key));
            crate::lifecycle_state::services::slots::project_value_step(values,journal,joint::state_at(receipt.events(),receipt.at()),receipt.events().last().state,receipt.event());
        }
    }
}
impl<T,M,C,G,Cb,X> Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>> {
    /// Called by ordinary native root, Child and effect-group callbacks. Check
    /// the entire stored body's declarations before applying any instruction.
    #[verifier::rlimit(30)]
    pub fn run_service_program(&mut self,id:usize,program:&Program)->(out:Result<Report,AdmissionError>)
        requires old(self).wf(),program.valid(),
        ensures final(self).wf(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),final(self).execution_journal()==old(self).execution_journal(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> old(self).cleanup_state().live(id) && old(self).value_state().is_some() && program.declared(old(self).value_state().unwrap())
                && out->Ok_0.certified(program.code(),old(self).value_state().unwrap())
                && out->Ok_0.dynamic_semantics(program.code(),old(self).value_state().unwrap()) && out->Ok_0.ordered() && out->Ok_0.failure_ordered()
                && retained(out->Ok_0.steps@,*final(self),id,old(self).cleanup_state().queues()[id].slots().len())
                && out->Ok_0.queue_semantics(*final(self),id,old(self).cleanup_state().queues()[id].slots().len())
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting()+tokens(out->Ok_0.steps@)
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots(),
            final(self).status_links()==old(self).status_links(),
    {
        if !self.accepts_acquisition(id) {return Err(AdmissionError::Closed);}
        let episode=match self.native() {Some(episode)=>episode,None=>return Err(AdmissionError::NoNativeOwner)};
        if let Some(pc)=program.missing(episode) {return Err(AdmissionError::Undeclared {pc,port:program.code[pc].port});}
        let ghost initial=*self;let ghost values=self.value_state().unwrap();
        let ghost offset=self.cleanup_state().queues()[id].slots().len();
        let tracked mut receipts=Map::tracked_empty();
        let mut steps:Vec<Step>=Vec::new();let tracked mut previous:Option<joint::Receipt>=None;let mut pc=if program.code.is_empty() {None} else {Some(0usize)};
        proof {empty_prefix(program.code(),values);}
        while pc.is_some()
            invariant initial==*old(self),offset==initial.cleanup_state().queues()[id].slots().len(),initial.cleanup_state().live(id),self.wf(),program.valid(),program.declared(values),self.value_state()==Some(values),initial.value_state()==Some(values),
                self.status_links()==initial.status_links(),self.capture()==initial.capture(),self.work_state()==initial.work_state(),self.phase_spec()==initial.phase_spec(),self.execution_journal()==initial.execution_journal(),
                previous.is_some()==(steps.len()>0),previous.is_some() ==> previous.unwrap().wf() && previous.unwrap().same(&steps@.last().write.admission.registration().completion()) && previous.unwrap().covers(&steps@.last().write.admission.registration().write()),
                (Report {steps,failure:None,receipts:Tracked(receipts)}).ordered(),
                (Report {steps,failure:None,receipts:Tracked(receipts)}).witnessed(),
                prefix(program.code(),steps@,values),pc==next(program.code(),steps@),pc.is_some() ==> pc.unwrap()<program.code().len(),
                retained(steps@,*self,id,offset),
                self.cleanup_state().queues()[id].protocol().waiting()==initial.cleanup_state().queues()[id].protocol().waiting()+tokens(steps@),
                self.cleanup_state().queues()[id].slots().take(offset as int)==initial.cleanup_state().queues()[id].slots(),
            decreases if pc.is_some() {program.code.len()-pc.unwrap()} else {0},
        {
            let at=pc.unwrap();let call=program.code[at];let ghost prior=*self;let ghost earlier_steps=steps@;
            let write=match self.apply_native_value_chained(id,call.port,call.instruction.operation,call.instruction.branch,Tracked(match &previous {Some(receipt)=>Some(receipt.duplicate()),None=>None})) {
                Ok(write)=>write,
                Err(error)=>{
                    let ghost rejection=access::failure_witness(prior,*self,id,call.port,call.instruction.operation,error);
                    proof {
                        if rejection.is_some() {
                            self.representation();
                            let tracked rejected=self.attempts.borrow().latest();
                            receipts.tracked_insert((steps.len() as int,false),rejected);
                        }
                        let report=Report {steps,failure:Some(Failure {pc:at,error,rejection:Ghost(rejection)}),receipts:Tracked(receipts)};
                        report.interpret_dynamic(program,values);report.interpret_queue(*self,id,offset);
                    }
                    return Ok(Report::failed(steps,Failure {pc:at,error,rejection:Ghost(rejection)},Tracked(receipts)));
                },
            };
            proof {
                assert(call.instruction.valid(at as int,program.code().len()));
                append_prefix(program.code(),earlier_steps,values,Step {pc:at,write});
                append_tokens(earlier_steps,Step {pc:at,write});
                append_retained(earlier_steps,prior,*self,id,offset,Step {pc:at,write});
            }
            proof {
                if earlier_steps.len()>0 && previous.unwrap().journal()==write.admission.registration().write().journal() {
                    write.admission.registration().write().after_cover(&previous.unwrap(),&earlier_steps.last().write.admission.registration().write());
                }
            }
            proof {write.admission.evidence.borrow().retain(&mut receipts,steps.len() as int);}
            let Tracked(last)=write.admission.completion_receipt();proof {previous=Some(last);}
            pc=write.admission.next;steps.push(Step {pc:at,write});
            proof {
                assert forall|i:int| 0<i<steps.len() && steps@[i].write.admission.registration().write().journal()==steps@[i-1].write.admission.registration().write().journal()
                    implies (#[trigger] steps@[i]).write.admission.registration().write().follows(&steps@[i-1].write.admission.registration().write()) by {
                    if i<earlier_steps.len() {assert(steps@[i]==earlier_steps[i]);assert(steps@[i-1]==earlier_steps[i-1]);}
                }
            }
        }
        let report=Report {steps,failure:None,receipts:Tracked(receipts)};
        proof {report.interpret_dynamic(program,values);report.interpret_queue(*self,id,offset);}
        Ok(report)
    }
}
}
