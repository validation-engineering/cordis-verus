//! Whole finite function interpretation with dynamic service resolution as an
//! explicit input. Every resolution schedule has a least-grammar inhabitant on
//! the full allocation carrier. Actual reports supply authenticated selections;
//! aliases and interleavings are not assumed to be independent named ports.
#[cfg(verus_keep_ghost)]
use super::{
    access, alias, effect,
    services::{self, Call},
    slot::ServiceSlot,
    Outcome, ValueState,
};
use super::{
    joint,
    services::{Program, Report},
};
#[cfg(verus_keep_ghost)]
use crate::{dependent_grammar as d, lifecycle_state::services::NativeEpisode};
use vstd::prelude::*;

verus! {
/// Qualify local keys by the actual Journal; equal numeric keys in separate
/// domains never identify one allocation or manufacture a shared total order.
pub ghost struct Address {pub journal:joint::Journal,pub key:nat}
pub type Resolution=spec_fn(usize)->Address;
pub open spec fn address(write:access::Write)->Address {
    let receipt=write.admission.registration().write();Address {journal:receipt.journal(),key:receipt.event().key}
}
/// Export the allocation address from the actual write receipt before lifting
/// its state. This does not require a global cross-Journal observation.
pub proof fn address_origin(write:access::Write)
    ensures address(write).journal==write.admission.registration().write().journal(),
        address(write).key==write.admission.registration().write().event().key,
{}
pub open spec fn qualify(journal:joint::Journal,heap:Map<nat,ValueState>)->Map<Address,ValueState> {
    Map::new(heap.dom().map_by(|key:nat|Address {journal,key},|a:Address|a.key),|a:Address|heap[a.key])
}
proof fn qualify_insert(journal:joint::Journal,heap:Map<nat,ValueState>,key:nat,value:ValueState)
    ensures qualify(journal,heap.insert(key,value))==qualify(journal,heap).insert(Address {journal,key},value),
{
    broadcast use Set::lemma_map_by_contains;
    assert(qualify(journal,heap.insert(key,value)) =~= qualify(journal,heap).insert(Address {journal,key},value));
}
proof fn qualified_write(write:access::Write,call:Call)
    requires write.corresponds(call.instruction.operation,call.instruction.branch),
    ensures {
        let r=write.admission.registration().write();let event=r.event().change->Value_event;
        let run=d::run(alias::library(),alias::node(address(write),alias::operation_code(call.instruction.operation),call.instruction.branch),
            qualify(r.journal(),access::objects(joint::state_at(r.events(),r.at()))));
        &&& run.is_some() && run.unwrap().state==qualify(r.journal(),access::objects(r.events().last().state))
        &&& run.unwrap().next==write.admission.next
        &&& forall|recovery:Map<Address,ValueState>| #[trigger] (run.unwrap().undo)(recovery)==
            if recovery.contains_key(address(write)) && recovery[address(write)]==event.after()
                {Some(recovery.insert(address(write),event.before()))} else {None}
    },
{
    broadcast use Set::lemma_map_by_contains;
    address_origin(write);write.general_semantics();
    let r=write.admission.registration().write();let event=r.event().change->Value_event;
    r.transition();reveal(joint::changes);
    assert(access::objects(joint::state_at(r.events(),r.at()))[r.event().key]==event.before());
    alias::operation_agrees(call.instruction.operation,event.before());
    qualify_insert(r.journal(),access::objects(joint::state_at(r.events(),r.at())),r.event().key,event.after());
}

pub open spec fn node(code:Seq<Call>,resolution:Resolution,pc:usize)->d::Node<Address,(Address,effect::Code),(),ValueState,Outcome,usize> {
    if pc<code.len() {alias::node(resolution(pc),alias::operation_code(code[pc as int].instruction.operation),code[pc as int].instruction.branch)}
    else {d::Node::Unit}
}
pub open spec fn program(code:Seq<Call>,resolution:Resolution)->d::Program<Address,(Address,effect::Code),(),ValueState,Outcome,usize> {
    |pc:usize|node(code,resolution,pc)
}
pub open spec fn keys(code:Seq<Call>,resolution:Resolution)->ISet<Address> {
    ISet::new(|key:Address|exists|pc:usize| pc<code.len() && #[trigger] resolution(pc)==key)
}
impl Program {
    /// Universal in both the input heap and the resolution schedule, including
    /// unselected branches and failure domains. Resolution is an explicit
    /// environment input, not a promise that a service slot never changes.
    pub proof fn resolved_member(&self,resolution:Resolution,pc:usize)
        requires self.valid(),
        ensures d::member(alias::library(),program(self.code(),resolution),keys(self.code(),resolution),ISet::empty(),pc),
        decreases if pc<self.code().len() {self.code().len()-pc} else {0},
    {
        self.shape();
        if pc<self.code().len() {
            assert(self.code()[pc as int].instruction.valid(pc as int,self.code().len()));
            let branch=self.code()[pc as int].instruction.branch;
            if branch.matched.is_some() {self.resolved_member(resolution,branch.matched.unwrap());}
            if branch.unmatched.is_some() {self.resolved_member(resolution,branch.unmatched.unwrap());}
            assert(keys(self.code(),resolution).contains(resolution(pc)));
            assert forall|out:Outcome| branch.selected(out).is_some() implies
                d::members(alias::library(),program(self.code(),resolution),keys(self.code(),resolution),ISet::empty()).contains(branch.selected(out).unwrap()) by { }
        }
        d::constructor_member(alias::library(),program(self.code(),resolution),keys(self.code(),resolution),ISet::empty(),pc);
    }
}
pub open spec fn forward(steps:Seq<services::Step>)->bool {
    forall|i:int,j:int| #![trigger steps[i],steps[j]] 0<=i<j<steps.len() ==> steps[i].pc<steps[j].pc
}
proof fn transitive_points(steps:Seq<services::Step>,i:int,j:int)
    requires 0<=i<j<steps.len(),forall|k:int| 0<k<steps.len() ==> (#[trigger] steps[k-1]).pc<steps[k].pc,
    ensures steps[i].pc<steps[j].pc,
    decreases j-i,
{assert(steps[j-1].pc<steps[j].pc);if j>i+1 {transitive_points(steps,i,j-1);}}
impl Report {
    pub open spec fn resolution(&self)->Resolution {
        |pc:usize| if exists|i:int| 0<=i<self.steps.len() && (#[trigger] self.steps@[i]).pc==pc {
            let i=choose|i:int| 0<=i<self.steps.len() && (#[trigger] self.steps@[i]).pc==pc;
            address(self.steps@[i].write)
        } else if self.failure.is_some() && self.failure.unwrap().position()==pc && self.failure.unwrap().rejection().is_some() {
            let r=self.failure.unwrap().rejection().unwrap().receipt;Address {journal:r.journal(),key:r.event().key}
        } else {arbitrary()}
    }
    pub proof fn forward_points<T,M>(&self,body:&Program,episode:NativeEpisode<ServiceSlot<T,M>>)
        requires body.valid(),self.certified(body.code(),episode),
        ensures forward(self.steps@),
    {
        body.shape();reveal(services::prefix);
        assert forall|i:int| 0<i<self.steps.len() implies (#[trigger] self.steps@[i-1]).pc<self.steps@[i].pc by {
            assert(self.steps@.take(i).last()==self.steps@[i-1]);
            let prev=self.steps@[i-1];let call=body.code()[prev.pc as int];
            assert(call.instruction.valid(prev.pc as int,body.code().len()));
        }
        assert forall|i:int,j:int| #![trigger self.steps@[i],self.steps@[j]] 0<=i<j<self.steps.len()
            implies self.steps@[i].pc<self.steps@[j].pc by {transitive_points(self.steps@,i,j);}
    }
    pub proof fn resolution_at(&self,i:int)
        requires forward(self.steps@),0<=i<self.steps.len(),
        ensures (self.resolution())(self.steps@[i].pc)==address(self.steps@[i].write),
    {
        let pc=self.steps@[i].pc;
        assert(exists|j:int| 0<=j<self.steps.len() && (#[trigger] self.steps@[j]).pc==pc);
        let j=choose|j:int| 0<=j<self.steps.len() && (#[trigger] self.steps@[j]).pc==pc;
        if j<i {assert(self.steps@[j].pc<self.steps@[i].pc);} else if i<j {assert(self.steps@[i].pc<self.steps@[j].pc);}
        assert(i==j);
    }
    /// A failed instruction has not executed previously: branches strictly
    /// increase the program counter. Its actual rejection supplies its address.
    pub proof fn failure_resolution<T,M>(&self,body:&Program,episode:NativeEpisode<ServiceSlot<T,M>>)
        requires body.valid(),self.certified(body.code(),episode),forward(self.steps@),
            self.failure.is_some(),self.failure.unwrap().rejection().is_some(),
        ensures {
            let failure=self.failure.unwrap();let r=failure.rejection().unwrap().receipt;
            (self.resolution())(failure.position())==(Address {journal:r.journal(),key:r.event().key})
        },
    {
        body.shape();reveal(services::prefix);
        let failure=self.failure.unwrap();
        if self.steps.len()>0 {
            let last=self.steps@.last();
            assert(body.code()[last.pc as int].instruction.valid(last.pc as int,body.code().len()));
            assert(last.pc<failure.position());
        }
        assert forall|i:int| 0<=i<self.steps.len() implies (#[trigger] self.steps@[i]).pc!=failure.position() by {
            if i<self.steps.len()-1 {assert(self.steps@[i].pc<self.steps@.last().pc);}
        }
    }
    pub open spec fn failure_semantics(&self,code:Seq<Call>)->bool {
        self.failure.is_some() && self.failure.unwrap().rejection().is_some() ==> {
            let failure=self.failure.unwrap();let r=failure.rejection().unwrap().receipt;
            &&& (self.resolution())(failure.position())==(Address {journal:r.journal(),key:r.event().key})
            &&& d::run(alias::library(),node(code,self.resolution(),failure.position()),
                qualify(r.journal(),access::objects(joint::state_at(r.events(),r.at())))).is_none()
            &&& joint::state_at(r.events(),r.at())==r.events().last().state
            &&& joint::pending_at(r.events(),r.at())==r.events().last().pending
        }
    }
    pub proof fn interpret_failure<T,M>(&self,body:&Program,episode:NativeEpisode<ServiceSlot<T,M>>)
        requires body.valid(),self.certified(body.code(),episode),forward(self.steps@),
        ensures self.failure_semantics(body.code()),
    {
        broadcast use Set::lemma_map_by_contains;
        if self.failure.is_some() && self.failure.unwrap().rejection().is_some() {
            self.failure_resolution(body,episode);
            let failure=self.failure.unwrap();let rejection=failure.rejection().unwrap();let r=rejection.receipt;
            assert(rejection.certified(episode,body.code()[failure.position() as int].port,
                body.code()[failure.position() as int].instruction.operation,failure.error_spec()->Value_0));
            rejection.stutters();r.transition();reveal(joint::changes);
            assert(access::objects(joint::state_at(r.events(),r.at()))[r.event().key]==r.event().change->Value_event.before());
            alias::operation_agrees(body.code()[failure.position() as int].instruction.operation,r.event().change->Value_event.before());
        }
    }
    /// The real selected allocation, actual operation/outcome/continuation,
    /// and returned strict inverse at every instruction of this complete body.
    /// Intervening events remain in each receipt's authoritative input history.
    #[verifier::opaque]
    pub open spec fn dynamic_semantics<T,M>(&self,code:Seq<Call>,episode:NativeEpisode<ServiceSlot<T,M>>)->bool {
        &&& self.certified(code,episode) && forward(self.steps@) && self.failure_semantics(code)
        &&& d::member(alias::library(),program(code,self.resolution()),keys(code,self.resolution()),ISet::empty(),0)
        &&& forall|i:int| 0<=i<self.steps.len() ==> {
            let step=#[trigger] self.steps@[i];let r=step.write.admission.registration().write();let event=r.event().change->Value_event;
            let run=d::run(alias::library(),node(code,self.resolution(),step.pc),qualify(r.journal(),access::objects(joint::state_at(r.events(),r.at()))));
            &&& (self.resolution())(step.pc)==address(step.write)
            &&& address(step.write).journal==step.write.binding.capture_spec().value_spec().journal_spec()
            &&& address(step.write).key==step.write.binding.capture_spec().value_spec().object().key
            &&& run.is_some() && run.unwrap().state==qualify(r.journal(),access::objects(r.events().last().state))
            &&& run.unwrap().next==step.write.admission.next
            &&& forall|recovery:Map<Address,ValueState>| #[trigger] (run.unwrap().undo)(recovery)==
                if recovery.contains_key(address(step.write)) && recovery[address(step.write)]==event.after()
                    {Some(recovery.insert(address(step.write),event.before()))} else {None}
        }
    }
    pub proof fn interpret_dynamic<T,M>(&self,body:&Program,episode:NativeEpisode<ServiceSlot<T,M>>)
        requires body.valid(),self.certified(body.code(),episode),
        ensures self.dynamic_semantics(body.code(),episode),
    {
        reveal(Report::dynamic_semantics);self.forward_points(body,episode);self.interpret_failure(body,episode);body.resolved_member(self.resolution(),0);reveal(services::prefix);
        assert forall|i:int| 0<=i<self.steps.len() implies {
            let step=#[trigger] self.steps@[i];let r=step.write.admission.registration().write();let event=r.event().change->Value_event;
            let run=d::run(alias::library(),node(body.code(),self.resolution(),step.pc),qualify(r.journal(),access::objects(joint::state_at(r.events(),r.at()))));
            &&& (self.resolution())(step.pc)==address(step.write)
            &&& address(step.write).journal==step.write.binding.capture_spec().value_spec().journal_spec()
            &&& address(step.write).key==step.write.binding.capture_spec().value_spec().object().key
            &&& run.is_some() && run.unwrap().state==qualify(r.journal(),access::objects(r.events().last().state))
            &&& run.unwrap().next==step.write.admission.next
            &&& forall|recovery:Map<Address,ValueState>| #[trigger] (run.unwrap().undo)(recovery)==
                if recovery.contains_key(address(step.write)) && recovery[address(step.write)]==event.after()
                    {Some(recovery.insert(address(step.write),event.before()))} else {None}
        } by {self.resolution_at(i);qualified_write(self.steps@[i].write,body.code()[self.steps@[i].pc as int]);}
    }
}
}
