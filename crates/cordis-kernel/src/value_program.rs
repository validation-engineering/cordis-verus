//! Finite, outcome-selected programs over the real shared service value.
//! A program executes under the value's lock; its inverses are returned in
//! execution order to the actual episode owner, which retains every one.
use super::{
    joint, Applied, Branch, Inverse, Operation, Outcome, ReversibleValue, Snapshot, ValueError,
    ValueState,
};
#[cfg(verus_keep_ghost)]
use super::{library, operation, Event};
use crate::execution::Execution;
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
#[cfg(verus_keep_ghost)]
use crate::{dependent_grammar as d, fresh_grammar as f, guarded_components as c, Port};
use std::collections::VecDeque;
use vstd::prelude::*;

verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Instruction {pub operation:Operation,pub branch:Branch}
impl Instruction {
    pub open spec fn valid(&self,pc:int,length:nat)->bool {
        (self.branch.matched.is_some() ==> pc<self.branch.matched.unwrap()<length)
            && (self.branch.unmatched.is_some() ==> pc<self.branch.unmatched.unwrap()<length)
    }
    pub(crate) fn check(&self,pc:usize,length:usize)->(out:bool) ensures out==self.valid(pc as int,length as nat), {
        let yes=match self.branch.matched {None=>true,Some(n)=>pc<n && n<length};
        let no=match self.branch.unmatched {None=>true,Some(n)=>pc<n && n<length};yes && no
    }
}
pub struct Program {code:Vec<Instruction>}
impl Program {
    pub closed spec fn code(&self)->Seq<Instruction> {self.code@}
    pub closed spec fn valid(&self)->bool {forall|i:int| 0<=i<self.code().len() ==> #[trigger] self.code()[i].valid(i,self.code().len())}
    pub fn new(code:Vec<Instruction>)->(out:Result<Self,Vec<Instruction>>)
        ensures out.is_ok() ==> out->Ok_0.valid() && out->Ok_0.code()==code@,
            out.is_err() ==> out->Err_0==code && exists|i:int| 0<=i<code.len() && !code@[i].valid(i,code.len() as nat),
    {
        let mut i=0;
        while i<code.len()
            invariant i<=code.len(),forall|j:int| 0<=j<i ==> #[trigger] code@[j].valid(j,code.len() as nat),
            decreases code.len()-i,
        {
            if !code[i].check(i,code.len()) {return Err(code);}
            i+=1;
        }
        Ok(Self {code})
    }
    /// Revalidate stored code when it crosses a generic registry boundary.
    pub fn check(&self)->(out:bool) ensures out==self.valid(), {
        let mut i=0;
        while i<self.code.len()
            invariant i<=self.code.len(),forall|j:int| 0<=j<i ==> #[trigger] self.code()[j].valid(j,self.code().len()),
            decreases self.code.len()-i,
        {if !self.code[i].check(i,self.code.len()) {assert(!self.code()[i as int].valid(i as int,self.code().len()));return false;}i+=1;}
        true
    }
    pub open spec fn root(&self)->Option<usize> {if self.code().len()==0 {None} else {Some(0)}}
    pub proof fn valid_instruction(&self,pc:usize)
        requires self.valid(),pc<self.code().len(),
        ensures self.code()[pc as int].valid(pc as int,self.code().len()),
    {}
    pub fn instruction(&self,pc:usize)->(out:Option<Instruction>)
        ensures out==if pc<self.code().len() {Some(self.code()[pc as int])} else {None},
    {if pc<self.code.len() {Some(self.code[pc])} else {None}}
    pub fn len(&self)->(out:usize) ensures out==self.code().len(), {self.code.len()}
    pub fn is_empty(&self)->(out:bool) ensures out==(self.code().len()==0), {self.code.is_empty()}
}
pub open spec fn node(code:Seq<Instruction>,key:Port,pc:usize)->d::Node<Port,(Port,Operation),(),ValueState,Outcome,usize> {
    if pc<code.len() {d::Node::Operation {operation:(key,code[pc as int].operation),argument:(),select:|out:Outcome|code[pc as int].branch.selected(out)}} else {d::Node::Unit}
}
pub open spec fn programs(code:Seq<Instruction>,key:Port)->f::Programs<(Port,Operation),(),ValueState,Outcome,usize> {
    |_:usize| |pc:usize| f::Node::Dependent {node:node(code,key,pc)}
}
impl Program {
    pub proof fn member(&self,key:Port,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,pc:usize)
        requires self.valid(),keys.contains(key),
        ensures f::member(library(),programs(self.code(),key),actor,keys,provisions,pc),
        decreases if pc<self.code().len() {self.code().len()-pc} else {0},
    {
        let ps=programs(self.code(),key);
        if pc<self.code().len() {
            let instruction=self.code()[pc as int];assert(instruction.valid(pc as int,self.code().len()));
            if instruction.branch.matched.is_some() {self.member(key,actor,keys,provisions,instruction.branch.matched.unwrap());}
            if instruction.branch.unmatched.is_some() {self.member(key,actor,keys,provisions,instruction.branch.unmatched.unwrap());}
            assert forall|out:Outcome| instruction.branch.selected(out).is_some() implies
                f::members(library(),ps).contains((actor,keys,provisions,instruction.branch.selected(out).unwrap())) by { }
        }
        f::constructor_member(library(),ps,actor,keys,provisions,pc);
    }
    /// Membership covers all legal contexts and every selected continuation,
    /// independently of whether a particular program run happens to succeed.
    pub proof fn component(&self,key:Port,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,pc:usize)
        requires self.valid(),keys.contains(key),
        ensures c::component(library(),programs(self.code(),key),actor,keys,provisions,pc),
    {
        super::primitive_theory();self.member(key,actor,keys,provisions,pc);
        c::member_is_component(|_:Port,a:ValueState,b:ValueState|a==b,library(),programs(self.code(),key),actor,keys,provisions,pc);
    }
}

pub struct Point {pub state:ValueState,pub next:Option<usize>}
pub open spec fn prefix(code:Seq<Instruction>,points:Seq<Point>,outcomes:Seq<Outcome>)->bool {
    &&& points.len()==outcomes.len()+1
    &&& points.first().next==if code.len()==0 {None} else {Some(0)}
    &&& forall|i:int| 0<=i<points.len() ==> (#[trigger] points[i].next.is_some() ==> points[i].next.unwrap()<code.len())
    &&& forall|i:int| 0<=i<outcomes.len() ==> {
        let before=points[i];let after=points[i+1];
        &&& before.next.is_some()
        &&& operation(code[before.next.unwrap() as int].operation)(before.state).is_some()
        &&& operation(code[before.next.unwrap() as int].operation)(before.state).unwrap().value==after.state
        &&& operation(code[before.next.unwrap() as int].operation)(before.state).unwrap().outcome==#[trigger] outcomes[i]
        &&& after.next==code[before.next.unwrap() as int].branch.selected(outcomes[i])
    }
}
pub proof fn extend_prefix(code:Seq<Instruction>,points:Seq<Point>,outcomes:Seq<Outcome>,outcome:Outcome,after:Point)
    requires prefix(code,points,outcomes),points.last().next.is_some(),
        operation(code[points.last().next.unwrap() as int].operation)(points.last().state).is_some(),
        operation(code[points.last().next.unwrap() as int].operation)(points.last().state).unwrap().value==after.state,
        operation(code[points.last().next.unwrap() as int].operation)(points.last().state).unwrap().outcome==outcome,
        after.next==code[points.last().next.unwrap() as int].branch.selected(outcome),
        after.next.is_some() ==> after.next.unwrap()<code.len(),
    ensures prefix(code,points.push(after),outcomes.push(outcome)),
{
    assert forall|i:int| 0<=i<outcomes.push(outcome).len() implies {
        let before=points.push(after)[i];let end=points.push(after)[i+1];
        &&& before.next.is_some()
        &&& operation(code[before.next.unwrap() as int].operation)(before.state).is_some()
        &&& operation(code[before.next.unwrap() as int].operation)(before.state).unwrap().value==end.state
        &&& operation(code[before.next.unwrap() as int].operation)(before.state).unwrap().outcome==#[trigger] outcomes.push(outcome)[i]
        &&& end.next==code[before.next.unwrap() as int].branch.selected(outcomes.push(outcome)[i])
    } by {if i<outcomes.len() {assert(outcomes.push(outcome)[i]==outcomes[i]);}}
}
pub open spec fn source_steps(code:Seq<Instruction>,key:Port,points:Seq<Point>,states:Seq<Map<Port,ValueState>>)->bool {
    states.len()==points.len() && forall|i:int| #![trigger states[i]] 0<=i<points.len()-1 ==> {
        let step=d::run(library(),node(code,key,points[i].next.unwrap()),states[i]);
        &&& points[i].next.is_some() && points[i].next.unwrap()<code.len()
        &&& step.is_some() && step.unwrap().state==states[i+1] && step.unwrap().next==points[i+1].next
    }
}
pub open spec fn instruction_event(code:Seq<Instruction>,points:Seq<Point>,outcomes:Seq<Outcome>,i:int)->Event {
    let instruction=code[points[i].next.unwrap() as int];
    Event::Forward {operation:instruction.operation,branch:instruction.branch,before:points[i].state,after:points[i+1].state,outcome:outcomes[i],next:points[i+1].next}
}
pub open spec fn recorded(code:Seq<Instruction>,points:Seq<Point>,outcomes:Seq<Outcome>,offset:nat,events:Seq<Event>)->bool {
    offset+outcomes.len()<=events.len() && forall|i:int| 0<=i<outcomes.len() ==> #[trigger] events[offset+i]==instruction_event(code,points,outcomes,i)
}
#[allow(dead_code)]
#[must_use]
pub struct ProgramReport {pub outcomes:Vec<Outcome>,pub error:Option<ValueError>,pub snapshot:Snapshot,points:Ghost<Seq<Point>>,offset:Ghost<nat>,registrations:Ghost<Seq<super::registration::Evidence>>,pub(crate) receipts:Tracked<super::registration::ReceiptMap>}
impl ProgramReport {
    pub closed spec fn receipts(&self)->super::registration::ReceiptMap {self.receipts@}
    pub(crate) fn receipt_witnesses(&self)->(out:Tracked<&super::registration::ReceiptMap>)
        ensures *out@==self.receipts(),
    {Tracked(self.receipts.borrow())}
    pub open spec fn witnessed(&self)->bool {
        super::registration::witnesses(self.receipts())
            && self.receipts().contains_key((-1,false))
            && self.receipts()[(-1,false)].journal()==self.observation().journal_spec()
            && self.receipts()[(-1,false)].events()==self.observation().joint_spec().events()
            && forall|i:int| 0<=i<self.registrations().len() ==>
                super::registration::recorded_in(self.receipts(),i,#[trigger] self.registrations()[i])
    }
    pub closed spec fn registrations(&self)->Seq<super::registration::Evidence> {self.registrations@}
    pub open spec fn registered(&self)->bool {
        self.witnessed() && self.registrations().len()==self.results().len() && forall|i:int| 0<=i<self.results().len() ==> {
            let evidence=#[trigger] self.registrations()[i];
            &&& evidence.certified() && evidence.write().journal()==self.observation().journal_spec()
            &&& evidence.write().at()==self.joint_positions()[i]
            &&& evidence.write().event().key==self.observation().object().key
            &&& evidence.write().event().change==(joint::Change::Value {event:self.observation().history()[self.offset()+i]})
        }
    }

    pub closed spec fn offset(&self)->nat {self.offset@}
    pub open spec fn joint_positions(&self)->Seq<nat> {Seq::new(self.results().len(),|i:int|self.observation().positions()[self.offset()+i])}
    pub closed spec fn failure(&self)->Option<ValueError> {self.error}
    pub fn error(&self)->(out:Option<ValueError>) ensures out==self.failure(), {self.error}
    pub closed spec fn points(&self)->Seq<Point> {self.points@}
    pub closed spec fn results(&self)->Seq<Outcome> {self.outcomes@}
    pub closed spec fn observation(&self)->Snapshot {self.snapshot}
    pub closed spec fn certified(&self,code:Seq<Instruction>)->bool {
        &&& prefix(code,self.points(),self.outcomes@)
        &&& self.snapshot.certified() && self.snapshot.state()==self.points().last().state
        &&& self.snapshot.history().len()==self.offset()+self.results().len()+if self.error.is_some() {1nat} else {0nat}
        &&& recorded(code,self.points(),self.results(),self.offset(),self.snapshot.history())
        &&& self.error.is_some() ==> self.snapshot.history().last()==(Event::Rejected {operation:code[self.points().last().next.unwrap() as int].operation,before:self.points().last().state})
        &&& if self.error.is_none() {self.points().last().next.is_none()} else {
            self.points().last().next.is_some() && operation(code[self.points().last().next.unwrap() as int].operation)(self.points().last().state).is_none()
        }
    }
    /// Every successful instruction has a concrete, ordered position in the
    /// same domain trace as slot swaps and lifecycle steps. These positions
    /// are captured from the authoritative lock, not supplied by a caller.
    pub proof fn registered_instruction(&self,code:Seq<Instruction>,i:int)
        requires self.certified(code),self.registered(),0<=i<self.results().len(),
        ensures self.registrations()[i].certified(),
            self.registrations()[i].write().event().change==(joint::Change::Value {event:instruction_event(code,self.points(),self.results(),i)}),
    {}
    pub proof fn joint_steps(&self,code:Seq<Instruction>)
        requires self.certified(code),
        ensures self.joint_positions().len()==self.results().len(),
            forall|i:int| 0<=i<self.results().len() ==> {
                let at=#[trigger] self.joint_positions()[i];let frames=self.observation().joint_spec().events();
                &&& at<frames.len() && frames[at as int].event.key==self.observation().object().key
                &&& frames[at as int].event.change==(joint::Change::Value {event:instruction_event(code,self.points(),self.results(),i)})
            },
            forall|i:int,j:int| 0<=i<j<self.results().len() ==> #[trigger] self.joint_positions()[i]<#[trigger] self.joint_positions()[j],
    {
        self.snapshot.projection();
        assert forall|i:int| 0<=i<self.results().len() implies {
            let at=#[trigger] self.joint_positions()[i];let frames=self.observation().joint_spec().events();
            &&& at<frames.len() && frames[at as int].event.key==self.observation().object().key
            &&& frames[at as int].event.change==(joint::Change::Value {event:instruction_event(code,self.points(),self.results(),i)})
        } by {assert(self.snapshot.history()[self.offset()+i]==instruction_event(code,self.points(),self.results(),i));}
    }
    pub open spec fn failed_position(&self)->nat {self.observation().positions()[(self.offset()+self.results().len()) as int]}
    pub proof fn joint_rejection(&self,code:Seq<Instruction>)
        requires self.certified(code),self.failure().is_some(),
        ensures self.failed_position()<self.observation().joint_spec().events().len(),
            self.observation().joint_spec().events()[self.failed_position() as int].event.key==self.observation().object().key,
            self.observation().joint_spec().events()[self.failed_position() as int].event.change==(joint::Change::Value {event:Event::Rejected {
                operation:code[self.points().last().next.unwrap() as int].operation,before:self.points().last().state}}),
            forall|i:int| 0<=i<self.results().len() ==> #[trigger] self.joint_positions()[i]<self.failed_position(),
    {self.snapshot.projection();assert(self.offset()+self.results().len()==self.snapshot.history().len()-1);}
    /// An actual contiguous source execution. Both rejected programs and
    /// successful ones retain the certified prefix that really ran.
    pub proof fn source_execution(&self,code:Seq<Instruction>,key:Port,initial:Map<Port,ValueState>)->(states:Seq<Map<Port,ValueState>>)
        requires self.certified(code),initial.contains_key(key),initial[key]==self.points().first().state,
        ensures states.len()==self.results().len()+1,states.first()==initial,
            states.last()==initial.insert(key,self.observation().state()),
            source_steps(code,key,self.points(),states),
    {
        let states=self.points().map(|_:int,p:Point|initial.insert(key,p.state));
        assert(states.first() =~= initial);
        assert forall|i:int| #![trigger states[i]] 0<=i<self.points().len()-1 implies {
            let step=d::run(library(),node(code,key,self.points()[i].next.unwrap()),states[i]);
            &&& self.points()[i].next.is_some() && self.points()[i].next.unwrap()<code.len()
            &&& step.is_some() && step.unwrap().state==states[i+1] && step.unwrap().next==self.points()[i+1].next
        } by {
            assert(self.outcomes@[i]==self.results()[i]);
            assert(self.points()[i].next.is_some());
            assert(self.points()[i].next.unwrap()<code.len());
            assert(operation(code[self.points()[i].next.unwrap() as int].operation)(self.points()[i].state).unwrap().outcome==self.outcomes@[i]);
            assert(initial.insert(key,self.points()[i].state).insert(key,self.points()[i+1].state) =~= initial.insert(key,self.points()[i+1].state));
        }
        assert(source_steps(code,key,self.points(),states));
        states
    }
}
pub(crate) struct Batch {pub(crate) items:VecDeque<Applied>,pub(crate) report:ProgramReport}
impl Batch {
    pub(crate) closed spec fn certified(&self,program:&Program,value:&ReversibleValue,managed:bool)->bool {
        &&& self.report.certified(program.code())
        &&& self.report.snapshot.source()==value.source() && self.report.snapshot.object()==value.object()
        &&& self.report.snapshot.journal_spec()==value.journal_spec()
        &&& self.items@.len()==self.report.outcomes.len()
        &&& forall|i:int| 0<=i<self.items@.len() ==> {
            let pc=self.report.points()[i].next.unwrap();let instruction=program.code()[pc as int];
            &&& self.items@[i].pending_for(managed)
            &&& (#[trigger] self.items@[i]).corresponds(value,instruction.operation,instruction.branch)
            &&& self.items@[i].outcome==self.report.outcomes@[i]
            &&& self.items@[i].inverse.origin().at()==self.report.joint_positions()[i]
            &&& self.items@[i].inverse.state().before==self.report.points()[i].state
            &&& self.items@[i].inverse.state().after==self.report.points()[i+1].state
        }
    }
}
impl ReversibleValue {
    pub(crate) fn run_following(&self,program:&Program,Ghost(managed):Ghost<bool>,Tracked(cause):Tracked<Option<joint::Receipt>>)->(out:Batch)
        requires program.valid(),cause.is_some() ==> cause.unwrap().wf(),
        ensures out.certified(program,self,managed),out.report.witnessed(),
            cause.is_some() && cause.unwrap().journal()==self.journal_spec() ==>
                forall|i:int| 0<=i<out.items@.len() ==> (#[trigger] out.items@[i]).inverse.origin().follows(&cause.unwrap()),
    {
        let (mut cell,guard)=self.inner.acquire_write();
        let mut current=if program.code.is_empty() {None} else {Some(0usize)};
        let mut items:VecDeque<Applied>=VecDeque::new();let mut outcomes:Vec<Outcome>=Vec::new();let mut error=None;
        let ghost mut points=seq![Point {state:cell.state,next:current}];
        let ghost offset=cell.history@.len();
        while current.is_some() && error.is_none()
            invariant program.valid(),cause.is_some() ==> cause.unwrap().wf(),
                cause.is_some() && cause.unwrap().journal()==self.journal_spec() ==>
                    forall|i:int| 0<=i<items@.len() ==> (#[trigger] items@[i]).inverse.origin().follows(&cause.unwrap()),
                cell.wf(),cell.initial@==self.initial(),cell.authority@.source()==self.source(),
                cell.joint.journal()==self.journal_spec(),cell.joint.key()==self.inner.pred().key,
                error.is_some() ==> current.is_some() && operation(program.code()[current.unwrap() as int].operation)(cell.state).is_none(),
                prefix(program.code(),points,outcomes@),points.last().state==cell.state,points.last().next==current,
                cell.history@.len()==offset+outcomes.len()+if error.is_some() {1nat} else {0nat},
                recorded(program.code(),points,outcomes@,offset,cell.history@),
                error.is_some() ==> cell.history@.last()==(Event::Rejected {operation:program.code()[points.last().next.unwrap() as int].operation,before:points.last().state}),
                items@.len()==outcomes.len(),
                forall|i:int| 0<=i<items@.len() ==> {
                    let pc=points[i].next.unwrap();let instruction=program.code()[pc as int];
                    &&& items@[i].pending_for(managed)
                    &&& (#[trigger] items@[i]).corresponds(self,instruction.operation,instruction.branch)
                    &&& items@[i].outcome==outcomes@[i]
                    &&& items@[i].inverse.origin().at()==cell.positions@[offset+i]
                    &&& items@[i].inverse.state().before==points[i].state
                    &&& items@[i].inverse.state().after==points[i+1].state
                },
            decreases if current.is_some() && error.is_none() {program.code.len()-current.unwrap()+1} else {0},
        {
            let pc=current.unwrap();let instruction=program.code[pc];
            let ghost events=cell.history@;let ghost old_points=points;let ghost old_outcomes=outcomes@;
            let tracked earlier=match cause {Some(ref receipt)=>Some(receipt.duplicate()),None=>None};
            match cell.forward_following(instruction.operation,instruction.branch,Ghost(managed),Tracked(earlier)) {
                Err(failure)=>{
                    error=Some(failure);
                    proof {
                        assert forall|i:int| 0<=i<outcomes.len() implies #[trigger] cell.history@[offset+i]==instruction_event(program.code(),points,outcomes@,i) by {
                            assert(cell.history@[offset+i]==events[offset+i]);
                        }
                    }
                },
                Ok(forward)=>{
                    proof {
                        assert(instruction.valid(pc as int,program.code().len()));
                        extend_prefix(program.code(),points,outcomes@,forward.outcome,Point {state:cell.state,next:forward.next});
                        points=points.push(Point {state:cell.state,next:forward.next});
                    }
                    current=forward.next;outcomes.push(forward.outcome);
                    proof {
                        assert forall|i:int| 0<=i<outcomes.len() implies #[trigger] cell.history@[offset+i]==instruction_event(program.code(),points,outcomes@,i) by {
                            if i<old_outcomes.len() {assert(cell.history@[offset+i]==events[offset+i]);}
                            else {assert(cell.history@[offset+i]==cell.history@.last());}
                        }
                    }
                    let tracked origin=cell.joint.receipt();
                    items.push_back(Applied {outcome:forward.outcome,next:forward.next,pending:forward.pending,inverse:Inverse {target:self.clone(),state:forward.inverse,origin:Tracked(origin)}});
                },
            }
        }
        let snapshot=cell.snapshot();guard.release_write(cell);
        proof {snapshot.production_state();assert(snapshot.joint_spec().events().len()>0);}
        let Tracked(observed)=snapshot.joint_execution().receipt();
        let tracked mut receipts=Map::tracked_empty();proof {receipts.tracked_insert((-1int,false),observed);}
        Batch {items,report:ProgramReport {outcomes,error,snapshot,points:Ghost(points),offset:Ghost(offset),registrations:Ghost(Seq::empty()),receipts:Tracked(receipts)}}
    }
}
impl<V,C,G,Cb,X> Execution<V,C,G,ChildCleanup<Cb,X>> {
    /// Admission is checked before any write. The checked interpreter keeps
    /// the value lock for the complete finite program, then this exclusive
    /// owner registers every actual inverse in order before returning.
    #[allow(clippy::len_zero)] // The pinned vstd specifies VecDeque::len, but not is_empty.
    pub fn run_value_program(&mut self,id:usize,value:&ReversibleValue,program:&Program)->(out:Result<ProgramReport,ValueError>)
        requires old(self).wf(),program.valid(),
        ensures final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> out==Err(ValueError::Closed) && *final(self)==*old(self),
            out.is_err()==!(old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)),
            out.is_ok() ==> out->Ok_0.certified(program.code()) && out->Ok_0.registered()
                && out->Ok_0.observation().source()==value.source() && out->Ok_0.observation().object()==value.object()
                && out->Ok_0.observation().journal_spec()==value.journal_spec()
                && final(self).cleanup_state().queues()[id].slots().len()==old(self).cleanup_state().queues()[id].slots().len()+out->Ok_0.results().len()
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots()
                && forall|i:int| #![trigger out->Ok_0.points()[i]] 0<=i<out->Ok_0.results().len() ==> {
                    let offset=old(self).cleanup_state().queues()[id].slots().len();let slot=final(self).cleanup_state().queues()[id].slots()[offset+i];
                    &&& slot.is_some() && slot.unwrap() is Value
                    &&& out->Ok_0.registrations()[i].records(slot.unwrap()->Value_0,final(self).cleanup_state().queues()[id].link(),
                        final(self).cleanup_state().queues()[id].protocol().domain_id(),(offset+i) as usize)
                    &&& slot.unwrap()->Value_0.target()==*value
                    &&& slot.unwrap()->Value_0.state().before==out->Ok_0.points()[i].state
                    &&& slot.unwrap()->Value_0.state().after==out->Ok_0.points()[i+1].state
                },
            final(self).status_links()==old(self).status_links(),
    {self.run_value_program_following(id,value,program,Tracked(None))}
    #[allow(clippy::len_zero)] // The checked VecDeque contract uses len.
    pub(crate) fn run_value_program_following(&mut self,id:usize,value:&ReversibleValue,program:&Program,Tracked(cause):Tracked<Option<joint::Receipt>>)->(out:Result<ProgramReport,ValueError>)
        requires old(self).wf(),program.valid(),cause.is_some() ==> cause.unwrap().wf(),
        ensures out.is_ok() && cause.is_some() && cause.unwrap().journal()==value.journal_spec() ==>
                forall|i:int| 0<=i<out->Ok_0.results().len() ==> (#[trigger] out->Ok_0.registrations()[i]).write().follows(&cause.unwrap()),
            final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && out==Err(ValueError::Closed),
            out.is_err()==!(old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)),
            out.is_ok() ==> out->Ok_0.certified(program.code()) && out->Ok_0.registered()
                && out->Ok_0.observation().source()==value.source() && out->Ok_0.observation().object()==value.object()
                && out->Ok_0.observation().journal_spec()==value.journal_spec()
                && final(self).cleanup_state().queues()[id].slots().len()==old(self).cleanup_state().queues()[id].slots().len()+out->Ok_0.results().len()
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots()
                && forall|i:int| #![trigger out->Ok_0.points()[i]] 0<=i<out->Ok_0.results().len() ==> {
                    let offset=old(self).cleanup_state().queues()[id].slots().len();let slot=final(self).cleanup_state().queues()[id].slots()[offset+i];
                    &&& slot.is_some() && slot.unwrap() is Value
                    &&& out->Ok_0.registrations()[i].records(slot.unwrap()->Value_0,final(self).cleanup_state().queues()[id].link(),
                        final(self).cleanup_state().queues()[id].protocol().domain_id(),(offset+i) as usize)
                    &&& slot.unwrap()->Value_0.target()==*value
                    &&& slot.unwrap()->Value_0.state().before==out->Ok_0.points()[i].state
                    &&& slot.unwrap()->Value_0.state().after==out->Ok_0.points()[i+1].state
                },
            final(self).status_links()==old(self).status_links(),
    {
        if !self.accepts_acquisition(id) {return Err(ValueError::Closed);}
        let ghost prior=*self;
        let ghost managed=joint::local(self.cleanup_state().queues()[id].link(),value.journal_spec());
        let ghost earlier=cause;
        let batch=value.run_following(program,Ghost(managed),Tracked(cause));let ghost all=batch.items@;
        let mut report=batch.report;let mut items=batch.items;let ghost mut i:int=0;
        let ghost mut registrations:Seq<super::registration::Evidence>=Seq::empty();
        let Tracked(mut receipts)=report.receipts;report.receipts=Tracked(Map::tracked_empty());
        let ghost slots=self.cleanup_state().queues()[id].slots();
        while items.len()>0
            invariant earlier.is_some() && earlier.unwrap().journal()==value.journal_spec() ==>
                    forall|j:int| 0<=j<all.len() ==> (#[trigger] all[j]).inverse.origin().follows(&earlier.unwrap()),
                self.status_links()==prior.status_links(),self.wf(),self.value_attempts()==prior.value_attempts(),self.cleanup_state().live(id),report.certified(program.code()),
                self.work_state()==prior.work_state(),self.value_state()==prior.value_state(),self.phase_spec()==prior.phase_spec(),
                self.cleanup_state().queues()[id].link()==prior.cleanup_state().queues()[id].link(),
                self.cleanup_state().queues()[id].protocol().domain_id()==prior.cleanup_state().queues()[id].protocol().domain_id(),
                super::registration::witnesses(receipts),receipts.contains_key((-1,false)),
                receipts[(-1,false)].journal()==report.observation().journal_spec(),receipts[(-1,false)].events()==report.observation().joint_spec().events(),
                forall|j:int| 0<=j<registrations.len() ==> super::registration::recorded_in(receipts,j,#[trigger] registrations[j]),
                registrations.len()==i,managed==joint::local(self.cleanup_state().queues()[id].link(),value.journal_spec()),
                forall|j:int| 0<=j<i ==> (#[trigger] registrations[j]).records(all[j].inverse,self.cleanup_state().queues()[id].link(),
                    self.cleanup_state().queues()[id].protocol().domain_id(),(slots.len()+j) as usize),
                all.len()==report.outcomes.len(),0<=i<=all.len(),items@==all.skip(i as int),
                self.cleanup_state().queues()[id].slots()==slots+all.take(i as int).map(|_:int,a:Applied|Some(ChildCleanup::<Cb,X>::Value(a.inverse))),
                forall|j:int| 0<=j<all.len() ==> all[j].pending_for(managed) && (#[trigger] all[j]).corresponds(value,program.code()[report.points()[j].next.unwrap() as int].operation,program.code()[report.points()[j].next.unwrap() as int].branch)
                    && all[j].inverse.origin().at()==report.joint_positions()[j]
                    && all[j].inverse.state().before==report.points()[j].state && all[j].inverse.state().after==report.points()[j+1].state,
            decreases items.len(),
        {
            let applied=items.pop_front().unwrap();
            let _registered=self.register_inverse(id,applied);
            proof {
                _registered.evidence.borrow().retain(&mut receipts,i);
                registrations=registrations.push(_registered.evidence@);
            }
            proof {
                assert(all.take(i as int).push(all[i as int]) =~= all.take(i as int+1));
                assert(all.skip(i as int).skip(1) =~= all.skip(i as int+1));
            }
            proof {i=i+1;}
        }
        proof {assert((slots+all.map(|_:int,a:Applied|Some(ChildCleanup::<Cb,X>::Value(a.inverse)))).take(slots.len() as int) =~= slots);}
        report.registrations=Ghost(registrations);report.receipts=Tracked(receipts);
        proof {
            assert forall|j:int| 0<=j<report.results().len() implies {
                let evidence=#[trigger] report.registrations()[j];
                &&& evidence.certified() && evidence.write().journal()==report.observation().journal_spec()
                &&& evidence.write().at()==report.joint_positions()[j]
                &&& evidence.write().event().key==report.observation().object().key
                &&& evidence.write().event().change==(joint::Change::Value {event:report.observation().history()[report.offset()+j]})
            } by {
                assert(all[j].corresponds(value,program.code()[report.points()[j].next.unwrap() as int].operation,program.code()[report.points()[j].next.unwrap() as int].branch));
                assert(report.observation().history()[report.offset()+j]==instruction_event(program.code(),report.points(),report.results(),j));
            }
        }
        Ok(report)
    }
}
}
