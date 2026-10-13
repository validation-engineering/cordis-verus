//! Finite, outcome-selected programs over the real shared service value.
//! A program executes under the value's lock; its inverses are returned in
//! execution order to the actual episode owner, which retains every one.
#[cfg(verus_keep_ghost)]
use super::{library, operation};
use super::{
    Applied, Branch, Inverse, Operation, Outcome, ReversibleValue, Snapshot, ValueError, ValueState,
};
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
    fn check(&self,pc:usize,length:usize)->(out:bool) ensures out==self.valid(pc as int,length as nat), {
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
    pub open spec fn root(&self)->Option<usize> {if self.code().len()==0 {None} else {Some(0)}}
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
#[allow(dead_code)]
#[must_use]
pub struct ProgramReport {pub outcomes:Vec<Outcome>,pub error:Option<ValueError>,pub snapshot:Snapshot,points:Ghost<Seq<Point>>}
impl ProgramReport {
    pub closed spec fn points(&self)->Seq<Point> {self.points@}
    pub closed spec fn results(&self)->Seq<Outcome> {self.outcomes@}
    pub closed spec fn observation(&self)->Snapshot {self.snapshot}
    pub closed spec fn certified(&self,code:Seq<Instruction>)->bool {
        &&& prefix(code,self.points(),self.outcomes@)
        &&& self.snapshot.certified() && self.snapshot.state()==self.points().last().state
        &&& if self.error.is_none() {self.points().last().next.is_none()} else {
            self.points().last().next.is_some() && operation(code[self.points().last().next.unwrap() as int].operation)(self.points().last().state).is_none()
        }
    }
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
    pub(crate) closed spec fn certified(&self,program:&Program,value:&ReversibleValue)->bool {
        &&& self.report.certified(program.code())
        &&& self.items@.len()==self.report.outcomes.len()
        &&& forall|i:int| 0<=i<self.items@.len() ==> {
            let pc=self.report.points()[i].next.unwrap();let instruction=program.code()[pc as int];
            &&& (#[trigger] self.items@[i]).corresponds(value,instruction.operation,instruction.branch)
            &&& self.items@[i].outcome==self.report.outcomes@[i]
            &&& self.items@[i].inverse.state().before==self.report.points()[i].state
            &&& self.items@[i].inverse.state().after==self.report.points()[i+1].state
        }
    }
}
impl ReversibleValue {
    pub(crate) fn run(&self,program:&Program)->(out:Batch)
        requires program.valid(),ensures out.certified(program,self),
    {
        let (mut cell,guard)=self.inner.acquire_write();
        let mut current=if program.code.is_empty() {None} else {Some(0usize)};
        let mut items:VecDeque<Applied>=VecDeque::new();let mut outcomes:Vec<Outcome>=Vec::new();let mut error=None;
        let ghost mut points=seq![Point {state:cell.state,next:current}];
        while current.is_some() && error.is_none()
            invariant program.valid(),cell.wf(),cell.initial@==self.initial(),
                error.is_some() ==> current.is_some() && operation(program.code()[current.unwrap() as int].operation)(cell.state).is_none(),
                prefix(program.code(),points,outcomes@),points.last().state==cell.state,points.last().next==current,
                items@.len()==outcomes.len(),
                forall|i:int| 0<=i<items@.len() ==> {
                    let pc=points[i].next.unwrap();let instruction=program.code()[pc as int];
                    &&& (#[trigger] items@[i]).corresponds(self,instruction.operation,instruction.branch)
                    &&& items@[i].outcome==outcomes@[i]
                    &&& items@[i].inverse.state().before==points[i].state
                    &&& items@[i].inverse.state().after==points[i+1].state
                },
            decreases if current.is_some() && error.is_none() {program.code.len()-current.unwrap()+1} else {0},
        {
            let pc=current.unwrap();let instruction=program.code[pc];
            match cell.forward(instruction.operation,instruction.branch) {
                Err(failure)=>{error=Some(failure);},
                Ok(forward)=>{
                    proof {
                        assert(instruction.valid(pc as int,program.code().len()));
                        extend_prefix(program.code(),points,outcomes@,forward.outcome,Point {state:cell.state,next:forward.next});
                        points=points.push(Point {state:cell.state,next:forward.next});
                    }
                    current=forward.next;outcomes.push(forward.outcome);
                    items.push_back(Applied {outcome:forward.outcome,next:forward.next,inverse:Inverse {target:self.clone(),state:forward.inverse}});
                },
            }
        }
        let snapshot=cell.snapshot();guard.release_write(cell);
        Batch {items,report:ProgramReport {outcomes,error,snapshot,points:Ghost(points)}}
    }
}
impl<V,C,G,Cb,X> Execution<V,C,G,ChildCleanup<Cb,X>> {
    /// Admission is checked before any write. The checked interpreter keeps
    /// the value lock for the complete finite program, then this exclusive
    /// owner registers every actual inverse in order before returning.
    #[allow(clippy::len_zero)] // The pinned vstd specifies VecDeque::len, but not is_empty.
    pub fn run_value_program(&mut self,id:usize,value:&ReversibleValue,program:&Program)->(out:Result<ProgramReport,ValueError>)
        requires old(self).wf(),program.valid(),
        ensures final(self).wf(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> out->Ok_0.certified(program.code())
                && final(self).cleanup_state().queues()[id].slots().len()==old(self).cleanup_state().queues()[id].slots().len()+out->Ok_0.results().len()
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots()
                && forall|i:int| #![trigger out->Ok_0.points()[i]] 0<=i<out->Ok_0.results().len() ==> {
                    let offset=old(self).cleanup_state().queues()[id].slots().len();let slot=final(self).cleanup_state().queues()[id].slots()[offset+i];
                    &&& slot.is_some() && slot.unwrap() is Value
                    &&& slot.unwrap()->Value_0.target()==*value
                    &&& slot.unwrap()->Value_0.state().before==out->Ok_0.points()[i].state
                    &&& slot.unwrap()->Value_0.state().after==out->Ok_0.points()[i+1].state
                },
    {
        if !self.accepts_acquisition(id) {return Err(ValueError::Closed);}
        let ghost prior=*self;
        let batch=value.run(program);let ghost all=batch.items@;
        let report=batch.report;let mut items=batch.items;let ghost mut i:int=0;
        let ghost slots=self.cleanup_state().queues()[id].slots();
        while items.len()>0
            invariant self.wf(),self.cleanup_state().live(id),report.certified(program.code()),
                self.work_state()==prior.work_state(),self.value_state()==prior.value_state(),self.phase_spec()==prior.phase_spec(),
                all.len()==report.outcomes.len(),0<=i<=all.len(),items@==all.skip(i as int),
                self.cleanup_state().queues()[id].slots()==slots+all.take(i as int).map(|_:int,a:Applied|Some(ChildCleanup::<Cb,X>::Value(a.inverse))),
                forall|j:int| 0<=j<all.len() ==> (#[trigger] all[j]).corresponds(value,program.code()[report.points()[j].next.unwrap() as int].operation,program.code()[report.points()[j].next.unwrap() as int].branch)
                    && all[j].inverse.state().before==report.points()[j].state && all[j].inverse.state().after==report.points()[j+1].state,
            decreases items.len(),
        {
            let applied=items.pop_front().unwrap();
            let _result=self.register(id,ChildCleanup::Value(applied.inverse));assert(_result.is_ok());
            proof {
                assert(all.take(i as int).push(all[i as int]) =~= all.take(i as int+1));
                assert(all.skip(i as int).skip(1) =~= all.skip(i as int+1));
            }
            proof {i=i+1;}
        }
        proof {assert((slots+all.map(|_:int,a:Applied|Some(ChildCleanup::<Cb,X>::Value(a.inverse)))).take(slots.len() as int) =~= slots);}
        Ok(report)
    }
}
}
