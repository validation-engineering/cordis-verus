//! Checked reversible service values. The actual value, inverse and history
//! share one lock. No plugin callback supplies an expected result or inverse.
//! The history is ghost-only: execution does not retain an unbounded audit log.
#[cfg(verus_keep_ghost)]
use crate::{dependent_grammar as d, mediated as m, Port};
use std::sync::Arc;
use vstd::prelude::*;
use vstd::rwlock::{RwLock, RwLockPredicate};

verus! {

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Operation { Replace(u64), Add(u64), Xor(u64), CompareExchange { expected:u64,value:u64 } }
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Outcome { pub before:u64,pub after:u64,pub matched:bool }
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum ValueError { Closed, Overflow, Capacity, Interference }
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct ValueState {pub value:u64,pub depth:u64}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Branch {pub matched:Option<usize>,pub unmatched:Option<usize>}
impl Branch {
    pub open spec fn selected(&self,outcome:Outcome)->Option<usize> {if outcome.matched {self.matched} else {self.unmatched}}
    pub fn select(&self,outcome:Outcome)->(out:Option<usize>) ensures out==self.selected(outcome), {
        if outcome.matched {self.matched} else {self.unmatched}
    }
}
impl Operation {
    pub open spec fn eval(&self,input:u64)->Option<Outcome> {
        match self {
            Self::Replace(value)=>Some(Outcome {before:input,after:*value,matched:true}),
            Self::Add(value)=>if input as int+*value as int<=u64::MAX {Some(Outcome {before:input,after:(input+*value) as u64,matched:true})} else {None},
            Self::Xor(mask)=>Some(Outcome {before:input,after:input^*mask,matched:true}),
            Self::CompareExchange {expected,value}=>Some(Outcome {before:input,after:if input==*expected {*value} else {input},matched:input==*expected}),
        }
    }
    pub fn evaluate(&self,input:u64)->(out:Result<Outcome,ValueError>)
        ensures out.is_ok()==self.eval(input).is_some(),out.is_ok() ==> Some(out->Ok_0)==self.eval(input),
            out.is_err() ==> out==Err(ValueError::Overflow),
    {
        match self {
            Self::Replace(value)=>Ok(Outcome {before:input,after:*value,matched:true}),
            Self::Add(value)=>match input.checked_add(*value) {
                Some(after)=>Ok(Outcome {before:input,after,matched:true}),None=>Err(ValueError::Overflow),
            },
            Self::Xor(mask)=>Ok(Outcome {before:input,after:input^*mask,matched:true}),
            Self::CompareExchange {expected,value}=>Ok(Outcome {before:input,after:if input==*expected {*value} else {input},matched:input==*expected}),
        }
    }
}

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct InverseState {pub before:ValueState,pub after:ValueState}
impl InverseState {
    pub open spec fn undo(&self,input:ValueState)->Option<ValueState> {if input==self.after {Some(self.before)} else {None}}
}
/// This is the scalar operation used by the R1 dependent grammar, including
/// its strict inverse domain. Depth belongs to the observation, not a hidden
/// precondition on a value-only model.
pub open spec fn operation(op:Operation)->m::Operation<ValueState,Outcome> {
    |input:ValueState| if input.depth==u64::MAX || op.eval(input.value).is_none() {None} else {
        let result=op.eval(input.value).unwrap();
        let after=ValueState {value:result.after,depth:(input.depth+1) as u64};
        Some(m::ValueYield {value:after,outcome:result,undo:|current:ValueState|if current==after {Some(input)} else {None}})
    }
}
pub open spec fn library()->d::Library<Port,(Port,Operation),(),ValueState,Outcome> {
    d::Library {values:|_:Port,_:ValueState|true,arguments:|_:(Port,Operation),_:()|true,
        outcomes:|_:(Port,Operation),_:Outcome|true,key:|a:(Port,Operation)|a.0,allowed:ISet::full(),
        apply:|a:(Port,Operation),_:()|operation(a.1)}
}
pub proof fn primitive_theory()
    ensures d::primitive_theory(|_:Port,a:ValueState,b:ValueState|a==b,library()),
{
    assert forall|a:(Port,Operation),x:()| library().allowed.contains(a) && (library().arguments)(a,x)
        implies d::operation_typed(library(),a,x)
            && m::operation_admissible(|u:ValueState,v:ValueState|u==v,(library().apply)(a,x)) by { }
}

/// Every write and restore, including rejected attempts, has a source class.
pub enum Event {
    Forward {operation:Operation,branch:Branch,before:ValueState,after:ValueState,outcome:Outcome,next:Option<usize>},
    Rejected {operation:Operation,before:ValueState},
    Restore {inverse:InverseState,before:ValueState,after:ValueState},
    Blocked {inverse:InverseState,before:ValueState},
}
impl Event {
    pub open spec fn before(&self)->ValueState {match self {Self::Forward {before,..}|Self::Rejected {before,..}|Self::Restore {before,..}|Self::Blocked {before,..}=>*before}}
    pub open spec fn after(&self)->ValueState {match self {Self::Forward {after,..}|Self::Restore {after,..}=>*after,Self::Rejected {before,..}|Self::Blocked {before,..}=>*before}}
    pub open spec fn valid(&self)->bool {
        match self {
            Self::Forward {operation:op,branch,before,after,outcome,next}=>operation(*op)(*before).is_some()
                && operation(*op)(*before).unwrap().value==*after && operation(*op)(*before).unwrap().outcome==*outcome && *next==branch.selected(*outcome),
            Self::Rejected {operation:op,before}=>operation(*op)(*before).is_none(),
            Self::Restore {inverse,before,after}=>inverse.undo(*before)==Some(*after),
            Self::Blocked {inverse,before}=>inverse.undo(*before).is_none(),
        }
    }
}
pub open spec fn execution(initial:ValueState,events:Seq<Event>,last:ValueState)->bool {
    &&& if events.len()==0 {last==initial} else {events.first().before()==initial && events.last().after()==last}
    &&& forall|i:int| 0<=i<events.len() ==> #[trigger] events[i].valid()
    &&& forall|i:int| 0<=i<events.len()-1 ==> #[trigger] events[i].after()==events[i+1].before()
}
pub proof fn extend(initial:ValueState,events:Seq<Event>,last:ValueState,event:Event)
    requires execution(initial,events,last),event.valid(),event.before()==last,
    ensures execution(initial,events.push(event),event.after()),
{
    assert forall|i:int| 0<=i<events.push(event).len()-1 implies #[trigger] events.push(event)[i].after()==events.push(event)[i+1].before() by {
        if i==events.len()-1 {assert(events[i].after()==last);}
    }
}

/// Actual fields plus a checked source execution ending in those fields.
/// A snapshot is an observation at its lock acquisition, not a promise that a
/// later reader will see the same value.
#[allow(dead_code)]
pub struct Snapshot {state:ValueState,initial:Ghost<ValueState>,history:Ghost<Seq<Event>>}
impl Snapshot {
    pub closed spec fn state(&self)->ValueState {self.state}
    pub closed spec fn initial(&self)->ValueState {self.initial@}
    pub closed spec fn history(&self)->Seq<Event> {self.history@}
    pub closed spec fn certified(&self)->bool {execution(self.initial(),self.history(),self.state())}
    pub fn value(&self)->(out:u64) ensures out==self.state().value, {self.state.value}
    pub fn depth(&self)->(out:u64) ensures out==self.state().depth, {self.state.depth}
}
#[allow(dead_code)]
struct Cell {state:ValueState,initial:Ghost<ValueState>,history:Ghost<Seq<Event>>}
impl Cell {
    spec fn wf(&self)->bool {execution(self.initial@,self.history@,self.state)}
    fn snapshot(&self)->(out:Snapshot)
        requires self.wf(),ensures out.certified(),out.state()==self.state,out.history()==self.history@,out.initial()==self.initial@,
    {Snapshot {state:self.state,initial:self.initial,history:self.history}}
    proof fn record(tracked &mut self,before:ValueState,event:Event)
        requires execution(old(self).initial@,old(self).history@,before),event.valid(),event.before()==before,event.after()==old(self).state,
        ensures final(self).wf(),final(self).state==old(self).state,final(self).initial==old(self).initial,final(self).history@==old(self).history@.push(event),
    {
        extend(self.initial@,self.history@,before,event);
        self.history=Ghost(self.history@.push(event));
    }
}
#[allow(dead_code)] // Read only by the erased lock predicate.
struct Forward {outcome:Outcome,next:Option<usize>,inverse:InverseState}
impl Forward {
    spec fn corresponds(&self,op:Operation,branch:Branch)->bool {
        &&& operation(op)(self.inverse.before).is_some()
        &&& operation(op)(self.inverse.before).unwrap().value==self.inverse.after
        &&& operation(op)(self.inverse.before).unwrap().outcome==self.outcome
        &&& self.next==branch.selected(self.outcome)
        &&& forall|input:ValueState| #[trigger] self.inverse.undo(input)==(operation(op)(self.inverse.before).unwrap().undo)(input)
    }
}
impl Cell {
    fn forward(&mut self,op:Operation,branch:Branch)->(out:Result<Forward,ValueError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).initial==old(self).initial,
            out.is_ok()==operation(op)(old(self).state).is_some(),
            out.is_ok() ==> out->Ok_0.corresponds(op,branch) && out->Ok_0.inverse.before==old(self).state && out->Ok_0.inverse.after==final(self).state,
            out.is_err() ==> final(self).state==old(self).state && (out==Err(ValueError::Capacity) || out==Err(ValueError::Overflow)),
    {
        let before=self.state;
        if before.depth==u64::MAX {
            proof {self.record(before,Event::Rejected {operation:op,before});}
            return Err(ValueError::Capacity);
        }
        let outcome=match op.evaluate(before.value) {
            Ok(outcome)=>outcome,
            Err(error)=>{
                proof {self.record(before,Event::Rejected {operation:op,before});}
                return Err(error);
            },
        };
        let after=ValueState {value:outcome.after,depth:before.depth+1};let next=branch.select(outcome);
        self.state=after;
        proof {self.record(before,Event::Forward {operation:op,branch,before,after,outcome,next});}
        Ok(Forward {outcome,next,inverse:InverseState {before,after}})
    }
}

#[allow(dead_code)] // Read only by the erased lock predicate.
struct Predicate {initial:ValueState}
impl RwLockPredicate<Cell> for Predicate {
    closed spec fn inv(self,cell:Cell)->bool {cell.wf() && cell.initial@==self.initial}
}

/// A shareable service with no unguarded setter and no mutable inner reference.
/// Keep this value in a declared Cordis service; managed calls store its real
/// inverse in the episode cleanup owner before returning to the plugin.
pub struct ReversibleValue {inner:Arc<RwLock<Cell,Predicate>>}
impl Clone for ReversibleValue {
    fn clone(&self)->(out:Self) ensures out==*self, {Self {inner:self.inner.clone()}}
}
/// Linear and tied to its original shared value. No constructor, Clone, target
/// parameter or mutable payload lets a plugin substitute another restoration.
pub struct Inverse {target:ReversibleValue,state:InverseState}
impl Inverse {
    pub closed spec fn target(&self)->ReversibleValue {self.target}
    pub closed spec fn state(&self)->InverseState {self.state}
    /// A failed attempt retains the exact inverse; success consumes it.
    pub fn restore(self)->(out:Result<Snapshot,Self>)
        ensures out.is_ok() ==> out->Ok_0.certified() && out->Ok_0.state()==self.state().before,
            out.is_err() ==> out->Err_0==self,
    {
        let (mut cell,guard)=self.target.inner.acquire_write();
        let before=cell.state;
        if before!=self.state.after {
            proof {cell.record(before,Event::Blocked {inverse:self.state,before});}
            guard.release_write(cell);return Err(self);
        }
        cell.state=self.state.before;
        proof {cell.record(before,Event::Restore {inverse:self.state,before,after:cell.state});}
        let snapshot=cell.snapshot();guard.release_write(cell);Ok(snapshot)
    }
}
pub struct Applied {pub outcome:Outcome,pub next:Option<usize>,pub inverse:Inverse}
impl Applied {
    pub open spec fn corresponds(&self,target:&ReversibleValue,op:Operation,branch:Branch)->bool {
        &&& self.inverse.target()==*target
        &&& operation(op)(self.inverse.state().before).is_some()
        &&& operation(op)(self.inverse.state().before).unwrap().value==self.inverse.state().after
        &&& operation(op)(self.inverse.state().before).unwrap().outcome==self.outcome
        &&& self.next==branch.selected(self.outcome)
        &&& forall|input:ValueState| #[trigger] self.inverse.state().undo(input)==(operation(op)(self.inverse.state().before).unwrap().undo)(input)
    }
}
impl ReversibleValue {
    pub closed spec fn initial(&self)->ValueState {self.inner.pred().initial}
    pub fn new(value:u64)->(out:Self)
        ensures out.initial()==(ValueState {value,depth:0}),
    {
        let state=ValueState {value,depth:0};
        Self {inner:Arc::new(RwLock::new(Cell {state,initial:Ghost(state),history:Ghost(Seq::empty())},Ghost(Predicate {initial:state})))}
    }
    pub fn snapshot(&self)->(out:Snapshot) ensures out.certified(),out.initial()==self.initial(), {
        let guard=self.inner.acquire_read();let out=guard.borrow().snapshot();guard.release_read();out
    }
    /// Execute the actual operation and select from its actual result while
    /// retaining its actual inverse. There is no expected-result argument.
    pub fn apply(&self,op:Operation,branch:Branch)->(out:Result<Applied,ValueError>)
        ensures out.is_ok() ==> out->Ok_0.corresponds(self,op,branch),
            out.is_err() ==> out==Err(ValueError::Capacity) || out==Err(ValueError::Overflow),
    {
        let (mut cell,guard)=self.inner.acquire_write();
        let result=cell.forward(op,branch);
        guard.release_write(cell);
        match result {
            Ok(forward)=>Ok(Applied {outcome:forward.outcome,next:forward.next,inverse:Inverse {target:self.clone(),state:forward.inverse}}),
            Err(error)=>Err(error),
        }
    }
}

/// Interpret every successful production write as an R1 dependent-grammar
/// operation at the chosen declared key. Other service entries are framed.
pub proof fn forward_interpretation(event:Event,key:Port,table:Map<Port,ValueState>)
    requires event.valid(),event is Forward,table.contains_key(key),table[key]==event.before(),
    ensures {
        let op=event->Forward_operation;let branch=event->Forward_branch;
        let node=d::Node::Operation {operation:(key,op),argument:(),select:|out:Outcome|branch.selected(out)};
        let result=d::run(library(),node,table);
        &&& result.is_some() && result.unwrap().state==table.insert(key,event.after()) && result.unwrap().next==event->Forward_next
        &&& forall|test:Map<Port,ValueState>| #[trigger] (result.unwrap().undo)(test)==
            if test.contains_key(key) && test[key]==event.after() {Some(test.insert(key,event.before()))} else {None}
    },
{ }
/// Whole history correspondence, not a collection of unconnected method labels.
/// Rejected calls stutter; restoration uses the same strict returned function.
pub proof fn history_interpretation(snapshot:Snapshot,key:Port,table:Map<Port,ValueState>)
    requires snapshot.certified(),table.contains_key(key),table[key]==snapshot.initial(),
    ensures forall|i:int| #![trigger snapshot.history()[i]] 0<=i<snapshot.history().len() ==> {
        let event=snapshot.history()[i];let before=table.insert(key,event.before());let after=table.insert(key,event.after());
        &&& event.valid()
        &&& ((event is Rejected || event is Blocked) ==> before==after)
        &&& (event is Forward ==> d::run(library(),d::Node::Operation {operation:(key,event->Forward_operation),argument:(),
            select:|out:Outcome|event->Forward_branch.selected(out)},before).unwrap().state==after)
        &&& (event is Restore ==> d::inverse(key,|v:ValueState|event->Restore_inverse.undo(v))(before)==Some(after))
    },
{
    assert forall|i:int| #![trigger snapshot.history()[i]] 0<=i<snapshot.history().len() implies {
        let event=snapshot.history()[i];let before=table.insert(key,event.before());let after=table.insert(key,event.after());
        &&& event.valid()
        &&& ((event is Rejected || event is Blocked) ==> before==after)
        &&& (event is Forward ==> d::run(library(),d::Node::Operation {operation:(key,event->Forward_operation),argument:(),
            select:|out:Outcome|event->Forward_branch.selected(out)},before).unwrap().state==after)
        &&& (event is Restore ==> d::inverse(key,|v:ValueState|event->Restore_inverse.undo(v))(before)==Some(after))
    } by {
        let event=snapshot.history()[i];
        assert(event.valid());
        if event is Forward {forward_interpretation(event,key,table.insert(key,event.before()));}
        if event is Forward || event is Restore {
            assert(table.insert(key,event.before()).insert(key,event.after()) =~= table.insert(key,event.after()));
        }
    }
}
}

#[path = "value_program.rs"]
pub mod program;
