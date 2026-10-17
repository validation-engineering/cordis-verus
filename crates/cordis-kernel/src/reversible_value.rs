//! Checked reversible service values. The actual value, inverse and history
//! share one lock. No plugin callback supplies an expected result or inverse.
//! The history is ghost-only: execution does not retain an unbounded audit log.
#[cfg(verus_keep_ghost)]
use crate::{dependent_grammar as d, mediated as m, Port};
use std::sync::Arc;
use vstd::prelude::*;
use vstd::resource::Loc;
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
    Computed {code:effect::Code,branch:Branch,before:ValueState,after:ValueState,outcome:Outcome,next:Option<usize>},
    ComputationRejected {code:effect::Code,before:ValueState},
    StaleComputation {expected:ValueState,before:ValueState},
}
impl Event {
    pub open spec fn before(&self)->ValueState {match self {Self::Forward {before,..}|Self::Rejected {before,..}|Self::Restore {before,..}|Self::Blocked {before,..}|Self::Computed {before,..}|Self::ComputationRejected {before,..}|Self::StaleComputation {before,..}=>*before}}
    pub open spec fn after(&self)->ValueState {match self {Self::Forward {after,..}|Self::Restore {after,..}|Self::Computed {after,..}=>*after,Self::Rejected {before,..}|Self::Blocked {before,..}|Self::ComputationRejected {before,..}|Self::StaleComputation {before,..}=>*before}}
    pub open spec fn valid(&self)->bool {
        match self {
            Self::Forward {operation:op,branch,before,after,outcome,next}=>operation(*op)(*before).is_some()
                && operation(*op)(*before).unwrap().value==*after && operation(*op)(*before).unwrap().outcome==*outcome && *next==branch.selected(*outcome),
            Self::Rejected {operation:op,before}=>operation(*op)(*before).is_none(),
            Self::Restore {inverse,before,after}=>inverse.undo(*before)==Some(*after),
            Self::Blocked {inverse,before}=>inverse.undo(*before).is_none(),
            Self::Computed {code,branch,before,after,outcome,next}=>effect::operation(*code)(*before).is_some()
                && effect::operation(*code)(*before).unwrap().value==*after && effect::operation(*code)(*before).unwrap().outcome==*outcome && *next==branch.selected(*outcome),
            Self::ComputationRejected {code,before}=>effect::operation(*code)(*before).is_none(),
            Self::StaleComputation {expected,before}=>expected!=before,
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
pub struct Snapshot {
    state:ValueState,initial:Ghost<ValueState>,history:Ghost<Seq<Event>>,
    witness:Tracked<history::Witness<Event>>,joint:joint::Snapshot,key:Ghost<nat>,positions:Ghost<Seq<nat>>,
}
impl Snapshot {
    pub closed spec fn state(&self)->ValueState {self.state}
    pub closed spec fn initial(&self)->ValueState {self.initial@}
    pub closed spec fn history(&self)->Seq<Event> {self.history@}
    pub closed spec fn source(&self)->Loc {self.witness@.source()}
    pub closed spec fn positions(&self)->Seq<nat> {self.positions@}
    pub closed spec fn object(&self)->joint::Object {joint::Object {domain:self.joint.domain(),key:self.key@}}
    pub closed spec fn journal_spec(&self)->joint::Journal {self.joint.journal_spec()}
    pub fn joint_execution(&self)->(out:&joint::Snapshot) ensures *out==self.joint_spec(), {&self.joint}
    pub closed spec fn joint_spec(&self)->joint::Snapshot {self.joint}
    pub closed spec fn certified(&self)->bool {
        execution(self.initial(),self.history(),self.state()) && self.witness@.wf() && self.witness@.events()==self.history()
            && self.joint.certified() && self.joint.last().contains_key(self.key@)
            && self.joint.last()[self.key@]==(joint::Record::Object {source:self.source(),state:self.state()})
            && joint::indexed(self.history(),self.positions(),self.joint.events(),self.key@)
    }
    pub open spec fn extends(&self,earlier:&Self)->bool {
        self.source()==earlier.source() && self.initial()==earlier.initial() && self.object()==earlier.object() && self.joint_spec().extends(&earlier.joint_spec())
            && earlier.history().len()<=self.history().len()
            && self.history().take(earlier.history().len() as int)==earlier.history()
    }
    pub proof fn reflexive(&self)
        ensures self.extends(self),
    {assert(self.history().take(self.history().len() as int) =~= self.history());assert(self.joint.events().take(self.joint.events().len() as int) =~= self.joint.events());}
    pub proof fn execution(&self)
        requires self.certified(),
        ensures execution(self.initial(),self.history(),self.state()),
    {}
    pub proof fn projection(&self)
        requires self.certified(),
        ensures joint::indexed(self.history(),self.positions(),self.joint_spec().events(),self.object().key),
    {}
    pub proof fn production_state(&self)
        requires self.certified(),
        ensures self.joint_spec().certified(),self.joint_spec().last().contains_key(self.object().key),
            self.joint_spec().last()[self.object().key]==(joint::Record::Object {source:self.source(),state:self.state()}),
    {}
    pub fn value(&self)->(out:u64) ensures out==self.state().value, {self.state.value}
    pub fn depth(&self)->(out:u64) ensures out==self.state().depth, {self.state.depth}
}
#[allow(dead_code)]
struct Cell {
    state:ValueState,initial:Ghost<ValueState>,history:Ghost<Seq<Event>>,
    authority:Tracked<history::Authority<Event>>,joint:joint::Member,positions:Ghost<Seq<nat>>,
}
impl Cell {
    spec fn wf(&self)->bool {
        execution(self.initial@,self.history@,self.state) && self.authority@.wf() && self.authority@.events()==self.history@ && self.joint.wf()
            && self.joint.record()==(joint::Record::Object {source:self.authority@.source(),state:self.state})
            && joint::indexed(self.history@,self.positions@,self.joint.events(),self.joint.key())
    }
    fn snapshot(&self)->(out:Snapshot)
        requires self.wf(),ensures out.certified(),out.state()==self.state,out.history()==self.history@,out.initial()==self.initial@,
            out.source()==self.authority@.source(),out.object()==self.joint.object(),out.journal_spec()==self.joint.journal(),out.positions()==self.positions@,
    {
        let tracked witness=self.authority.borrow().snapshot();
        let joint=self.joint.observe();
        proof {joint::extend_indexed(self.history@,self.positions@,self.joint.events(),joint.events(),self.joint.key());}
        Snapshot {state:self.state,initial:self.initial,history:self.history,witness:Tracked(witness),joint,key:Ghost(self.joint.key()),positions:self.positions}
    }
    fn snapshot_following(&self,Tracked(earlier):Tracked<&joint::Receipt>)->(out:Snapshot)
        requires self.wf(),earlier.wf(),
        ensures earlier.journal()==self.joint.journal() ==> earlier.events().len()<=out.joint_spec().events().len()
                && out.joint_spec().events().take(earlier.events().len() as int)==earlier.events(),
            out.certified(),out.state()==self.state,out.history()==self.history@,out.initial()==self.initial@,
            out.source()==self.authority@.source(),out.object()==self.joint.object(),out.journal_spec()==self.joint.journal(),out.positions()==self.positions@,
    {
        let tracked witness=self.authority.borrow().snapshot();
        let joint=self.joint.observe_following(Tracked(earlier));
        proof {joint::extend_indexed(self.history@,self.positions@,self.joint.events(),joint.events(),self.joint.key());}
        Snapshot {state:self.state,initial:self.initial,history:self.history,witness:Tracked(witness),joint,key:Ghost(self.joint.key()),positions:self.positions}
    }
    fn snapshot_after(&self,earlier:&Snapshot)->(out:Snapshot)
        requires self.wf(),earlier.certified(),earlier.source()==self.authority@.source(),earlier.initial()==self.initial@,
            earlier.object()==self.joint.object(),earlier.journal_spec()==self.joint.journal(),
        ensures out.certified(),out.extends(earlier),out.state()==self.state,out.history()==self.history@,
            out.initial()==self.initial@,out.source()==self.authority@.source(),out.object()==self.joint.object(),out.journal_spec()==self.joint.journal(),out.positions()==self.positions@,
    {
        proof {self.extends(earlier);}
        let tracked witness=self.authority.borrow().snapshot();
        let joint=self.joint.observe_after(&earlier.joint);
        proof {joint::extend_indexed(self.history@,self.positions@,self.joint.events(),joint.events(),self.joint.key());}
        Snapshot {state:self.state,initial:self.initial,history:self.history,witness:Tracked(witness),joint,key:Ghost(self.joint.key()),positions:self.positions}
    }
    proof fn extends(tracked &self,tracked earlier:&Snapshot)
        requires self.wf(),earlier.certified(),earlier.source()==self.authority@.source(),
        ensures earlier.history().len()<=self.history@.len(),self.history@.take(earlier.history().len() as int)==earlier.history(),
    {self.authority.borrow().extends(earlier.witness.borrow());}
    fn record_following(&mut self,Ghost(before):Ghost<ValueState>,Ghost(event):Ghost<Event>,Ghost(managed):Ghost<bool>,Tracked(cause):Tracked<Option<joint::Receipt>>)->(out:Tracked<Option<joint::Pending>>)
        requires cause.is_some() ==> cause.unwrap().wf(),
            managed ==> event is Forward || event is Computed,
            execution(old(self).initial@,old(self).history@,before),old(self).authority@.wf(),old(self).authority@.events()==old(self).history@,old(self).joint.wf(),
            joint::indexed(old(self).history@,old(self).positions@,old(self).joint.events(),old(self).joint.key()),
            old(self).joint.record()==(joint::Record::Object {source:old(self).authority@.source(),state:before}),event.valid(),event.before()==before,event.after()==old(self).state,
        ensures cause.is_some() && cause.unwrap().journal()==old(self).joint.journal() ==>
                cause.unwrap().events().len()<final(self).joint.events().len() && final(self).joint.events().take(cause.unwrap().events().len() as int)==cause.unwrap().events(),
            joint::pending_matches(out@,final(self).joint.journal(),final(self).joint.key(),(final(self).joint.events().len()-1) as nat,managed),
            final(self).wf(),final(self).state==old(self).state,final(self).initial==old(self).initial,final(self).history@==old(self).history@.push(event),
            final(self).history@.take(old(self).history@.len() as int)==old(self).history@,final(self).authority@.source()==old(self).authority@.source(),
            final(self).joint.journal()==old(self).joint.journal(),final(self).joint.key()==old(self).joint.key(),
            final(self).joint.events().last().event.change==(joint::Change::Value {event}),
            final(self).positions@==old(self).positions@.push((final(self).joint.events().len()-1) as nat),
            final(self).positions@.take(old(self).positions@.len() as int)==old(self).positions@,
    {
        let ghost events=self.history@;let ghost frames=self.joint.events();
        proof {
        extend(self.initial@,self.history@,before,event);
        assert(self.history@.push(event).take(self.history@.len() as int) =~= self.history@);
        self.authority.borrow_mut().append(event);
        self.history=Ghost(self.history@.push(event));
        }
        proof {reveal(joint::changes);}
        let pending=self.joint.update_following(Ghost(joint::Record::Object {source:self.authority@.source(),state:self.state}),Ghost(joint::Change::Value {event}),Tracked(cause),Ghost(managed),Tracked(None));
        proof {
            joint::append_indexed(events,self.positions@,frames,self.joint.events(),self.joint.key(),event);
            let prior=self.positions@;
            self.positions=Ghost(self.positions@.push((self.joint.events().len()-1) as nat));
            assert(self.positions@.take(prior.len() as int) =~= prior);
        }
        pending
    }
}
#[allow(dead_code)] // Read only by the erased lock predicate.
struct Forward {outcome:Outcome,next:Option<usize>,inverse:InverseState,pending:Tracked<Option<joint::Pending>>}
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
    fn forward(&mut self,op:Operation,branch:Branch,Ghost(managed):Ghost<bool>)->(out:Result<Forward,ValueError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).initial==old(self).initial,final(self).authority@.source()==old(self).authority@.source(),
            final(self).joint.journal()==old(self).joint.journal(),final(self).joint.key()==old(self).joint.key(),
            final(self).joint.events().last().event.change==(joint::Change::Value {event:final(self).history@.last()}),
            final(self).positions@.last()==final(self).joint.events().len()-1,
            final(self).positions@.take(old(self).positions@.len() as int)==old(self).positions@,
            final(self).history@.len()==old(self).history@.len()+1,
            final(self).history@.take(old(self).history@.len() as int)==old(self).history@,
            out.is_ok() ==> final(self).history@.last()==(Event::Forward {operation:op,branch,before:old(self).state,after:final(self).state,outcome:out->Ok_0.outcome,next:out->Ok_0.next}),
            out.is_err() ==> final(self).history@.last()==(Event::Rejected {operation:op,before:old(self).state}),
            out.is_ok()==operation(op)(old(self).state).is_some(),
            out.is_ok() ==> joint::pending_matches (out->Ok_0.pending@,final(self).joint.journal(),final(self).joint.key(),(final(self).joint.events().len()-1) as nat,managed),
            out.is_ok() ==> out->Ok_0.corresponds(op,branch) && out->Ok_0.inverse.before==old(self).state && out->Ok_0.inverse.after==final(self).state,
            out.is_err() ==> final(self).state==old(self).state && (out==Err(ValueError::Capacity) || out==Err(ValueError::Overflow)),
            out.is_err() ==> attempt::value_rejection (final(self).history@.last(),op,out->Err_0),
    {self.forward_following(op,branch,Ghost(managed),Tracked(None))}
    fn forward_following(&mut self,op:Operation,branch:Branch,Ghost(managed):Ghost<bool>,Tracked(cause):Tracked<Option<joint::Receipt>>)->(out:Result<Forward,ValueError>)
        requires old(self).wf(),cause.is_some() ==> cause.unwrap().wf(),
        ensures cause.is_some() && cause.unwrap().journal()==old(self).joint.journal() ==>
                cause.unwrap().events().len()<final(self).joint.events().len() && final(self).joint.events().take(cause.unwrap().events().len() as int)==cause.unwrap().events(),
            final(self).wf(),final(self).initial==old(self).initial,final(self).authority@.source()==old(self).authority@.source(),
            final(self).joint.journal()==old(self).joint.journal(),final(self).joint.key()==old(self).joint.key(),
            final(self).joint.events().last().event.change==(joint::Change::Value {event:final(self).history@.last()}),
            final(self).positions@.last()==final(self).joint.events().len()-1,
            final(self).positions@.take(old(self).positions@.len() as int)==old(self).positions@,
            final(self).history@.len()==old(self).history@.len()+1,
            final(self).history@.take(old(self).history@.len() as int)==old(self).history@,
            out.is_ok() ==> final(self).history@.last()==(Event::Forward {operation:op,branch,before:old(self).state,after:final(self).state,outcome:out->Ok_0.outcome,next:out->Ok_0.next}),
            out.is_err() ==> final(self).history@.last()==(Event::Rejected {operation:op,before:old(self).state}),
            out.is_ok()==operation(op)(old(self).state).is_some(),
            out.is_ok() ==> joint::pending_matches(out->Ok_0.pending@,final(self).joint.journal(),final(self).joint.key(),(final(self).joint.events().len()-1) as nat,managed),
            out.is_ok() ==> out->Ok_0.corresponds(op,branch) && out->Ok_0.inverse.before==old(self).state && out->Ok_0.inverse.after==final(self).state,
            out.is_err() ==> final(self).state==old(self).state && (out==Err(ValueError::Capacity) || out==Err(ValueError::Overflow)),
            out.is_err() ==> attempt::value_rejection(final(self).history@.last(),op,out->Err_0),
    {
        let before=self.state;
        if before.depth==u64::MAX {
            let _pending=self.record_following(Ghost(before),Ghost(Event::Rejected {operation:op,before}),Ghost(false),Tracked(cause));
            return Err(ValueError::Capacity);
        }
        let outcome=match op.evaluate(before.value) {
            Ok(outcome)=>outcome,
            Err(error)=>{
                let _pending=self.record_following(Ghost(before),Ghost(Event::Rejected {operation:op,before}),Ghost(false),Tracked(cause));
                return Err(error);
            },
        };
        let after=ValueState {value:outcome.after,depth:before.depth+1};let next=branch.select(outcome);
        self.state=after;
        let pending=self.record_following(Ghost(before),Ghost(Event::Forward {operation:op,branch,before,after,outcome,next}),Ghost(managed),Tracked(cause));
        Ok(Forward {outcome,next,inverse:InverseState {before,after},pending})
    }
}

#[allow(dead_code)] // Read only by the erased lock predicate.
struct Predicate {initial:ValueState,source:Loc,journal:joint::Journal,key:nat}
impl RwLockPredicate<Cell> for Predicate {
    closed spec fn inv(self,cell:Cell)->bool {cell.wf() && cell.initial@==self.initial && cell.authority@.source()==self.source && cell.joint.journal()==self.journal && cell.joint.key()==self.key}
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
pub struct Inverse {target:ReversibleValue,state:InverseState,#[allow(dead_code)] origin:Tracked<joint::Receipt>}
impl Inverse {
    pub closed spec fn target(&self)->ReversibleValue {self.target}
    pub closed spec fn state(&self)->InverseState {self.state}
    pub closed spec fn origin(&self)->joint::Receipt {self.origin@}
    pub open spec fn recorded(&self)->bool {
        self.origin().wf() && self.origin().journal()==self.target().journal_spec()
            && self.origin().event().key==self.target().object().key
            && match self.origin().event().change {joint::Change::Value {event}=>
                (event is Forward || event is Computed) && event.valid()
                    && event.before()==self.state().before && event.after()==self.state().after,_=>false}
    }
    /// A failed attempt retains the exact inverse; success consumes it.
    pub fn restore(self)->(out:Result<Snapshot,Self>)
        ensures out.is_ok() ==> out->Ok_0.certified() && out->Ok_0.state()==self.state().before && out->Ok_0.source()==self.target().source(),
            out.is_err() ==> out->Err_0==self,
    {self.restore_following(Tracked(None)).0}
    /// The returned receipt comes from the actual guarded restore attempt,
    /// including a blocked attempt. Same-domain dispatch precedes this commit.
    pub(crate) fn restore_following(self,Tracked(cause):Tracked<Option<joint::Receipt>>)
        ->(out:(Result<Snapshot,Self>,Tracked<joint::Receipt>))
        requires cause.is_some() ==> cause.unwrap().wf(),
        ensures restoration::attempted(&out.1@,self,out.0.is_ok()),
            cause.is_some() && cause.unwrap().journal()==self.target().journal_spec() ==> out.1@.follows(&cause.unwrap()),
            out.0.is_ok() ==> out.0->Ok_0.certified() && out.0->Ok_0.state()==self.state().before
                && out.0->Ok_0.source()==self.target().source() && out.0->Ok_0.object()==self.target().object()
                && out.0->Ok_0.journal_spec()==self.target().journal_spec()
                && out.0->Ok_0.history().last()==out.1@.event().change->Value_event
                && out.0->Ok_0.positions().last()==out.1@.at(),
            out.0.is_err() ==> out.0->Err_0==self,
    {
        let (mut cell,guard)=self.target.inner.acquire_write();
        let before=cell.state;
        if before!=self.state.after {
            let _pending=cell.record_following(Ghost(before),Ghost(Event::Blocked {inverse:self.state,before}),Ghost(false),Tracked(cause));
            let tracked receipt=cell.joint.receipt();
            guard.release_write(cell);return (Err(self),Tracked(receipt));
        }
        cell.state=self.state.before;
        let _pending=cell.record_following(Ghost(before),Ghost(Event::Restore {inverse:self.state,before,after:cell.state}),Ghost(false),Tracked(cause));
        let tracked receipt=cell.joint.receipt();
        let snapshot=cell.snapshot();guard.release_write(cell);(Ok(snapshot),Tracked(receipt))
    }

}
pub struct Applied {pub outcome:Outcome,pub next:Option<usize>,#[allow(dead_code)] pub pending:Tracked<Option<joint::Pending>>,pub inverse:Inverse}
impl Applied {
    pub open spec fn pending_for(&self,enabled:bool)->bool {
        joint::pending_matches(self.pending@,self.inverse.target().journal_spec(),self.inverse.target().object().key,self.inverse.origin().at(),enabled)
    }
    pub open spec fn corresponds(&self,target:&ReversibleValue,op:Operation,branch:Branch)->bool {
        &&& self.inverse.recorded()
        &&& self.inverse.origin().event().change==(joint::Change::Value {event:Event::Forward {operation:op,branch,
            before:self.inverse.state().before,after:self.inverse.state().after,outcome:self.outcome,next:self.next}})
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
    pub closed spec fn source(&self)->Loc {self.inner.pred().source}
    pub fn new(value:u64)->(out:Self)
        ensures out.initial()==(ValueState {value,depth:0}),
    {
        Self::new_in(&joint::Journal::new(),value)
    }
    pub closed spec fn journal_spec(&self)->joint::Journal {self.inner.pred().journal}
    pub closed spec fn object(&self)->joint::Object {joint::Object {domain:self.journal_spec().source(),key:self.inner.pred().key}}
    pub fn journal(&self)->(out:joint::Journal) ensures out==self.journal_spec(), {
        let (journal,_receipt)=self.reference();journal
    }
    /// Collect a persistent object receipt before acquiring any slot or Journal
    /// lock. It proves allocation identity, not a frozen object value.
    pub(crate) fn reference(&self)->(out:(joint::Journal,Tracked<joint::Receipt>))
        ensures out.0==self.journal_spec(),out.1@.wf(),out.1@.journal()==self.journal_spec(),
            out.1@.event().key==self.object().key,out.1@.event().after is Object,
            out.1@.event().after->Object_source==self.source(),
    {
        let guard=self.inner.acquire_read();let cell=guard.borrow();
        let journal=cell.joint.domain();let tracked receipt=cell.joint.receipt();
        guard.release_read();(journal,Tracked(receipt))
    }
    /// Allocate directly in the lifecycle's execution domain. Registration and
    /// every later mutation use the same real journal lock.
    pub fn new_in(journal:&joint::Journal,value:u64)->(out:Self)
        ensures out.initial()==(ValueState {value,depth:0}),out.journal_spec()==*journal,
    {
        let state=ValueState {value,depth:0};
        let tracked authority=history::Authority::new();
        let ghost source=authority.source();
        let joint=journal.allocate(Ghost(joint::Record::Object {source,state}));
        let ghost key=joint.key();
        Self {inner:Arc::new(RwLock::new(Cell {state,initial:Ghost(state),history:Ghost(Seq::empty()),authority:Tracked(authority),joint,positions:Ghost(Seq::empty())},
            Ghost(Predicate {initial:state,source,journal:*journal,key})))}
    }
    /// Observe the actual value and its domain trace while holding the value
    /// read lock. The trace's heap entry is proved equal to this snapshot.
    pub fn observe_execution(&self)->(out:(Snapshot,joint::Snapshot))
        ensures out.0.certified(),out.0.source()==self.source(),out.1.certified(),
            out.1.domain()==self.object().domain,out.1.resolve(self.object())==Some(out.0.state()),
    {
        let guard=self.inner.acquire_read();let cell=guard.borrow();
        let snapshot=cell.snapshot();let joint=cell.joint.observe();
        guard.release_read();(snapshot,joint)
    }
    pub(crate) fn snapshot_following(&self,Tracked(earlier):Tracked<&joint::Receipt>)->(out:Snapshot)
        requires earlier.wf(),
        ensures out.certified(),out.initial()==self.initial(),out.source()==self.source(),out.object()==self.object(),out.journal_spec()==self.journal_spec(),
            earlier.journal()==self.journal_spec() ==> earlier.events().len()<=out.joint_spec().events().len()
                && out.joint_spec().events().take(earlier.events().len() as int)==earlier.events(),
    {let guard=self.inner.acquire_read();let out=guard.borrow().snapshot_following(Tracked(earlier));guard.release_read();out}
    pub fn snapshot(&self)->(out:Snapshot) ensures out.certified(),out.initial()==self.initial(),out.source()==self.source(),out.object()==self.object(),out.journal_spec()==self.journal_spec(), {
        let guard=self.inner.acquire_read();let out=guard.borrow().snapshot();guard.release_read();out
    }
    /// Observe the real shared history after a retained checkpoint, including
    /// other callers' writes and blocked/successful cleanup attempts.
    fn snapshot_after(&self,_earlier:&Snapshot)->(out:Snapshot)
        requires _earlier.certified(),_earlier.source()==self.source(),_earlier.initial()==self.initial(),_earlier.object()==self.object(),_earlier.journal_spec()==self.journal_spec(),
        ensures out.certified(),out.extends(_earlier),out.initial()==self.initial(),out.source()==self.source(),out.object()==self.object(),out.journal_spec()==self.journal_spec(),
    {
        let guard=self.inner.acquire_read();let cell=guard.borrow();
        proof {cell.extends(_earlier);}
        let out=cell.snapshot_after(_earlier);guard.release_read();out
    }
    /// Execute the actual operation and select from its actual result while
    /// retaining its actual inverse. There is no expected-result argument.
    pub fn apply(&self,op:Operation,branch:Branch)->(out:Result<Applied,ValueError>)
        ensures out.is_ok() ==> out->Ok_0.corresponds(self,op,branch),
            out.is_err() ==> out==Err(ValueError::Capacity) || out==Err(ValueError::Overflow),
    {let tracked mut attempts=attempt::Ledger::new();self.apply_pending(op,branch,Ghost(false),Tracked(&mut attempts))}
    pub(crate) fn apply_pending(&self,op:Operation,branch:Branch,Ghost(managed):Ghost<bool>,Tracked(attempts):Tracked<&mut attempt::Ledger>)->(out:Result<Applied,ValueError>)
        requires old(attempts).wf(),
        ensures final(attempts).appended(old(attempts),self),
            out.is_ok() ==> final(attempts).records(out->Ok_0.inverse),
            out.is_err() ==> attempt::value_rejection(final(attempts).event(),op,out->Err_0), out.is_ok() ==> out->Ok_0.corresponds(self,op,branch) && out->Ok_0.pending_for(managed),
            out.is_err() ==> out==Err(ValueError::Capacity) || out==Err(ValueError::Overflow),
    {self.apply_pending_following(op,branch,Ghost(managed),Tracked(attempts),Tracked(None))}
    pub(crate) fn apply_pending_following(&self,op:Operation,branch:Branch,Ghost(managed):Ghost<bool>,Tracked(attempts):Tracked<&mut attempt::Ledger>,Tracked(cause):Tracked<Option<joint::Receipt>>)->(out:Result<Applied,ValueError>)
        requires old(attempts).wf(),cause.is_some() ==> cause.unwrap().wf(),
        ensures cause.is_some() && cause.unwrap().journal()==self.journal_spec() ==> final(attempts).events().last().follows(&cause.unwrap()),
            final(attempts).appended(old(attempts),self),
            out.is_ok() ==> final(attempts).records(out->Ok_0.inverse),
            out.is_err() ==> attempt::value_rejection(final(attempts).event(),op,out->Err_0), out.is_ok() ==> out->Ok_0.corresponds(self,op,branch) && out->Ok_0.pending_for(managed),
            out.is_err() ==> out==Err(ValueError::Capacity) || out==Err(ValueError::Overflow),
    {
        let (mut cell,guard)=self.inner.acquire_write();
        let result=cell.forward_following(op,branch,Ghost(managed),Tracked(cause));
        let tracked origin=cell.joint.receipt();
        proof {attempts.record(&origin);}
        guard.release_write(cell);
        match result {
            Ok(forward)=>Ok(Applied {outcome:forward.outcome,next:forward.next,pending:forward.pending,inverse:Inverse {target:self.clone(),state:forward.inverse,origin:Tracked(origin)}}),
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
/// Classification of a complete scalar observation, including intervening
/// callers. Rejections preserve the value/depth; restores apply the captured
/// strict inverse; accepted operations use their real outcome-selected node.
pub open spec fn interpreted_step(event:Event,key:Port,before:Map<Port,ValueState>,after:Map<Port,ValueState>)->bool {
    &&& event.valid() && before.contains_key(key) && before[key]==event.before()
    &&& after==before.insert(key,event.after())
    &&& match event {
        Event::Forward {operation,branch,next,..}=>{
            let run=d::run(library(),d::Node::Operation {operation:(key,operation),argument:(),select:|out:Outcome|branch.selected(out)},before);
            run.is_some() && run.unwrap().state==after && run.unwrap().next==next
        },
        Event::Computed {..}=>effect::table_step(event,key,before,after),
        Event::Restore {inverse,..}=>d::inverse(key,|v:ValueState|inverse.undo(v))(before)==Some(after),
        Event::Rejected {..}|Event::Blocked {..}|Event::ComputationRejected {..}|Event::StaleComputation {..}=>before==after,
    }
}
pub proof fn interpret_event(event:Event,key:Port,before:Map<Port,ValueState>)
    requires event.valid(),before.contains_key(key),before[key]==event.before(),
    ensures interpreted_step(event,key,before,before.insert(key,event.after())),
{
    if event is Forward {forward_interpretation(event,key,before);}
    if event is Computed {effect::forward_interpretation(event,key,before);}
    if event.after()==event.before() {assert(before.insert(key,event.after()) =~= before);}
}
/// Whole history correspondence, not a collection of unconnected method labels.
/// Rejected calls stutter; restoration uses the same strict returned function.
pub proof fn history_interpretation(snapshot:&Snapshot,key:Port,table:Map<Port,ValueState>)
    requires snapshot.certified(),table.contains_key(key),table[key]==snapshot.initial(),
    ensures forall|i:int| #![trigger snapshot.history()[i]] 0<=i<snapshot.history().len() ==> {
        let event=snapshot.history()[i];let before=table.insert(key,event.before());let after=table.insert(key,event.after());
        &&& event.valid()
        &&& ((event is Rejected || event is Blocked || event is ComputationRejected || event is StaleComputation) ==> before==after)
        &&& (event is Forward ==> d::run(library(),d::Node::Operation {operation:(key,event->Forward_operation),argument:(),
            select:|out:Outcome|event->Forward_branch.selected(out)},before).unwrap().state==after)
        &&& (event is Restore ==> d::inverse(key,|v:ValueState|event->Restore_inverse.undo(v))(before)==Some(after))
        &&& (event is Computed ==> effect::table_step(event,key,before,after))
    },
{
    assert forall|i:int| #![trigger snapshot.history()[i]] 0<=i<snapshot.history().len() implies {
        let event=snapshot.history()[i];let before=table.insert(key,event.before());let after=table.insert(key,event.after());
        &&& event.valid()
        &&& ((event is Rejected || event is Blocked || event is ComputationRejected || event is StaleComputation) ==> before==after)
        &&& (event is Forward ==> d::run(library(),d::Node::Operation {operation:(key,event->Forward_operation),argument:(),
            select:|out:Outcome|event->Forward_branch.selected(out)},before).unwrap().state==after)
        &&& (event is Restore ==> d::inverse(key,|v:ValueState|event->Restore_inverse.undo(v))(before)==Some(after))
        &&& (event is Computed ==> effect::table_step(event,key,before,after))
    } by {
        let event=snapshot.history()[i];
        assert(event.valid());
        if event is Forward {forward_interpretation(event,key,table.insert(key,event.before()));}
        if event is Computed {effect::forward_interpretation(event,key,table.insert(key,event.before()));}
        if event is Forward || event is Restore || event is Computed {
            assert(table.insert(key,event.before()).insert(key,event.after()) =~= table.insert(key,event.after()));
        }
    }
}
}

#[path = "value_program.rs"]
pub mod program;

#[path = "scalar_effect.rs"]
pub mod effect;

#[path = "shared_value_history.rs"]
pub mod history;

#[path = "value_cursor.rs"]
pub mod cursor;

#[path = "value_slot.rs"]
pub mod slot;

#[path = "value_heap.rs"]
pub mod heap;

#[path = "joint_execution.rs"]
pub mod joint;

#[path = "value_access.rs"]
pub mod access;
#[path = "value_alias.rs"]
pub mod alias;
#[path = "native_effect.rs"]
pub mod native_effect;

#[path = "value_function.rs"]
pub mod function;

#[path = "service_program.rs"]
pub mod services;

#[path = "service_function.rs"]
pub mod service_function;

#[path = "service_composition.rs"]
pub mod service_composition;

#[path = "service_stack.rs"]
pub mod service_stack;

#[path = "value_registration.rs"]
pub mod registration;

#[path = "value_attempt.rs"]
pub mod attempt;

#[path = "value_restoration.rs"]
pub mod restoration;

#[path = "shared_payload.rs"]
pub mod payload;

#[path = "managed_function.rs"]
pub mod managed;
