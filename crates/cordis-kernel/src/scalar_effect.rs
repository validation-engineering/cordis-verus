//! Extensible scalar computations with checked preparation and managed landing.
//! User computation runs outside the value and episode locks. A private prepared
//! value retains the real input, result and target; landing rechecks that input.
//! Trait implementations need Verus verification to establish their model law.
#[cfg(verus_keep_ghost)]
use super::Event;
use super::{
    Applied, Branch, Inverse, InverseState, Operation, Outcome, ReversibleValue, ValueState,
};
use crate::execution::{Execution, ValueAdmission};
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, fresh_grammar as f, guarded_components as c, mediated as m, Port,
};
use vstd::prelude::*;

verus! {

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Decision {pub value:u64,pub matched:bool}
pub type Code = spec_fn(u64)->Option<Decision>;

/// Implement `model` and prove that `compute` returns exactly its actual result.
/// The managed owner constructs the inverse, so implementations cannot substitute
/// its target or captured before/after state. External effects are not covered by
/// this scalar contract; unchecked Rust implementations do not inherit the law.
pub trait ScalarEffect: Sized {
    spec fn model(&self)->Code;
    fn compute(self,input:u64)->(out:Option<Decision>)
        ensures out==(self.model())(input);
}

impl ScalarEffect for Operation {
    open spec fn model(&self)->Code {
        |input:u64| match self.eval(input) {Some(out)=>Some(Decision {value:out.after,matched:out.matched}),None=>None}
    }
    fn compute(self,input:u64)->(out:Option<Decision>) {
        match self.evaluate(input) {Ok(out)=>Some(Decision {value:out.after,matched:out.matched}),Err(_)=>None}
    }
}

/// A separately implemented primitive, without extending the Operation enum.
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct ScaleAdd {pub scale:u64,pub offset:u64}
impl ScalarEffect for ScaleAdd {
    open spec fn model(&self)->Code {
        |input:u64| if input as int*self.scale as int+self.offset as int<=u64::MAX {
            Some(Decision {value:(input as int*self.scale as int+self.offset as int) as u64,matched:true})
        } else {None}
    }
    fn compute(self,input:u64)->(out:Option<Decision>) {
        match input.checked_mul(self.scale) {
            None=>None,
            Some(scaled)=>scaled.checked_add(self.offset).map(|value:u64| -> (decision:Decision)
                ensures decision==(Decision {value,matched:true}),
            {Decision {value,matched:true}}),
        }
    }
}

/// Compose calculations before making one guarded shared-value write.
pub struct Then<L,R> {pub first:L,pub then:R}
impl<L:ScalarEffect,R:ScalarEffect> ScalarEffect for Then<L,R> {
    open spec fn model(&self)->Code {
        |input:u64| match (self.first.model())(input) {
            None=>None,Some(value)=>(self.then.model())(value.value),
        }
    }
    fn compute(self,input:u64)->(out:Option<Decision>) {
        match self.first.compute(input) {None=>None,Some(value)=>self.then.compute(value.value)}
    }
}
/// The actual predicate outcome selects the next calculation. Intermediates
/// are local data: rejection causes no partial shared-value write.
pub struct Choose<P,Y,N> {pub predicate:P,pub matched:Y,pub unmatched:N}
impl<P:ScalarEffect,Y:ScalarEffect,N:ScalarEffect> ScalarEffect for Choose<P,Y,N> {
    open spec fn model(&self)->Code {
        |input:u64| match (self.predicate.model())(input) {
            None=>None,Some(value)=>if value.matched {(self.matched.model())(value.value)} else {(self.unmatched.model())(value.value)},
        }
    }
    fn compute(self,input:u64)->(out:Option<Decision>) {
        match self.predicate.compute(input) {
            None=>None,Some(value)=>if value.matched {self.matched.compute(value.value)} else {self.unmatched.compute(value.value)},
        }
    }
}

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum EffectError {Closed,Capacity,Interference,Rejected}

pub open spec fn operation(code:Code)->m::Operation<ValueState,Outcome> {
    |input:ValueState| if input.depth==u64::MAX || code(input.value).is_none() {None} else {
        let result=code(input.value).unwrap();
        let after=ValueState {value:result.value,depth:(input.depth+1) as u64};
        Some(m::ValueYield {value:after,outcome:Outcome {before:input.value,after:result.value,matched:result.matched},
            undo:|current:ValueState|if current==after {Some(input)} else {None}})
    }
}
pub open spec fn library()->d::Library<Port,(Port,Code),(),ValueState,Outcome> {
    d::Library {values:|_:Port,_:ValueState|true,arguments:|_:(Port,Code),_:()|true,
        outcomes:|_:(Port,Code),_:Outcome|true,key:|a:(Port,Code)|a.0,allowed:ISet::full(),
        apply:|a:(Port,Code),_:()|operation(a.1)}
}
/// Capturing the real before/after states establishes strict restoration for
/// every modeled computation; no plugin-provided inverse law is assumed here.
pub proof fn primitive_theory()
    ensures d::primitive_theory(|_:Port,a:ValueState,b:ValueState|a==b,library()),
{
    assert forall|a:(Port,Code),x:()| library().allowed.contains(a) && (library().arguments)(a,x)
        implies d::operation_typed(library(),a,x)
            && m::operation_admissible(|u:ValueState,v:ValueState|u==v,(library().apply)(a,x)) by { }
}

pub open spec fn terminal_program(code:Code,key:Port)->f::Programs<(Port,Code),(),ValueState,Outcome,()> {
    |_:usize| |_:()| f::Node::Dependent {node:d::Node::Operation {operation:(key,code),argument:(),select:|_:Outcome|None}}
}
/// Full-carrier membership for the terminal managed scalar operation. A
/// continuation outside this scalar calculation still needs its own contract.
pub proof fn terminal_component(code:Code,key:Port,actor:usize,keys:ISet<Port>,provisions:ISet<Port>)
    requires keys.contains(key),
    ensures c::component(library(),terminal_program(code,key),actor,keys,provisions,()),
{
    primitive_theory();
    f::constructor_member(library(),terminal_program(code,key),actor,keys,provisions,());
    c::member_is_component(|_:Port,a:ValueState,b:ValueState|a==b,library(),terminal_program(code,key),actor,keys,provisions,());
}

#[allow(dead_code)] // The semantic code is erased in ordinary Rust.
pub struct Prepared {
    target:ReversibleValue,
    expected:ValueState,
    decision:Option<Decision>,
    code:Ghost<Code>,
    observed:Ghost<super::Snapshot>,
    cause:Tracked<super::joint::Receipt>,
}
impl Prepared {
    pub closed spec fn target(&self)->ReversibleValue {self.target}
    pub closed spec fn expected(&self)->ValueState {self.expected}
    pub closed spec fn code(&self)->Code {self.code@}
    pub closed spec fn observation(&self)->super::Snapshot {self.observed@}
    pub closed spec fn cause(&self)->super::joint::Receipt {self.cause@}
    pub closed spec fn wf(&self)->bool {
        self.decision==(self.code())(self.expected().value)
            && self.observation().certified() && self.observation().state()==self.expected()
            && self.observation().source()==self.target().source()
            && self.observation().object()==self.target().object()
            && self.observation().journal_spec()==self.target().journal_spec()
            && self.cause().wf() && self.cause().journal()==self.target().journal_spec()
            && self.cause().events()==self.observation().joint_spec().events()
    }

    pub proof fn read_evidence(&self)
        requires self.wf(),
        ensures self.cause().wf(),self.cause().journal()==self.target().journal_spec(),
            self.cause().events()==self.observation().joint_spec().events(),self.observation().certified(),
            self.observation().state()==self.expected(),self.observation().journal_spec()==self.target().journal_spec(),
    { }

    /// Only the checked execution owner can land this prepared computation.
    /// The entire check/write is under the value lock; no plugin code runs here.
    pub(crate) fn commit(self,branch:Branch,Ghost(managed):Ghost<bool>,Tracked(attempts):Tracked<&mut super::attempt::Ledger>)->(out:Result<Applied,EffectError>)
        requires self.wf(),old(attempts).wf(),
        ensures final(attempts).appended(old(attempts),&self.target()),
            final(attempts).events().last().follows(&self.cause()),
            out.is_ok() ==> final(attempts).records(out->Ok_0.inverse),
            out.is_err() ==> super::attempt::effect_rejection(final(attempts).event(),self.code(),self.expected(),out->Err_0), out.is_ok() ==> out->Ok_0.effect_corresponds(&self.target(),self.code(),branch)
            && out->Ok_0.inverse.state().before==self.expected() && out->Ok_0.pending_for(managed),
            out.is_err() ==> out!=Err(EffectError::Closed),
    { commit_calculated(&self.target,self.expected,self.decision,self.code,branch,Ghost(managed),Tracked(self.cause.borrow().duplicate()),Tracked(attempts)) }

}
#[allow(clippy::too_many_arguments)] // Four inputs carry erased proof data; four are runtime values.
fn commit_calculated(target:&ReversibleValue,expected:ValueState,decision:Option<Decision>,Ghost(code):Ghost<Code>,branch:Branch,
    Ghost(managed):Ghost<bool>,Tracked(cause):Tracked<super::joint::Receipt>,Tracked(attempts):Tracked<&mut super::attempt::Ledger>)->(out:Result<Applied,EffectError>)
    requires decision==code(expected.value),cause.wf(),cause.journal()==target.journal_spec(),old(attempts).wf(),
    ensures final(attempts).appended(old(attempts),target),final(attempts).events().last().follows(&cause),
        out.is_ok() ==> final(attempts).records(out->Ok_0.inverse),
        out.is_err() ==> super::attempt::effect_rejection(final(attempts).event(),code,expected,out->Err_0),
        out.is_ok() ==> out->Ok_0.effect_corresponds(target,code,branch) && out->Ok_0.inverse.state().before==expected && out->Ok_0.pending_for(managed),
        out.is_err() ==> out!=Err(EffectError::Closed),
    {
        let (mut cell,guard)=target.inner.acquire_write();
        let before=cell.state;
        if before!=expected {
            let _pending=cell.record_following(Ghost(before),Ghost(Event::StaleComputation {expected,before}),Ghost(false),Tracked(Some(cause.duplicate())));
            proof {let tracked receipt=cell.joint.receipt();attempts.record(&receipt);}
            guard.release_write(cell);return Err(EffectError::Interference);
        }
        if before.depth==u64::MAX {
            let _pending=cell.record_following(Ghost(before),Ghost(Event::ComputationRejected {code,before}),Ghost(false),Tracked(Some(cause.duplicate())));
            proof {let tracked receipt=cell.joint.receipt();attempts.record(&receipt);}
            guard.release_write(cell);return Err(EffectError::Capacity);
        }
        let decision=match decision {
            Some(value)=>value,
            None=>{
                let _pending=cell.record_following(Ghost(before),Ghost(Event::ComputationRejected {code,before}),Ghost(false),Tracked(Some(cause.duplicate())));
                proof {let tracked receipt=cell.joint.receipt();attempts.record(&receipt);}
            guard.release_write(cell);return Err(EffectError::Rejected);
            },
        };
        let after=ValueState {value:decision.value,depth:before.depth+1};
        let outcome=Outcome {before:before.value,after:after.value,matched:decision.matched};
        let next=branch.select(outcome);cell.state=after;
        let pending=cell.record_following(Ghost(before),Ghost(Event::Computed {code,branch,before,after,outcome,next}),Ghost(managed),Tracked(Some(cause.duplicate())));
        let tracked origin=cell.joint.receipt();
        proof {attempts.record(&origin);}
        guard.release_write(cell);
        Ok(Applied {outcome,next,pending,inverse:Inverse {target:target.clone(),state:InverseState {before,after},origin:Tracked(origin)}})
    }

impl ReversibleValue {
    /// Snapshot, release the read lock, then invoke the actual implementation.
    /// Dropping the prepared value makes no write and acquires no cleanup debt.
    pub fn prepare_effect<E:ScalarEffect>(&self,effect:E)->(out:Prepared)
        ensures out.wf(),out.target()==*self,out.code()==effect.model(),
    {
        self.prepare_observed(effect,self.snapshot())
    }
    /// Native captures supply a real read that includes their slot selection.
    /// This entry cannot turn caller-supplied numbers into a certified input.
    pub(crate) fn prepare_observed<E:ScalarEffect>(&self,effect:E,snapshot:super::Snapshot)->(out:Prepared)
        requires snapshot.certified(),snapshot.source()==self.source(),snapshot.object()==self.object(),snapshot.journal_spec()==self.journal_spec(),
        ensures out.wf(),out.target()==*self,out.code()==effect.model(),out.observation()==snapshot,
    {
        proof {assert(snapshot.joint_spec().events().len()>0);}
        let cause=snapshot.joint_execution().checkpoint_receipt();
        let ghost code=effect.model();
        let decision=effect.compute(snapshot.value());
        Prepared {target:self.clone(),expected:snapshot.state,decision,code:Ghost(code),observed:Ghost(snapshot),cause}
    }
}
impl Applied {
    pub open spec fn effect_corresponds(&self,target:&ReversibleValue,code:Code,branch:Branch)->bool {
        &&& self.inverse.recorded()
        &&& self.inverse.origin().event().change==(super::joint::Change::Value {event:Event::Computed {code,branch,
            before:self.inverse.state().before,after:self.inverse.state().after,outcome:self.outcome,next:self.next}})
        &&& self.inverse.target()==*target
        &&& operation(code)(self.inverse.state().before).is_some()
        &&& operation(code)(self.inverse.state().before).unwrap().value==self.inverse.state().after
        &&& operation(code)(self.inverse.state().before).unwrap().outcome==self.outcome
        &&& self.next==branch.selected(self.outcome)
        &&& forall|input:ValueState| #[trigger] self.inverse.state().undo(input)==(operation(code)(self.inverse.state().before).unwrap().undo)(input)
    }
}
impl<V,C,G,Cb,X> Execution<V,C,G,ChildCleanup<Cb,X>> {
    /// Revalidate admission after user computation, then retain the
    /// actual inverse before returning the outcome to the ordinary adapter.
    pub fn apply_prepared_effect(&mut self,id:usize,prepared:Prepared,branch:Branch)->(out:Result<ValueAdmission,EffectError>)
        requires old(self).wf(),prepared.wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),
            out!=Err(EffectError::Closed) ==> final(self).value_attempts().events().last().follows(&prepared.cause()),
            final(self).wf(),final(self).capture()==old(self).capture(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            final(self).effect_state()==old(self).effect_state(),final(self).checked_out()==old(self).checked_out(),
            final(self).initialized()==old(self).initialized(),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            final(self).cleanup_state().drained_failure()==old(self).cleanup_state().drained_failure(),
            (out==Err(EffectError::Closed))==!(old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)),
            out.is_err() ==> final(self).same_runtime(old(self)),
            out==Err(EffectError::Closed) ==> *final(self)==*old(self),
            out!=Err(EffectError::Closed) ==> final(self).value_attempts().appended(&old(self).value_attempts(),&prepared.target()),
            out.is_err() && out!=Err(EffectError::Closed) ==>
                super::attempt::effect_rejection(final(self).value_attempts().event(),prepared.code(),prepared.expected(),out->Err_0),
            out.is_ok() ==> final(self).value_attempts().events().last().same(&out->Ok_0.registration().write()),
            out.is_ok() ==> final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link(),
            out.is_ok() ==> final(self).cleanup_state().acquisition_open(id)==old(self).cleanup_state().acquisition_open(id) && final(self).cleanup_state().live(id) && old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)
                && out->Ok_0.next==branch.selected(out->Ok_0.outcome)
                && out->Ok_0.token==old(self).cleanup_state().queues()[id].slots().len()
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(out->Ok_0.token)
                && final(self).cleanup_state().queues()[id].slots()==old(self).cleanup_state().queues()[id].slots().push(
                    final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int])
                && final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].is_some()
                && final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap() is Value
                && {
                    let inverse=final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap()->Value_0;
                    &&& out->Ok_0.registration().records(inverse,final(self).cleanup_state().queues()[id].link(),
                        final(self).cleanup_state().queues()[id].protocol().domain_id(),out->Ok_0.token)
                    &&& inverse.state().before==prepared.expected()
                    &&& (Applied {outcome:out->Ok_0.outcome,next:out->Ok_0.next,pending:Tracked(None),inverse}).effect_corresponds(&prepared.target(),prepared.code(),branch)
                },
            final(self).status_links()==old(self).status_links(),
    {
        // Commit exports the complete result contract; its private input-read
        // history need not be expanded again in this owner/queue composition.
        hide(Prepared::wf);
        if !self.accepts_acquisition(id) {return Err(EffectError::Closed);}
        proof {self.representation();}
        let result=prepared.commit(branch,Ghost(super::joint::local(self.cleanup_state().queues()[id].link(),prepared.target().journal_spec())),Tracked(self.attempts.borrow_mut()));
        proof {self.representation();}
        let applied=result?;
        let outcome=applied.outcome;let next=applied.next;
        let registered=self.register_inverse(id,applied);
        Ok(ValueAdmission {outcome,next,token:registered.token,evidence:registered.evidence})
    }
}

pub open spec fn table_step(event:Event,key:Port,before:Map<Port,ValueState>,after:Map<Port,ValueState>)->bool {
    &&& event is Computed
    &&& d::run(library(),d::Node::Operation {operation:(key,event->Computed_code),argument:(),
        select:|out:Outcome|event->Computed_branch.selected(out)},before).is_some()
    &&& d::run(library(),d::Node::Operation {operation:(key,event->Computed_code),argument:(),
        select:|out:Outcome|event->Computed_branch.selected(out)},before).unwrap().state==after
}
pub proof fn forward_interpretation(event:Event,key:Port,table:Map<Port,ValueState>)
    requires event.valid(),event is Computed,table.contains_key(key),table[key]==event.before(),
    ensures table_step(event,key,table,table.insert(key,event.after())),
        {
            let node=d::Node::Operation {operation:(key,event->Computed_code),argument:(),select:|out:Outcome|event->Computed_branch.selected(out)};
            let result=d::run(library(),node,table).unwrap();
            &&& result.next==event->Computed_next
            &&& forall|test:Map<Port,ValueState>| #[trigger] (result.undo)(test)==
                if test.contains_key(key) && test[key]==event.after() {Some(test.insert(key,event.before()))} else {None}
        },
{ }
}
