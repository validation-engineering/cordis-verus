//! Resumable interpreted programs on the production shared value. The program,
//! continuation, target and episode identity stay inside this linear owner.
//! Other callers may run between steps; persistent checkpoints retain their
//! actual events rather than pretending consecutive calls were atomic.
#[cfg(verus_keep_ghost)]
use super::program::Instruction;
use super::program::Program;
use super::slot::{ReadError, ServiceBinding, ServiceSlot};
use super::{Applied, Inverse, Outcome, ReversibleValue, Snapshot, ValueError};
#[cfg(verus_keep_ghost)]
use super::{Event, ValueState};
use crate::action_ledger::ActionTicket;
use crate::execution::Execution;
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
use crate::Port;
#[cfg(verus_keep_ghost)]
use crate::{dependent_grammar as d, guarded_components as c};
use vstd::prelude::*;

verus! {
#[derive(Copy,Clone)]
pub struct Owner {origin:Option<ActionTicket>,work:u64,group:usize,queue:u64}
impl Owner {
    pub(crate) fn capture<V,C,G,I>(execution:&Execution<V,C,G,I>,id:usize)->(out:Self)
        requires execution.wf(),execution.cleanup_state().live(id),
        ensures out.matches(execution,id),
    {
        proof {execution.representation();}
        Self {origin:execution.work.lifecycle_ticket(),work:execution.work.domain(),group:id,queue:execution.get(id).unwrap().domain()}
    }

    pub closed spec fn matches<V,C,G,I>(&self,execution:&Execution<V,C,G,I>,id:usize)->bool {
        self.origin==execution.origin() && self.work==execution.work_state().domain_id() && self.group==id
            && execution.cleanup_state().domain_ids().contains_key(id) && self.queue==execution.cleanup_state().domain_ids()[id]
    }
    pub(crate) fn check<V,C,G,I>(&self,execution:&Execution<V,C,G,I>,id:usize)->(out:bool)
        requires execution.wf(),execution.cleanup_state().live(id),
        ensures out==self.matches(execution,id),
    {
        proof {execution.representation();}
        self.origin==execution.work.lifecycle_ticket() && self.work==execution.work.domain() && self.group==id
            && self.queue==execution.get(id).unwrap().domain()
    }
}
pub struct Step {pub at:nat,pub pc:usize,pub next:Option<usize>}
pub open spec fn selects(code:Seq<Instruction>,step:Step,event:Event)->bool {
    step.pc<code.len() && match event {
        Event::Forward {operation,branch,next,..}=>operation==code[step.pc as int].operation
            && branch==code[step.pc as int].branch && step.next==next,
        Event::Rejected {operation,..}=>operation==code[step.pc as int].operation && step.next==Some(step.pc),
        _=>false,
    }
}
pub open spec fn path(code:Seq<Instruction>,steps:Seq<Step>,events:Seq<Event>,next:Option<usize>)->bool {
    &&& if steps.len()==0 {next==if code.len()==0 {None} else {Some(0)}}
        else {steps.first().pc==0 && next==steps.last().next}
    &&& next.is_some() ==> next.unwrap()<code.len()
    &&& forall|i:int| 0<=i<steps.len() ==> #[trigger] steps[i].at<events.len()
        && selects(code,steps[i],events[steps[i].at as int])
    &&& forall|i:int| 0<=i<steps.len()-1 ==> #[trigger] steps[i].next==Some(steps[i+1].pc) && steps[i].at<steps[i+1].at
}
pub proof fn extend_observation(code:Seq<Instruction>,steps:Seq<Step>,earlier:Seq<Event>,later:Seq<Event>,next:Option<usize>)
    requires path(code,steps,earlier,next),earlier.len()<=later.len(),later.take(earlier.len() as int)==earlier,
    ensures path(code,steps,later,next),
{
    assert forall|i:int| 0<=i<steps.len() implies #[trigger] steps[i].at<later.len()
        && selects(code,steps[i],later[steps[i].at as int]) by {
        assert(later[steps[i].at as int]==earlier[steps[i].at as int]);
    }
}
pub proof fn append_step(code:Seq<Instruction>,steps:Seq<Step>,events:Seq<Event>,pc:usize,next:Option<usize>)
    requires events.len()>0,path(code,steps,events,Some(pc)),
        selects(code,Step {at:(events.len()-1) as nat,pc,next},events.last()),
        next.is_some() ==> next.unwrap()<code.len(),
        steps.len()>0 ==> steps.last().at<events.len()-1,
    ensures path(code,steps.push(Step {at:(events.len()-1) as nat,pc,next}),events,next),
{
    let step=Step {at:(events.len()-1) as nat,pc,next};
    assert forall|i:int| 0<=i<steps.push(step).len()-1 implies #[trigger] steps.push(step)[i].next==Some(steps.push(step)[i+1].pc)
        && steps.push(step)[i].at<steps.push(step)[i+1].at by {
        if i==steps.len()-1 {assert(steps[i].next==Some(pc));}
    }
}

#[allow(dead_code)] // Checkpoints carry erased history and resource witnesses.
pub struct Cursor {
    program:Program,target:ReversibleValue,owner:Owner,next:Option<usize>,
    checkpoint:Snapshot,steps:Ghost<Seq<Step>>,binding:Option<ServiceBinding>,last_registration:Ghost<Option<super::registration::Evidence>>,
}
impl Cursor {
    pub closed spec fn last_registration(&self)->Option<super::registration::Evidence> {self.last_registration@}

    pub closed spec fn code(&self)->Seq<Instruction> {self.program.code()}
    pub closed spec fn target(&self)->ReversibleValue {self.target}
    pub closed spec fn owner(&self)->Owner {self.owner}
    pub closed spec fn next(&self)->Option<usize> {self.next}
    pub closed spec fn checkpoint(&self)->Snapshot {self.checkpoint}
    pub closed spec fn steps(&self)->Seq<Step> {self.steps@}
    pub closed spec fn binding_spec(&self)->Option<ServiceBinding> {self.binding}
    pub fn binding(&self)->(out:Option<&ServiceBinding>)
        ensures out.is_some()==self.binding_spec().is_some(),out.is_some() ==> *out.unwrap()==self.binding_spec().unwrap(),
    {self.binding.as_ref()}
    pub closed spec fn wf(&self)->bool {
        self.program.valid() && self.checkpoint.certified() && self.checkpoint.source()==self.target.source()
            && self.checkpoint.initial()==self.target.initial() && self.checkpoint.object()==self.target.object() && self.checkpoint.journal_spec()==self.target.journal_spec() && path(self.code(),self.steps(),self.checkpoint.history(),self.next())
            && (self.binding_spec().is_some() ==> self.binding_spec().unwrap().wf()
                && *self.binding_spec().unwrap().capture_spec().value_spec()==self.target())
    }
    pub open spec fn same_program(&self,earlier:&Self)->bool {
        self.code()==earlier.code() && self.target()==earlier.target() && self.owner()==earlier.owner() && self.binding_spec()==earlier.binding_spec()
    }
    pub open spec fn joint_positions(&self)->Seq<nat> {self.steps().map(|_:int,step:Step|self.checkpoint().positions()[step.at as int])}
    /// A resumed continuation's steps need not be adjacent: other writers,
    /// slot swaps and lifecycle commits may occur between these exact indices.
    pub proof fn joint_steps(&self)
        requires self.wf(),
        ensures self.joint_positions().len()==self.steps().len(),
            forall|i:int| 0<=i<self.steps().len() ==> {
                let at=#[trigger] self.joint_positions()[i];let frames=self.checkpoint().joint_spec().events();
                &&& at<frames.len() && frames[at as int].event.key==self.target().object().key
                &&& frames[at as int].event.change==(super::joint::Change::Value {event:self.checkpoint().history()[self.steps()[i].at as int]})
                &&& selects(self.code(),self.steps()[i],self.checkpoint().history()[self.steps()[i].at as int])
            },
            forall|i:int| 0<=i<self.steps().len()-1 ==> #[trigger] self.joint_positions()[i]<#[trigger] self.joint_positions()[i+1],
    {
        self.checkpoint.projection();
        assert forall|i:int| 0<=i<self.steps().len() implies {
            let at=#[trigger] self.joint_positions()[i];let frames=self.checkpoint().joint_spec().events();
            &&& at<frames.len() && frames[at as int].event.key==self.target().object().key
            &&& frames[at as int].event.change==(super::joint::Change::Value {event:self.checkpoint().history()[self.steps()[i].at as int]})
            &&& selects(self.code(),self.steps()[i],self.checkpoint().history()[self.steps()[i].at as int])
        } by {assert(self.steps()[i].at<self.checkpoint.history().len());}
    }
    pub fn position(&self)->(out:Option<usize>) ensures out==self.next(), {self.next}
    pub fn observation(&self)->(out:&Snapshot) ensures *out==self.checkpoint(), {&self.checkpoint}
    /// Include intervening writes and cleanup attempts, even after withdrawal.
    /// This only observes; it cannot admit another program step.
    pub fn observe(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_program(old(self)),final(self).next()==old(self).next(),
            final(self).steps()==old(self).steps(),final(self).checkpoint().extends(&old(self).checkpoint()),
    {
        let snapshot=self.target.snapshot_after(&self.checkpoint);
        proof {extend_observation(self.code(),self.steps(),self.checkpoint.history(),snapshot.history(),self.next());}
        self.checkpoint=snapshot;
    }
    /// A private interpreter step. The only caller must append its real inverse
    /// to the authenticated episode queue before exposing its result.
    fn advance(&mut self,Ghost(managed):Ghost<bool>)->(out:Result<Option<Applied>,ValueError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_program(old(self)),final(self).checkpoint().extends(&old(self).checkpoint()),
            (out==Ok(None))==old(self).next().is_none(),
            old(self).next().is_none() ==> *final(self)==*old(self),
            old(self).next().is_some() ==> final(self).steps().len()==old(self).steps().len()+1
                && final(self).steps().take(old(self).steps().len() as int)==old(self).steps(),
            old(self).next().is_some() ==> final(self).checkpoint().history().len()>old(self).checkpoint().history().len()
                && final(self).steps()==old(self).steps().push(Step {at:(final(self).checkpoint().history().len()-1) as nat,
                    pc:old(self).next().unwrap(),next:final(self).next()}),
            final(self).last_registration()==old(self).last_registration(),
            out.is_err() ==> super::attempt::value_rejection(final(self).checkpoint().history().last(),
                old(self).code()[old(self).next().unwrap() as int].operation,out->Err_0),
            out.is_err() ==> (out==Err(ValueError::Capacity) || out==Err(ValueError::Overflow)) && final(self).next()==old(self).next(),
            out.is_ok() && out->Ok_0.is_some() ==> {
                let applied=out->Ok_0.unwrap();let instruction=old(self).code()[old(self).next().unwrap() as int];
                &&& old(self).next().is_some()
                &&& applied.pending_for(managed)
                &&& applied.corresponds(&old(self).target(),instruction.operation,instruction.branch)
                &&& applied.inverse.origin().at()==final(self).checkpoint().positions().last()
                &&& final(self).next()==applied.next
                &&& final(self).checkpoint().history().last()==(Event::Forward {operation:instruction.operation,branch:instruction.branch,
                    before:applied.inverse.state().before,after:applied.inverse.state().after,outcome:applied.outcome,next:applied.next})
            },
    {
        proof {self.checkpoint.reflexive();}
        let pc=match self.next {None=>return Ok(None),Some(pc)=>pc};
        let instruction=self.program.instruction(pc).unwrap();
        let (mut cell,guard)=self.target.inner.acquire_write();
        proof {cell.extends(&self.checkpoint);}
        let ghost before=cell.history@;
        let result=cell.forward(instruction.operation,instruction.branch,Ghost(managed));
        let tracked origin=cell.joint.receipt();
        let snapshot=cell.snapshot_after(&self.checkpoint);guard.release_write(cell);
        let next=match &result {Ok(forward)=>forward.next,Err(_)=>Some(pc)};
        proof {
            assert(snapshot.history().take(self.checkpoint.history().len() as int) =~= self.checkpoint.history());
            extend_observation(self.code(),self.steps(),self.checkpoint.history(),snapshot.history(),Some(pc));
            self.program.valid_instruction(pc);
            assert(instruction.valid(pc as int,self.code().len()));
            append_step(self.code(),self.steps(),snapshot.history(),pc,next);
            let step=Step {at:(snapshot.history().len()-1) as nat,pc,next};
            assert(self.steps().push(step).take(self.steps().len() as int) =~= self.steps());
            self.steps=Ghost(self.steps().push(step));
        }
        self.checkpoint=snapshot;self.next=next;
        match result {
            Ok(forward)=>Ok(Some(Applied {outcome:forward.outcome,next:forward.next,pending:forward.pending,
                inverse:Inverse {target:self.target.clone(),state:forward.inverse,origin:Tracked(origin)}})),
            Err(error)=>Err(error),
        }
    }
    /// Lift this actual object's history through a retained, alias-aware view.
    /// This does not assert that every host slot stayed fixed during the trace.
    pub proof fn object_trace(&self,initial:super::heap::Observation)->(states:Seq<super::heap::Observation>)
        requires self.wf(),initial.wf(),initial.heap.contains_key(self.target().source()),
            initial.heap[self.target().source()]==self.checkpoint().initial(),
            self.binding_spec().is_some() ==> initial.bindings.contains_key(self.binding_spec().unwrap().port_spec())
                && initial.bindings[self.binding_spec().unwrap().port_spec()]==self.binding_spec().unwrap().selection(),
        ensures states.len()==self.checkpoint().history().len()+1,states.first()==initial,
            states.last()==initial.write(self.target().source(),self.checkpoint().state()),
            forall|i:int| 0<=i<self.checkpoint().history().len() ==>
                super::heap::step(self.checkpoint().history()[i],self.target().source(),#[trigger] states[i],states[i+1]),
            self.binding_spec().is_some() ==> initial.bindings[self.binding_spec().unwrap().port_spec()].object==self.target().source(),
    {super::heap::history(&self.checkpoint,initial)}
    /// Component membership comes from the actual stored program, on its
    /// entire declared carrier, not just the outcomes seen by this cursor.
    pub proof fn component(&self,key:Port,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,pc:usize)
        requires self.wf(),keys.contains(key),
        ensures c::component(super::library(),super::program::programs(self.code(),key),actor,keys,provisions,pc),
    {self.program.component(key,actor,keys,provisions,pc);}
    /// All selected calls belong to one continuous real history. Environment
    /// writes, failed restoration and successful retries remain in this trace.
    /// The projection is one scalar service, not the entire host context.
    pub proof fn interpreted_trace(&self,key:Port,initial:Map<Port,ValueState>)->(states:Seq<Map<Port,ValueState>>)
        requires self.wf(),initial.contains_key(key),initial[key]==self.checkpoint().initial(),
        ensures states.len()==self.checkpoint().history().len()+1,states.first()==initial,
            states.last()==initial.insert(key,self.checkpoint().state()),
            forall|i:int| 0<=i<self.checkpoint().history().len() ==> {
                let event=self.checkpoint().history()[i];
                &&& #[trigger] states[i]==initial.insert(key,event.before())
                &&& states[i+1]==initial.insert(key,event.after())
                &&& super::interpreted_step(event,key,states[i],states[i+1])
            },
            forall|i:int| #![trigger self.steps()[i]] 0<=i<self.steps().len() ==> {
                let step=self.steps()[i];let event=self.checkpoint().history()[step.at as int];
                &&& selects(self.code(),step,event)
                &&& event is Forward ==> {
                    let run=d::run(super::library(),super::program::node(self.code(),key,step.pc),states[step.at as int]);
                    &&& run.is_some() && run.unwrap().state==states[step.at as int+1] && run.unwrap().next==step.next
                }
                &&& event is Rejected ==> states[step.at as int]==states[step.at as int+1] && step.next==Some(step.pc)
            },
    {
        self.checkpoint.execution();
        super::history_interpretation(&self.checkpoint,key,initial);
        let history=self.checkpoint.history();
        let states=Seq::new(history.len()+1,|i:int|if i==0 {initial} else {initial.insert(key,history[i-1].after())});
        if history.len()==0 {assert(initial.insert(key,self.checkpoint.state()) =~= initial);}
        assert forall|i:int| 0<=i<history.len() implies {
            let event=history[i];
            &&& #[trigger] states[i]==initial.insert(key,event.before())
            &&& states[i+1]==initial.insert(key,event.after())
            &&& super::interpreted_step(event,key,states[i],states[i+1])
        } by {
            let event=history[i];
            if i==0 {assert(initial.insert(key,event.before()) =~= initial);}
            else {assert(history[i-1].after()==event.before());}
            super::interpret_event(event,key,states[i]);
            assert(states[i].insert(key,event.after()) =~= states[i+1]);
        }
        assert forall|i:int| #![trigger self.steps()[i]] 0<=i<self.steps().len() implies {
            let step=self.steps()[i];let event=history[step.at as int];
            &&& selects(self.code(),step,event)
            &&& event is Forward ==> {
                let run=d::run(super::library(),super::program::node(self.code(),key,step.pc),states[step.at as int]);
                &&& run.is_some() && run.unwrap().state==states[step.at as int+1] && run.unwrap().next==step.next
            }
            &&& event is Rejected ==> states[step.at as int]==states[step.at as int+1] && step.next==Some(step.pc)
        } by {
            let step=self.steps()[i];let event=history[step.at as int];
            assert(selects(self.code(),step,event));
            if event is Forward {super::forward_interpretation(event,key,states[step.at as int]);
                assert(states[step.at as int].insert(key,event.after()) =~= states[step.at as int+1]);}
        }
        states
    }
}

#[derive(Debug)]
pub enum StartError {Closed,NoNativeOwner,Read(ReadError)}
impl<T,M,C,G,Cb,X> Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>> {
    /// Compose the actual native capture with admission in the same owner.
    /// There is no caller-supplied binding, provider, version or target.
    pub fn begin_native_value_program(&self,id:usize,port:Port,program:Program)->(out:Result<Cursor,StartError>)
        requires self.wf(),program.valid(),
        ensures (out.is_err() && out->Err_0 is Closed)==!(self.work_state().accepts() && self.cleanup_state().acquisition_open(id)),
            out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.code()==program.code() && out->Ok_0.next()==program.root()
                && out->Ok_0.owner().matches(self,id) && out->Ok_0.steps().len()==0
                && self.value_state().is_some() && !self.value_state().unwrap().closed()
                && out->Ok_0.binding_spec().is_some() && out->Ok_0.binding_spec().unwrap().port_spec()==port
                && self.value_state().unwrap().selects_slot(out->Ok_0.binding_spec().unwrap().provider_spec(),port,
                    out->Ok_0.binding_spec().unwrap().capture_spec().slot()),
    {
        proof {self.representation();}
        if !self.accepts_acquisition(id) {return Err(StartError::Closed);}
        let values=match self.native() {Some(values)=>values,None=>return Err(StartError::NoNativeOwner)};
        let binding=match values.read_reversible(port) {Ok(binding)=>binding,Err(error)=>return Err(StartError::Read(error))};
        match self.begin_bound_value_program(id,binding,program) {
            Ok(cursor)=>Ok(cursor),Err(_)=>Err(StartError::Closed),
        }
    }
}

impl<V,C,G,Cb,X> Execution<V,C,G,ChildCleanup<Cb,X>> {
    pub fn begin_value_program(&self,id:usize,value:&ReversibleValue,program:Program)->(out:Result<Cursor,Program>)
        requires self.wf(),program.valid(),
        ensures out.is_ok()==(self.work_state().accepts() && self.cleanup_state().acquisition_open(id)),
            out.is_err() ==> out->Err_0==program,
            out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.code()==program.code() && out->Ok_0.target()==*value
                && out->Ok_0.owner().matches(self,id) && out->Ok_0.next()==program.root() && out->Ok_0.steps().len()==0,
    {
        proof {self.representation();}
        if !self.accepts_acquisition(id) {return Err(program);}
        let owner=Owner::capture(self,id);
        let next=if program.is_empty() {None} else {Some(0)};
        Ok(Cursor {program,target:value.clone(),owner,next,checkpoint:value.snapshot(),steps:Ghost(Seq::empty()),binding:None,last_registration:Ghost(None)})
    }
    /// Retain the actual service selection as well as its target. Later slot
    /// replacement cannot retarget this cursor or any inverse it has queued.
    pub fn begin_bound_value_program(&self,id:usize,binding:ServiceBinding,program:Program)->(out:Result<Cursor,Program>)
        requires self.wf(),binding.wf(),program.valid(),
        ensures out.is_ok()==(self.work_state().accepts() && self.cleanup_state().acquisition_open(id)),
            out.is_err() ==> out->Err_0==program,
            out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.code()==program.code()
                && out->Ok_0.binding_spec()==Some(binding) && out->Ok_0.target()==*binding.capture_spec().value_spec()
                && out->Ok_0.owner().matches(self,id) && out->Ok_0.next()==program.root() && out->Ok_0.steps().len()==0,
    {
        let mut cursor=self.begin_value_program(id,binding.value(),program)?;
        cursor.binding=Some(binding);Ok(cursor)
    }
    /// Authenticate the stored owner and recheck current admission before the
    /// value can change. Failures never discard already registered inverses.
    pub fn advance_value_program(&mut self,id:usize,cursor:&mut Cursor)->(out:Result<Option<Outcome>,ValueError>)
        requires old(self).wf(),old(cursor).wf(),
        ensures final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(cursor).wf(),final(cursor).same_program(old(cursor)),
            final(cursor).checkpoint().extends(&old(cursor).checkpoint()),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).effect_state()==old(self).effect_state(),final(self).checked_out()==old(self).checked_out(),
            final(self).initialized()==old(self).initialized(),final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            final(self).cleanup_state().drained_failure()==old(self).cleanup_state().drained_failure(),
            (out==Err(ValueError::Closed))==!(old(cursor).owner().matches(old(self),id)
                && old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)),
            (out==Ok(None))==(old(cursor).owner().matches(old(self),id) && old(self).work_state().accepts()
                && old(self).cleanup_state().acquisition_open(id) && old(cursor).next().is_none()),
            out!=Err(ValueError::Closed) && old(cursor).next().is_some() ==>
                final(cursor).steps()==old(cursor).steps().push(Step {at:(final(cursor).checkpoint().history().len()-1) as nat,
                    pc:old(cursor).next().unwrap(),next:final(cursor).next()}),
            out==Err(ValueError::Closed) ==> *final(cursor)==*old(cursor),
            out.is_err() && out!=Err(ValueError::Closed) ==> old(cursor).next().is_some()
                && super::attempt::value_rejection(final(cursor).checkpoint().history().last(),
                    old(cursor).code()[old(cursor).next().unwrap() as int].operation,out->Err_0),
            out.is_err() || out==Ok(None) ==> *final(self)==*old(self) && final(cursor).last_registration()==old(cursor).last_registration(),
            out.is_ok() && out->Ok_0.is_some() ==> {
                let slots=final(self).cleanup_state().queues()[id].slots();let prior=old(self).cleanup_state().queues()[id].slots();
                &&& slots.len()==prior.len()+1 && slots.take(prior.len() as int)==prior
                &&& slots.last().is_some() && slots.last().unwrap() is Value
                &&& slots.last().unwrap()->Value_0.target()==old(cursor).target()
                &&& {
                    let inverse=slots.last().unwrap()->Value_0;let event=final(cursor).checkpoint().history().last();
                    &&& event is Forward && event->Forward_outcome==out->Ok_0.unwrap()
                    &&& inverse.state().before==event.before() && inverse.state().after==event.after()
                    &&& inverse.recorded() && inverse.origin().at()==final(cursor).checkpoint().positions().last()
                    &&& final(cursor).last_registration().is_some()
                    &&& final(cursor).last_registration().unwrap().records(inverse,final(self).cleanup_state().queues()[id].link(),
                        final(self).cleanup_state().queues()[id].protocol().domain_id(),(slots.len()-1) as usize)
                    &&& final(cursor).next()==event->Forward_next
                }
            },
            final(self).status_links()==old(self).status_links(),
    {
        proof {cursor.checkpoint.reflexive();}
        if !self.accepts_acquisition(id) || !cursor.owner.check(self,id) {return Err(ValueError::Closed);}
        let applied=match cursor.advance(Ghost(super::joint::local(self.cleanup_state().queues()[id].link(),cursor.target().journal_spec())))? {None=>return Ok(None),Some(applied)=>applied};
        let outcome=applied.outcome;
        let _registered=self.register_inverse(id,applied);
        proof {cursor.last_registration=Ghost(Some(_registered.evidence@));}
        proof {
            let prior=old(self).cleanup_state().queues()[id].slots();
            assert(prior.push(Some(ChildCleanup::<Cb,X>::Value(applied.inverse))).take(prior.len() as int) =~= prior);
        }
        Ok(Some(outcome))
    }
}
}
