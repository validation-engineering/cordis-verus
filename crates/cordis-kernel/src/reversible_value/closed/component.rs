//! A sealed component owner. Its complete retained word consists of the real
//! root's data inverses followed by the native Child inverses admitted here.
//! No mutable owner or callback insertion escapes this interface.
use super::Value;
use crate::lifecycle_state::registration::shared_child::{ChildCleanup, SharedChild};
use crate::reversible_value::effect::ScalarEffect;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::replay::session::CallOwner;
use crate::reversible_value::managed::{
    self,
    replay::{session::Outcome, Source},
    Step,
};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn word<T:?Sized>(slots:Seq<Option<managed::Action<(),(),T,(),()>>>,steps:Seq<Step<T>>,children:Seq<SharedChild>)->bool {
    slots.len()==steps.len()+children.len()
        && (forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).in_slot(slots[i]))
        && (forall|i:int|0<=i<children.len() ==> slots[steps.len()+i]==Some(ChildCleanup::Native(#[trigger] children[i])))
}
/// Failures return the original real owner. They do not undo a completed call.
pub struct Rejected<E> {pub outcome:Outcome<E,Value>}
/// The ghost root is selected from a real completed invocation. All later
/// Native Child entries are appended by the original production admission.
pub struct Component<E> {outcome:Outcome<E,Value>,children:Vec<SharedChild>,#[allow(dead_code)] root:Ghost<Seq<Step<Value>>>}
impl<E:ScalarEffect+Copy> Component<E> {
    pub closed spec fn outcome(&self)->Outcome<E,Value> {self.outcome}
    pub closed spec fn owner(&self)->CallOwner<Value> {self.outcome.run.owner}
    pub closed spec fn root(&self)->Seq<Step<Value>> {self.root@}
    pub closed spec fn children(&self)->Seq<SharedChild> {self.children@}
    pub closed spec fn wf(&self)->bool {
        self.owner().wf() && self.owner().conserved() && self.owner().histories().dom()==set![0usize]
            && self.outcome().run.report.is_ok() && self.outcome().run.report->Ok_0.result.is_ok()
            && self.root()==self.outcome().run.report->Ok_0.result->Ok_0.steps@
            && word(self.owner().histories()[0].initial(),self.root(),self.children())
            && (forall|i:int|0<=i<self.children().len() ==> (#[trigger] self.children()[i]).wf()
                && self.owner().baseline().origin().is_some()
                && self.children()[i].domain_id()==self.owner().baseline().origin().unwrap().domain
                && self.children()[i].owner()==self.owner().baseline().origin().unwrap().id
                && self.children()[i].episode()==Some(self.owner().baseline().origin().unwrap().generation))
    }
    pub fn id(&self)->(out:usize) ensures out==self.outcome().run.id, {self.outcome.run.id}
    pub fn child_count(&self)->(out:usize) ensures out==self.children().len(), {self.children.len()}
    pub(crate) fn child(&self,index:usize)->(out:Option<&SharedChild>)
        requires self.wf(),ensures out.is_some()==(index<self.children().len()),out.is_some() ==> *out.unwrap()==self.children()[index as int] && out.unwrap().wf(),
    {if index<self.children.len() {Some(&self.children[index])} else {None}}
    // Explicit branches preserve the erased receipt and owner relations.
    #[allow(clippy::manual_map)]
    pub fn child_snapshot(&self,index:usize)->(out:Option<crate::lifecycle_state::registration::shared_child::ChildSnapshot>)
        requires self.wf(),ensures out.is_some()==(index<self.children().len()),out.is_some() ==> out.unwrap().wf()
            && out.unwrap().source()==self.children()[index as int].source(),
    {match self.child(index) {Some(child)=>Some(child.snapshot()),None=>None}}
    pub proof fn frame(&self,prior:&Self)
        requires prior.wf(),self.owner().wf(),self.owner().conserved(),self.owner().same_inverse_word(&prior.owner()),
            self.outcome().run.report==prior.outcome().run.report,self.root()==prior.root(),self.children()==prior.children(),
        ensures self.wf(),
    {
        assert(prior.owner().histories().contains_key(0));
        assert(self.owner().histories()[0].initial()==prior.owner().histories()[0].initial());
        assert(word(self.owner().histories()[0].initial(),self.root(),self.children()));
        assert forall|i:int|0<=i<self.children().len() implies (#[trigger] self.children()[i]).wf()
            && self.owner().baseline().origin().is_some()
            && self.children()[i].domain_id()==self.owner().baseline().origin().unwrap().domain
            && self.children()[i].owner()==self.owner().baseline().origin().unwrap().id
            && self.children()[i].episode()==Some(self.owner().baseline().origin().unwrap().generation) by {
            assert(self.children()[i]==prior.children()[i]);
        }
    }
    /// The entire root group must still be retained. Foreign groups, consumed
    /// entries and actions appended outside the root interpreter reject here.
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub(crate) fn seal(outcome:Outcome<E,Value>,Ghost(source):Ghost<Source<E,Value>>,Ghost(bank):Ghost<managed::replay::bank::Bank<Value>>)->(out:Result<Self,Rejected<E>>)
        requires outcome.matches(&source,&bank),
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.outcome()==outcome && out->Ok_0.children().len()==0,
            out.is_err() ==> out->Err_0.outcome==outcome,
    {
        let report=match &outcome.run.report {Ok(r)=>r,Err(_)=>return Err(Rejected {outcome})};
        let data=match &report.result {Ok(r)=>r,Err(_)=>return Err(Rejected {outcome})};
        proof {outcome.facts(&source,&bank);reveal(managed::replay::TargetRun::from_source);outcome.run.owner.facts();}
        let groups=outcome.run.owner.execution().groups();
        if groups.allocated_groups()!=1 {return Err(Rejected {outcome});}
        let queue=match groups.get(0) {Some(q)=>q,None=>return Err(Rejected {outcome})};
        if queue.retained_len()!=data.steps.len() {return Err(Rejected {outcome});}
        let mut i=0;
        while i<data.steps.len()
            invariant i<=data.steps.len(),forall|j:int|0<=j<i ==> queue.slots()[j].is_some(),
                queue.slots().len()==data.steps.len(),
            decreases data.steps.len()-i,
        {if queue.retained(i).is_none() {return Err(Rejected {outcome});}i+=1;}
        proof {
            let owner=outcome.run.owner;let baseline=owner.baseline().cleanup_state().queues()[0];
            assert(owner.histories().contains_key(0));assert(owner.entry(0));
            assert(owner.origins()[0]==baseline);
            assert(owner.histories()[0].starts_with(baseline.slots()));
            assert(owner.histories()[0].initial().len()==queue.slots().len());
            assert(baseline.slots().len()==outcome.run.offset@+data.steps.len());
            assert(outcome.run.offset@==0);
            assert(owner.histories()[0].initial() =~= baseline.slots());
            assert(owner.histories().dom() =~= set![0usize]);
            assert(word(owner.histories()[0].initial(),data.steps@,Seq::empty()));
            assert forall|id:usize,j:int|owner.histories().contains_key(id)
                && 0<=j<owner.histories()[id].current().len() && (#[trigger] owner.histories()[id].current()[j]).is_some() implies
                    j<owner.histories()[id].initial().len() && owner.histories()[id].current()[j]==owner.histories()[id].initial()[j] by {
                assert(id==0);assert(data.steps@[j].in_slot(owner.histories()[0].initial()[j]));
                assert(crate::cleanup_groups::payload::recovery::managed(owner.histories()[0].initial()[j].unwrap()));
                owner.histories()[0].conservation(j);
            }

        }
        let ghost root=data.steps@;
        Ok(Self {outcome,children:Vec::new(),root:Ghost(root)})
    }
    /// Request and inverse are created atomically by RecordedExecution. A
    /// failed admission leaves the whole component and its word unchanged.
    // Native admission is binary; rejection preserves this entire owner unchanged.
    #[allow(clippy::result_unit_err)]
    pub fn enqueue_child(&mut self)->(out:Result<usize,()>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).root()==old(self).root(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> out->Ok_0==old(self).children().len()
                && final(self).children().len()==old(self).children().len()+1
                && final(self).children().take(old(self).children().len() as int)==old(self).children(),
    {
        let ghost prior=*self;
        proof {self.outcome.run.owner.facts();}
        let (child,_token)=self.outcome.run.owner.enqueue_native_child(0,())?;
        let index=self.children.len();self.children.push(child);
        proof {
            let a=prior.owner().histories()[0].initial();
            let b=self.owner().histories()[0].initial();
            assert forall|i:int|0<=i<self.root().len() implies (#[trigger] self.root()[i]).in_slot(b[i]) by {assert(b[i]==a[i]);}
            assert forall|i:int|0<=i<self.children().len() implies b[self.root().len()+i]==Some(ChildCleanup::Native(#[trigger] self.children()[i])) by {
                if i<prior.children().len() {assert(self.children()[i]==prior.children()[i]);}
                else {assert(i==prior.children().len());}
            }
            assert forall|i:int|0<=i<self.children().len() implies (#[trigger] self.children()[i]).wf()
                && self.owner().baseline().origin().is_some()
                && self.children()[i].domain_id()==self.owner().baseline().origin().unwrap().domain
                && self.children()[i].owner()==self.owner().baseline().origin().unwrap().id
                && self.children()[i].episode()==Some(self.owner().baseline().origin().unwrap().generation) by {
                if i<prior.children().len() {assert(self.children()[i]==prior.children()[i]);}
            }
        }Ok(index)
    }
    /// Explicit exit to the ordinary host API consumes this sealed certificate.
    pub fn into_ordinary(self)->(out:Outcome<E,Value>) ensures out==self.outcome(), {self.outcome}
}
impl<P,E:ScalarEffect+Copy> super::replay::Session<P,E> {
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub fn invoke_component(&mut self,anchor:crate::Port,work_domain:u64,parent:Option<usize>)->(out:Result<Option<Component<E>>,ComponentError<E>>)
        requires old(self).wf(),ensures final(self).wf(),out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().wf(),
    {
        let outcome=match self.invoke_next_dynamic(anchor,work_domain,parent) {Ok(Some(o))=>o,Ok(None)=>return Ok(None),Err(e)=>return Err(ComponentError::Execution(e))};
        let source=Ghost(self.inner().source(outcome.source as int));let bank=Ghost(self.inner().bank());
        match Component::seal(outcome,source,bank) {Ok(c)=>Ok(Some(c)),Err(e)=>Err(ComponentError::Rejected(e))}
    }
}
// Failure retains the original owners without allocating or dropping their cleanup state.
#[allow(clippy::large_enum_variant)]
pub enum ComponentError<E> {Execution(super::replay::Error<E>),Rejected(Rejected<E>)}
/// Only value diagnostics leave the owner; discarded inverses and mutable
/// service handles stay inside this implementation.
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum CleanupStatus {
    Data {ticket:crate::cleanup_journal::RestoreTicket,restored:bool},
    Child {ticket:crate::cleanup_journal::RestoreTicket,result:Result<(),crate::Error>,acknowledged:bool},
}
type Dispatch=crate::cleanup_groups::payload::Dispatch<(),(),std::sync::Arc<managed::Slot<Value,()>>,Value,()>;
#[allow(dead_code)]
pub struct CleanupStep {pub status:CleanupStatus,data:Ghost<Option<Dispatch>>,retirement:Tracked<Option<crate::lifecycle_state::native::runtime::child_recovery::Retirement>>}
impl CleanupStep {
    pub closed spec fn data(&self)->Option<Dispatch> {self.data@}
    pub closed spec fn retirement(&self)->Option<crate::lifecycle_state::native::runtime::child_recovery::Retirement> {self.retirement@}
}
impl<E:ScalarEffect+Copy> Component<E> {
    proof fn native_dispatch(&self,dispatch:Dispatch,child:SharedChild,ticket:crate::cleanup_journal::RestoreTicket)
        requires self.wf(),self.owner().core().cleanup_state().live(0),
            dispatch==Dispatch::Other(crate::cleanup_queue::completion::CleanupDispatch::Host {ticket,action:ChildCleanup::Native(child)}),
            dispatch.from_slot(self.owner().core().cleanup_state().queues()[0].slots()),
        ensures child.wf(),ticket.token>=self.root().len(),ticket.token-self.root().len()<self.children().len(),
            self.children()[ticket.token-self.root().len()]==child,
            self.owner().histories()[0].initial()[ticket.token as int]==Some(ChildCleanup::Native(child)),
    {
        self.outcome.run.owner.facts();
        let slots=self.owner().core().cleanup_state().queues()[0].slots();
        assert(slots[ticket.token as int]==Some(ChildCleanup::Native(child)));
        assert(self.owner().histories()[0].current()==slots);
        assert(self.owner().histories()[0].initial()[ticket.token as int]==Some(ChildCleanup::Native(child)));
        if ticket.token<self.root().len() {assert(self.root()[ticket.token as int].in_slot(self.owner().histories()[0].initial()[ticket.token as int]));}
        let index=ticket.token-self.root().len();
        assert(self.children()[index]==child);
        assert(self.children()[index].wf());
    }
    /// Complete a native Child inverse only from the actual retirement result.
    /// A failed retirement retains that exact handle with RetainFailure. The
    /// child's later Unload remains a distinct lifecycle obligation.
    pub fn cleanup_next<P>(&mut self,session:&mut super::replay::Session<P,E>)->(out:Result<Option<CleanupStep>,crate::cleanup_journal::RestoreError>)
        requires old(self).wf(),old(session).wf(),
        ensures final(self).wf(),final(session).wf(),final(self).root()==old(self).root(),final(self).children()==old(self).children(),
            final(self).owner().same_inverse_word(&old(self).owner()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().data().is_some() ==>
                out->Ok_0.unwrap().data().unwrap().managed() && out->Ok_0.unwrap().data().unwrap().authentic(),
    {
        let ghost prior=*self;
        if !self.outcome.run.owner.execution().contains(0) {return Ok(None);}
        let dispatched=self.outcome.run.owner.dispatch(0);
        proof {self.frame(&prior);}
        let dispatch=match dispatched {Ok(Some(d))=>d,Ok(None)=>return Ok(None),Err(e)=>return Err(e)};
        let ghost observed=dispatch;
        use crate::cleanup_queue::completion::{CleanupDispatch,CleanupPolicy};
        match dispatch {
            Dispatch::Other(CleanupDispatch::Host {ticket,action:ChildCleanup::Native(child)})=>{
                proof {prior.native_dispatch(observed,child,ticket);}
                let (transition,Tracked(retirement))=session.retire_child(&child);
                let result=match transition.result {Ok(_)=>Ok(()),Err(e)=>Err(e)};
                let retry=if result.is_err() {Some(managed::interleaving::history::lifecycle::callbacks::HostAction::Native(child))} else {None};
                let acknowledged=self.outcome.run.owner.complete_result(0,ticket,result,retry,CleanupPolicy::RetainFailure).is_ok();
                proof {self.frame(&prior);}
                Ok(Some(CleanupStep {status:CleanupStatus::Child {ticket,result,acknowledged},data:Ghost(None),retirement:Tracked(retirement)}))
            },
            Dispatch::Other(CleanupDispatch::Value {ticket,completion})=>{
                let restored=completion.restored.is_some();
                Ok(Some(CleanupStep {status:CleanupStatus::Data {ticket,restored},data:Ghost(Some(observed)),retirement:Tracked(None)}))
            },
            Dispatch::Payload(completion)=>{
                let ticket=completion.ticket;let restored=completion.restored.is_some();
                Ok(Some(CleanupStep {status:CleanupStatus::Data {ticket,restored},data:Ghost(Some(observed)),retirement:Tracked(None)}))
            },
            Dispatch::Other(CleanupDispatch::Host {ticket:_ticket,action:_action})=>{
                proof {
                    prior.outcome.run.owner.facts();
                    let slots=prior.owner().histories()[0].initial();
                    assert(observed.from_slot(prior.owner().core().cleanup_state().queues()[0].slots()));
                    assert(slots[_ticket.token as int]==Some(_action));
                    if _ticket.token<prior.root().len() {
                        assert(prior.root()[_ticket.token as int].in_slot(slots[_ticket.token as int]));
                    } else {assert(slots[_ticket.token as int]==Some(ChildCleanup::Native(prior.children()[_ticket.token-prior.root().len()])));}
                    assert(false);
                }
                panic!("sealed component has no external cleanup action")
            },
        }
    }
    pub fn begin_cleanup<P>(&mut self,session:&mut super::replay::Session<P,E>,retiring:bool)->(out:Result<crate::action_ledger::ActionTicket,crate::Error>)
        requires old(self).wf(),old(session).wf(),ensures final(self).wf(),final(session).wf(),
    {let ghost prior=*self;let out=session.begin_cleanup(self.outcome.run.id,&mut self.outcome.run.owner,retiring);proof {self.frame(&prior);}out}
    pub fn resume_cleanup<P>(&self,session:&mut super::replay::Session<P,E>)->(out:Result<crate::action_ledger::ActionTicket,crate::Error>)
        requires self.wf(),old(session).wf(),ensures final(session).wf(),
    {session.resume_cleanup(self.outcome.run.id,&self.outcome.run.owner)}
    pub fn fail_cleanup<P>(&self,session:&mut super::replay::Session<P,E>)->(out:Result<(),crate::Error>)
        requires self.wf(),old(session).wf(),ensures final(session).wf(),
    {session.fail_cleanup(self.outcome.run.id,&self.outcome.run.owner)}
    pub fn retry_cleanup<P>(&mut self,session:&mut super::replay::Session<P,E>)->(out:Result<crate::action_ledger::ActionTicket,crate::Error>)
        requires old(self).wf(),old(session).wf(),ensures final(self).wf(),final(session).wf(),
    {let ghost prior=*self;let out=session.retry_cleanup(self.outcome.run.id,&mut self.outcome.run.owner);proof {self.frame(&prior);}out}
    pub fn release<P>(&mut self,session:&mut super::replay::Session<P,E>)->(out:Result<(),crate::Error>)
        requires old(self).wf(),old(session).wf(),ensures final(self).wf(),final(session).wf(),
    {
        let ghost prior=*self;
        let out=session.release(self.outcome.run.id,&mut self.outcome.run.owner);
        proof {self.frame(&prior);}
        match out {Ok(released)=>released.0.map(|_|()),Err(e)=>Err(e)}
    }
}

}

pub(crate) mod accumulator;

pub mod source;
