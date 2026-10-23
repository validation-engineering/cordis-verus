//! Source-derived typed inputs, fresh version names and atomic native landing.
//! A cursor belongs to an actual Bank allocation. No source revision is copied
//! into the target, and every successful write retains its real cleanup inverse.
use super::super::{Effect, Owner, ResultStep, Step};
use super::{
    bank::Bank,
    batch::Provider,
    inputs::{Input, Operand, Seed},
    selection, Source,
};
use crate::reversible_value::{effect::ScalarEffect, native_payload, payload};
use crate::versioned_value::ReplaceError;
use vstd::prelude::*;

verus! {
pub open spec fn injective(names:Map<u64,u64>)->bool {
    forall|a:u64,b:u64|names.contains_key(a) && names.contains_key(b) && #[trigger] names[a]==#[trigger] names[b] ==> a==b
}
pub open spec fn related<T:?Sized>(names:Map<u64,u64>,a:payload::State<T>,b:payload::State<T>)->bool {
    a.value==b.value && a.depth==b.depth && names.contains_pair(a.head,b.head)
}
pub open spec fn bounded(names:Map<u64,u64>,source:u64,target:u64)->bool {
    forall|head:u64|#[trigger] names.contains_key(head) ==> head<=source && names[head]<=target
}
pub proof fn extend(names:Map<u64,u64>,source:u64,target:u64,a:u64,b:u64)
    requires injective(names),bounded(names,source,target),source<a,target<b,
    ensures injective(names.insert(a,b)),bounded(names.insert(a,b),a,b),
        forall|key:u64|#[trigger] names.contains_key(key) ==> names.insert(a,b).contains_pair(key,names[key]),
{
    assert forall|x:u64,y:u64|names.insert(a,b).contains_key(x) && names.insert(a,b).contains_key(y)
        && #[trigger] names.insert(a,b)[x]==#[trigger] names.insert(a,b)[y] implies x==y by {
        if x==a && y!=a {assert(names[y]<=target);} else if y==a && x!=a {assert(names[x]<=target);}
    }
}
/// Strict inverse domains agree on every related state, including old heads.
/// Equality of payload bytes alone would not establish this result.
pub proof fn inverse<T:?Sized>(names:Map<u64,u64>,source:payload::restoration::Inverse<T>,target:payload::restoration::Inverse<T>,a:payload::State<T>,b:payload::State<T>)
    requires injective(names),source.wf(),target.wf(),
        related(names,source.before().state(),target.before().state()),
        related(names,source.after().state(),target.after().state()),related(names,a,b),
    ensures source.undo(a).is_some()==target.undo(b).is_some(),
        source.undo(a).is_some() ==> related(names,source.undo(a).unwrap(),target.undo(b).unwrap()),
{
    if target.undo(b).is_some() {assert(names[a.head]==names[source.after().state().head]);assert(a.head==source.after().state().head);}
}
#[derive(Debug)]
#[allow(inconsistent_fields)]
pub enum Error {
    Missing,Scalar,OutstandingHistory,Retired,ChangedVersion,SourceChanged,SourceOrder,WrongObject,
    Capture(native_payload::CaptureError),Selection(selection::Error),Landing(ReplaceError),
    TargetClock {source:u64,target:u64},
}
struct Checkpoint<T:?Sized> {source:Input<T>,initial:bool,target:payload::Capture<T>}
impl<T:?Sized> Checkpoint<T> {
    spec fn source(&self)->payload::Observation<T> {
        let inverse=self.source.source().result->Payload_0.inverse();if self.initial {inverse.before()} else {inverse.after()}
    }
    spec fn wf(&self,names:Map<u64,u64>,owner:payload::SharedPayload<T>,address:crate::reversible_value::service_composition::Address,namespace:vstd::resource::Loc)->bool {
        self.source.wf() && self.source.source().result is Payload && self.target.wf() && self.target.owner()==owner
            && self.source.source().address()==address && self.source.identity_spec().namespace()==namespace
            && related(names,self.source().state(),self.target.observation().state())
    }
}
#[allow(dead_code)] // The version map erases; real captures and source operands do not.
pub struct Cursor<T:?Sized> {entry:usize,last:Input<T>,initial:bool,target:payload::Capture<T>,names:Ghost<Map<u64,u64>>,history:Vec<Checkpoint<T>>}
impl<T:?Sized> Cursor<T> {
    pub closed spec fn last_input(&self)->Input<T> {self.last}
    pub closed spec fn entry(&self)->usize {self.entry}
    pub closed spec fn names(&self)->Map<u64,u64> {self.names@}
    pub closed spec fn target(&self)->payload::Capture<T> {self.target}
    pub closed spec fn source(&self)->payload::Observation<T> {
        let inverse=self.last.source().result->Payload_0.inverse();if self.initial {inverse.before()} else {inverse.after()}
    }
    pub closed spec fn wf(&self)->bool {
        self.last.wf() && self.last.source().result is Payload && self.source().wf() && self.target.wf()
            && related(self.names(),self.source().state(),self.target.observation().state())
            && self.target.revision_spec()<=self.source().revision
            && injective(self.names()) && bounded(self.names(),self.source().revision,self.target.revision_spec())
            && forall|i:int|0<=i<self.history.len() ==> (#[trigger] self.history@[i]).wf(self.names(),self.target.owner(),self.last.source().address(),self.last.identity_spec().namespace())
    }
    pub open spec fn belongs(&self,bank:&Bank<T>)->bool {
        self.entry()<bank.len_spec() && bank.target(self.entry() as int) is Payload
            && self.target().owner()==bank.target(self.entry() as int)->Payload_0
            && self.last_input().source().address()==bank.address(self.entry() as int)
    }
    /// The retained first operand and the target's actual zero-revision read
    /// establish initial correspondence. Existing inverse debt is never invented.
    #[verifier::rlimit(8)]
    pub fn start(bank:&Bank<T>,entry:usize)->(out:Result<Self,Error>)
        requires bank.wf(),
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.belongs(bank) && out->Ok_0.entry()==entry,
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        let first=match bank.first_input(entry) {Some(input)=>input,None=>return Err(Error::Missing)};
        let _head=match first.operand() {Operand::Payload {head,depth,..}=>{if *depth!=0 {return Err(Error::OutstandingHistory);}*head},_=>return Err(Error::Scalar)};
        let seed=match bank.seed(entry) {Some(Seed::Payload(seed))=>seed,_=>return Err(Error::Scalar)};
        let target=match seed.capture() {Some(c)=>c,None=>return Err(Error::Retired)};
        if target.revision()!=0 {return Err(Error::ChangedVersion);}
        proof {target.initial_state();first.provenance();
            let original=first.source().result->Payload_0.inverse();original.provenance();original.source_history();
            assert(original.before().state().head==_head);
            assert(original.before().state().depth==0);
            assert(original.before().value==target.observation().state().value);
        }
        let history=vec![Checkpoint {source:first.duplicate(),initial:true,target:target.duplicate()}];
        Ok(Self {entry,last:first.duplicate(),initial:true,target,names:Ghost(Map::empty().insert(_head,0)),history})
    }
    fn checkpoint(&self,input:&Input<T>)->(out:Option<usize>)
        requires self.wf(),input.wf(),input.identity_spec().namespace()==self.last_input().identity_spec().namespace(),
        ensures out.is_some() ==> out.unwrap()<self.history.len()
            && input.source().before() is Payload
            && input.source().before()->Payload_0==self.history@[out.unwrap() as int].source().state(),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        let mut i=0;
        while i<self.history.len()
            invariant self.wf(),input.wf(),input.identity_spec().namespace()==self.last_input().identity_spec().namespace(),i<=self.history.len(),
            decreases self.history.len()-i,
        {
            let previous=&self.history[i];
            let same=if previous.initial {input.same_payload_before(&previous.source)==Some(true)} else {input.continues_payload(&previous.source)==Some(true)};
            if same {return Some(i);}
            i+=1;
        }
        None
    }
    /// Actual numeric versions are diagnostic only; target revisions are issued
    /// by target storage and checked atomically by native Capture::land.
    pub fn target_revision(&self)->(out:u64) ensures out==self.target().revision_spec(), {self.target.revision()}
    /// Apply one preserved source instruction through native admission and the
    /// original cleanup queue. All input/identity checks precede the write.
    #[verifier::rlimit(12)]
    #[allow(clippy::too_many_arguments)] // The call and its real publication/cleanup owners are retained.
    pub fn apply<C,G,A,R,X,E:ScalarEffect+Copy>(&mut self,source:&Source<E,T>,position:usize,execution:&mut Owner<C,G,A,R,T,(),X>,id:usize,bank:&Bank<T>,providers:&[Provider<E,T>])
        ->(out:Result<Step<T>,Error>)
        requires old(self).wf(),old(self).belongs(bank),bank.wf(),source.wf(),old(execution).wf(),
            old(execution).value_state().is_some(),old(execution).value_state().unwrap().provisions().len()==0,
            selection::providers_match(bank,providers@,old(execution).value_state().unwrap().capture().sources),
            old(self).last_input().identity_spec().namespace()==bank.namespace(),
            forall|i:int|0<=i<source.input_spec().len() ==> (#[trigger] source.input_spec()[i]).identity_spec().namespace()==bank.namespace(),
        ensures final(self).wf(),final(self).belongs(bank),final(execution).wf(),
            final(self).entry()==old(self).entry(),
            final(execution).value_state()==old(execution).value_state(),
            out.is_err() ==> *final(self)==*old(self) && *final(execution)==*old(execution),
            out.is_err() && out->Err_0 is Landing ==> out->Err_0->Landing_0!=ReplaceError::Capacity,
            out.is_ok() ==> {
                let a=source.original().result->Ok_0.steps@[position as int];let b=out->Ok_0;
                &&& position<source.original().result->Ok_0.steps.len()
                &&& a.result is Payload && b.result is Payload && b.pc==a.pc && b.next==a.next
                &&& b.corresponds(source.program().code()[b.pc as int],source.original().ports@[b.pc as int],old(execution).value_state().unwrap())
                &&& final(execution).cleanup_state().live(id)
                &&& b.token()<final(execution).cleanup_state().queues()[id].slots().len()
                &&& b.in_slot(final(execution).cleanup_state().queues()[id].slots()[b.token() as int])
                &&& bank.mapping().contains_pair(a.address(),b.address())
                &&& related(final(self).names(),a.before()->Payload_0,b.before()->Payload_0)
                &&& related(final(self).names(),a.after()->Payload_0,b.after()->Payload_0)
                &&& forall|head:u64|#[trigger] old(self).names().contains_key(head) ==> final(self).names().contains_pair(head,old(self).names()[head])
            },
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        reveal(Source::input_spec);
        if position>=source.inputs.len() {return Err(Error::Missing);}
        proof {assert(source.input_spec()[position as int]==source.inputs@[position as int]);
            assert(source.inputs@[position as int].identity_spec().namespace()==bank.namespace());}
        let input=&source.inputs[position];
        if !matches!(input.operand(),Operand::Payload {..}) {return Err(Error::Scalar);}
        let pc=input.pc();let call=&source.function.code[pc];
        let value=match &call.effect {Effect::Replace(value)=>value.clone(),_=>return Err(Error::Scalar)};
        let index=match bank.find(input) {Some(index)=>index,None=>return Err(Error::WrongObject)};
        if index!=self.entry {return Err(Error::WrongObject);}
        let checkpoint=match self.checkpoint(input) {Some(i)=>i,None=>return Err(Error::SourceChanged)};
        let head=match input.payload_after_head() {Some(head)=>head,None=>{assert(false);panic!("typed input")}};
        let old_head=match self.last.payload_after_head() {Some(head)=>head,None=>{assert(false);panic!("typed cursor")}};
        let revision=if self.initial {old_head-1} else {old_head};
        proof {self.last.provenance();self.last.source().result->Payload_0.inverse().source_history();assert(revision==self.source().revision);}

        if head-1<revision {return Err(Error::SourceOrder);}
        let capture=match execution.capture_native_payload(id,source.ports[pc]) {Ok(c)=>c,Err(e)=>return Err(Error::Capture(e))};
        if let Err(e)=selection::check_payload_capture(bank,providers,index,&capture) {return Err(Error::Selection(e));}
        let current=capture.observation();
        if current.revision()<self.target.revision() {return Err(Error::ChangedVersion);}
        if current.revision()>head-1 {return Err(Error::TargetClock {source:head-1,target:current.revision()});}
        if !current.same_head(&self.history[checkpoint].target) {return Err(Error::ChangedVersion);}
        proof {
            capture.provenance();source.facts();input.provenance();
            let inverse=input.source().result->Payload_0.inverse();inverse.provenance();inverse.source_history();
            assert(input.source().before()->Payload_0==self.history@[checkpoint as int].source().state());
            assert(inverse.before().revision==head-1);
            assert(self.source().revision<=inverse.before().revision);
            assert(inverse.after().revision as int+inverse.after().state().depth as int<=u64::MAX);
            assert(self.target.revision_spec()<=inverse.before().revision);
            assert(capture.payload().observation().state()==self.history@[checkpoint as int].target.observation().state());
            assert(related(self.names(),inverse.before().state(),capture.payload().observation().state()));
            assert(capture.payload().revision_spec() as int+capture.payload().observation().state().depth as int+2<=u64::MAX);
        }
        let ghost source_inverse=input.source().result->Payload_0.inverse();
        let (admission,next)=match capture.land(execution,id,value) {Ok(pair)=>pair,Err((error,_,_))=>return Err(Error::Landing(error))};
        let step=Step {pc,result:ResultStep::Payload(admission),next:call.branch.matched};
        proof {
            let inverse=step.result->Payload_0.inverse();inverse.provenance();inverse.source_history();
            extend(self.names(),self.source().revision,self.target.revision_spec(),source_inverse.after().revision,inverse.after().revision);
            reveal(super::super::Step::corresponds);
            assert(step.corresponds(*call,source.ports@[pc as int],capture.episode()));
            step.interpretation(*call,source.ports@[pc as int],capture.episode());
            step.record_values(*call,source.ports@[pc as int],capture.episode());
            bank.mapping_entry(index as int);
        }
        let ghost names=self.names().insert(source_inverse.after().revision,step.result->Payload_0.inverse().after().revision);
        proof {
            assert forall|i:int|0<=i<self.history.len() implies (#[trigger] self.history@[i]).wf(names,self.target.owner(),self.last.source().address(),self.last.identity_spec().namespace()) by {
                let previous=self.history@[i];assert(self.names().contains_key(previous.source().state().head));
            }
        }
        self.last=input.duplicate();self.initial=false;self.target=next.observation().duplicate();self.names=Ghost(names);
        self.history.push(Checkpoint {source:input.duplicate(),initial:false,target:self.target.duplicate()});
        proof {
            assert(related(names,source_inverse.before().state(),step.result->Payload_0.inverse().before().state()));
            assert(related(names,source_inverse.after().state(),step.result->Payload_0.inverse().after().state()));
            assert(self.wf());
            assert(step.pc==input.source().pc && step.next==input.source().next);
            assert(step.corresponds(source.program().code()[step.pc as int],source.original().ports@[step.pc as int],old(execution).value_state().unwrap()));
            assert(execution.cleanup_state().live(id));
            assert(step.in_slot(execution.cleanup_state().queues()[id].slots()[step.token() as int]));
            assert(bank.mapping().contains_pair(input.source().address(),step.address()));
        }
        Ok(step)
    }
}
}
