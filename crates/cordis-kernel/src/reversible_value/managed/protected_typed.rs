//! Typed storage retained by the original managed function interpreter.
//! States and versions below describe actual write guards, not copied values.
#[cfg(verus_keep_ghost)]
use super::{Call, Step};
use super::{Effect, Owner, Slot};
#[cfg(verus_keep_ghost)]
use crate::cleanup_groups::payload as cleanup;
use crate::cleanup_groups::payload::{AccessError, Admission};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::services::NativeEpisode;
use crate::reversible_value::payload;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, service_composition::Address};
use crate::Port;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[allow(dead_code)] // Provider and port are erased episode-selection evidence.
pub(crate) struct Binding {pub provider:Ghost<usize>,pub port:Ghost<Port>,pub entry:usize}
pub(crate) struct Context<'a,T:?Sized,M> {
    cells:Vec<Option<payload::protected::Exclusive<'a,T>>>,
    slots:Vec<Arc<Slot<T,M>>>,bindings:Vec<Binding>,
}
#[derive(Debug)]
pub enum Error {Retired {entry:usize},Capacity {entry:usize},Binding {pc:usize},NotTyped,ChangedVersion {entry:usize},OutstandingHistory {entry:usize},SourceAllocation {step:usize},SourceState {step:usize}}
#[verifier::opaque]
pub open spec fn typed_only<E,T:?Sized>(code:Seq<Call<E,T>>)->bool {
    forall|i:int|0<=i<code.len() ==> (#[trigger] code[i]).effect is Replace
}
impl<E,T:?Sized> super::Function<E,T> {
    pub fn is_typed_only(&self)->(out:bool) ensures out==typed_only(self.code()),
    {
        reveal(typed_only);
        let mut i=0;
        while i<self.code.len()
            invariant i<=self.code.len(),forall|j:int|0<=j<i ==> (#[trigger] self.code()[j]).effect is Replace,
            decreases self.code.len()-i,
        {if !matches!(&self.code[i].effect,Effect::Replace(_)) {proof {reveal(typed_only);assert(!(self.code()[i as int].effect is Replace));}return false;}i+=1;}true
    }
}
#[verifier::opaque]
pub(crate) open spec fn after<T:?Sized>(initial:Seq<payload::State<T>>,routes:Seq<usize>,steps:Seq<Step<T>>)->Seq<payload::State<T>>
    decreases steps.len(),
{if steps.len()==0 {initial} else {let s=steps.last();after(initial,routes,steps.drop_last()).update(routes[s.pc as int] as int,s.after()->Payload_0)}}
#[verifier::opaque]
pub(crate) open spec fn clocks<T:?Sized>(initial:Seq<u64>,routes:Seq<usize>,steps:Seq<Step<T>>)->Seq<u64>
    decreases steps.len(),
{if steps.len()==0 {initial} else {let s=steps.last();clocks(initial,routes,steps.drop_last()).update(routes[s.pc as int] as int,s.result->Payload_0.inverse().after().revision)}}
#[verifier::opaque]
pub(crate) open spec fn execution<T:?Sized>(initial:Seq<payload::State<T>>,revisions:Seq<u64>,routes:Seq<usize>,steps:Seq<Step<T>>)->bool {
    forall|i:int|0<=i<steps.len() ==> {
        let s=#[trigger] steps[i];
        &&& s.result is Payload && s.pc<routes.len() && routes[s.pc as int]<initial.len() && revisions.len()==initial.len()
        &&& s.before()==super::semantics::Value::Payload(after(initial,routes,steps.take(i))[routes[s.pc as int] as int])
        &&& s.result->Payload_0.inverse().before().revision==clocks(revisions,routes,steps.take(i))[routes[s.pc as int] as int]
    }
}
pub(crate) proof fn empty<T:?Sized>(initial:Seq<payload::State<T>>,revisions:Seq<u64>,routes:Seq<usize>)
    ensures execution::<T>(initial,revisions,routes,Seq::empty()),after::<T>(initial,routes,Seq::empty())==initial,clocks::<T>(revisions,routes,Seq::empty())==revisions,
{reveal(execution);reveal(after);reveal(clocks);}
pub(crate) proof fn append<T:?Sized>(initial:Seq<payload::State<T>>,revisions:Seq<u64>,routes:Seq<usize>,steps:Seq<Step<T>>,s:Step<T>)
    requires execution(initial,revisions,routes,steps),s.result is Payload,s.pc<routes.len(),routes[s.pc as int]<initial.len(),revisions.len()==initial.len(),
        s.before()==super::semantics::Value::Payload(after(initial,routes,steps)[routes[s.pc as int] as int]),
        s.result->Payload_0.inverse().before().revision==clocks(revisions,routes,steps)[routes[s.pc as int] as int],
    ensures execution(initial,revisions,routes,steps.push(s)),
        after(initial,routes,steps.push(s))==after(initial,routes,steps).update(routes[s.pc as int] as int,s.after()->Payload_0),
        clocks(revisions,routes,steps.push(s))==clocks(revisions,routes,steps).update(routes[s.pc as int] as int,s.result->Payload_0.inverse().after().revision),
{
    reveal(execution);reveal(after);reveal(clocks);
    assert(steps.push(s).drop_last() =~= steps);
    assert forall|i:int|0<=i<steps.push(s).len() implies {
        let x=#[trigger] steps.push(s)[i];
        &&& x.result is Payload && x.pc<routes.len() && routes[x.pc as int]<initial.len() && revisions.len()==initial.len()
        &&& x.before()==super::semantics::Value::Payload(after(initial,routes,steps.push(s).take(i))[routes[x.pc as int] as int])
        &&& x.result->Payload_0.inverse().before().revision==clocks(revisions,routes,steps.push(s).take(i))[routes[x.pc as int] as int]
    } by {if i<steps.len() {assert(steps.push(s).take(i) =~= steps.take(i));} else {assert(steps.push(s).take(i) =~= steps);}}
}
#[verifier::opaque]
pub(crate) open spec fn addressed<T:?Sized>(targets:Seq<payload::SharedPayload<T>>,routes:Seq<usize>,steps:Seq<Step<T>>)->bool {
    forall|i:int|0<=i<steps.len() ==> {let s=#[trigger] steps[i];
        &&& s.pc<routes.len() && routes[s.pc as int]<targets.len()
        &&& s.address()==(Address {journal:targets[routes[s.pc as int] as int].journal_spec(),key:targets[routes[s.pc as int] as int].key()})}
}

pub(crate) proof fn typed_at<E,T:?Sized>(code:Seq<Call<E,T>>,pc:usize)
    requires typed_only(code),pc<code.len(),ensures code[pc as int].effect is Replace,
{reveal(typed_only);}
pub(crate) proof fn address_empty<T:?Sized>(targets:Seq<payload::SharedPayload<T>>,routes:Seq<usize>)
    ensures addressed::<T>(targets,routes,Seq::empty()),
{reveal(addressed);}
pub(crate) proof fn address_append<T:?Sized>(targets:Seq<payload::SharedPayload<T>>,routes:Seq<usize>,steps:Seq<Step<T>>,s:Step<T>)
    requires addressed(targets,routes,steps),s.pc<routes.len(),routes[s.pc as int]<targets.len(),
        s.address()==(Address {journal:targets[routes[s.pc as int] as int].journal_spec(),key:targets[routes[s.pc as int] as int].key()}),
    ensures addressed(targets,routes,steps.push(s)),
{reveal(addressed);assert forall|i:int|0<=i<steps.push(s).len() implies {let x=#[trigger] steps.push(s)[i];
    &&& x.pc<routes.len() && routes[x.pc as int]<targets.len()
    &&& x.address()==(Address {journal:targets[routes[x.pc as int] as int].journal_spec(),key:targets[routes[x.pc as int] as int].key()})} by {}}

#[allow(clippy::manual_while_let_some)]
fn release_cells<T:?Sized>(mut cells:Vec<Option<payload::protected::Exclusive<'_,T>>>)
    requires forall|i:int|0<=i<cells.len() ==> (#[trigger] cells@[i]).is_some() && cells@[i]->Some_0.wf(),
{
    while !cells.is_empty()
        invariant forall|i:int|0<=i<cells.len() ==> (#[trigger] cells@[i]).is_some() && cells@[i]->Some_0.wf(),
        decreases cells.len(),
    {cells.pop().unwrap().unwrap().release();}
}
impl<'a,T:?Sized,M> Context<'a,T,M> {
    pub(crate) closed spec fn targets(&self)->Seq<payload::SharedPayload<T>> {self.cells@.map(|_:int,x:Option<payload::protected::Exclusive<'a,T>>|x.unwrap().target())}
    pub(crate) closed spec fn states(&self)->Seq<payload::State<T>> {self.cells@.map(|_:int,x:Option<payload::protected::Exclusive<'a,T>>|x.unwrap().state().unwrap())}
    pub(crate) closed spec fn revisions(&self)->Seq<u64> {self.cells@.map(|_:int,x:Option<payload::protected::Exclusive<'a,T>>|x.unwrap().revision().unwrap())}
    pub(crate) closed spec fn slots(&self)->Seq<Arc<Slot<T,M>>> {self.slots@}
    pub(crate) closed spec fn bindings(&self)->Seq<Binding> {self.bindings@}
    pub(crate) closed spec fn routes(&self)->Seq<usize> {self.bindings@.map(|_:int,b:Binding|b.entry)}
    pub(crate) open spec fn shape(&self,old:&Self)->bool {self.targets()==old.targets() && self.slots()==old.slots() && self.bindings()==old.bindings() && self.routes()==old.routes()}
    pub(crate) closed spec fn wf(&self)->bool {
        self.cells.len()==self.slots.len()
            && (forall|i:int|0<=i<self.cells.len() ==> (#[trigger] self.cells@[i]).is_some() && self.cells@[i]->Some_0.wf()
                && self.cells@[i]->Some_0.state().is_some() && self.cells@[i]->Some_0.revision().is_some()
                && self.slots@[i].opaque_spec()==Some(self.cells@[i]->Some_0.target()))
            && (forall|i:int|0<=i<self.bindings.len() ==> (#[trigger] self.bindings@[i]).entry<self.cells.len())
    }
    #[verifier::opaque]
    pub(crate) open spec fn budget(&self,count:nat)->bool {
        forall|i:int|0<=i<self.states().len() ==> (#[trigger] self.revisions()[i]) as int+self.states()[i].depth as int+2*count<=u64::MAX
    }
    pub(crate) open spec fn for_call(&self,episode:NativeEpisode<Slot<T,M>>,pc:usize,port:Port)->bool {
        !episode.closed() && pc<self.bindings().len() && self.bindings()[pc as int].port@==port
            && episode.selects_value(self.bindings()[pc as int].provider@,port,self.slots()[self.bindings()[pc as int].entry as int])
    }
    #[verifier::opaque]
    pub(crate) open spec fn supports(&self,episode:NativeEpisode<Slot<T,M>>,ports:Seq<Port>)->bool {
        self.bindings().len()==ports.len() && forall|i:int|0<=i<ports.len() ==> self.for_call(episode,i as usize,#[trigger] ports[i])
    }

    pub(crate) proof fn supports_at(&self,episode:NativeEpisode<Slot<T,M>>,ports:Seq<Port>,pc:usize)
        requires self.supports(episode,ports),pc<ports.len(),
        ensures self.bindings().len()==ports.len(),self.for_call(episode,pc,ports[pc as int]),
    {reveal(Context::supports);}
    pub(crate) proof fn supports_frame(&self,prior:&Self,episode:NativeEpisode<Slot<T,M>>,ports:Seq<Port>)
        requires self.shape(prior),prior.supports(episode,ports),ensures self.supports(episode,ports),
    {reveal(Context::supports);}
    pub(crate) proof fn budget_at(&self,count:nat,index:int)
        requires self.budget(count),0<=index<self.states().len(),count>0,
        ensures self.revisions()[index] as int+self.states()[index].depth as int+2<=u64::MAX,
    {reveal(Context::budget);}
    pub(crate) proof fn consumed(&self,prior:&Self,count:nat,index:int,step:Step<T>)
        requires prior.budget(count),count>0,0<=index<prior.states().len(),step.result is Payload,step.result->Payload_0.inverse().wf(),
            prior.states()[index]==step.before()->Payload_0,prior.revisions()[index]==step.result->Payload_0.inverse().before().revision,
            self.states()==prior.states().update(index,step.after()->Payload_0),
            self.revisions()==prior.revisions().update(index,step.result->Payload_0.inverse().after().revision),
        ensures self.budget((count-1) as nat),
    {
        reveal(Context::budget);step.result->Payload_0.inverse().source_history();
        assert forall|i:int|0<=i<self.states().len() implies (#[trigger] self.revisions()[i]) as int+self.states()[i].depth as int+2*(count-1)<=u64::MAX by {
            assert(prior.revisions()[i] as int+prior.states()[i].depth as int+2*count<=u64::MAX);
        }
    }
    pub(crate) proof fn storage_facts(&self)
        requires self.wf(),ensures self.states().len()==self.targets().len(),self.revisions().len()==self.states().len(),self.slots().len()==self.targets().len(),
    {}
    pub(crate) proof fn call_facts(&self,pc:usize)
        requires self.wf(),pc<self.bindings().len(),
        ensures self.routes().len()==self.bindings().len(),self.states().len()==self.targets().len(),self.revisions().len()==self.states().len(),
            self.routes()[pc as int]<self.states().len(),
    {}
    pub(crate) fn acquire(values:&'a [payload::SharedPayload<T>],slots:Vec<Arc<Slot<T,M>>>)->(out:Result<Self,Error>)
        requires values.len()==slots.len(),forall|i:int|0<=i<slots.len() ==> (#[trigger] slots@[i]).opaque_spec()==Some(values@[i]),
            forall|i:int,j:int|0<=i<j<values.len() ==> values@[i]!=values@[j],
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.targets()==values@ && out->Ok_0.slots()==slots@ && out->Ok_0.bindings().len()==0,
    {
        let mut cells:Vec<Option<payload::protected::Exclusive<'a,T>>>=Vec::new();let mut i=0;
        while i<values.len()
            invariant i<=values.len(),cells.len()==i,values.len()==slots.len(),
                forall|j:int|0<=j<slots.len() ==> (#[trigger] slots@[j]).opaque_spec()==Some(values@[j]),
                forall|j:int|0<=j<cells.len() ==> (#[trigger] cells@[j]).is_some() && cells@[j]->Some_0.wf()
                    && cells@[j]->Some_0.state().is_some() && cells@[j]->Some_0.revision().is_some() && cells@[j]->Some_0.target()==values@[j],
            decreases values.len()-i,
        {
            let held=values[i].acquire_exclusive();
            if held.capture().is_none() {held.release();release_cells(cells);return Err(Error::Retired {entry:i});}
            cells.push(Some(held));i+=1;
        }
        let out=Self {cells,slots,bindings:Vec::new()};proof {assert(out.targets() =~= values@);}Ok(out)
    }
    pub(crate) fn capture(&self,entry:usize)->(out:payload::Capture<T>)
        requires self.wf(),entry<self.targets().len(),
        ensures out.wf(),out.owner()==self.targets()[entry as int],out.observation().state()==self.states()[entry as int],out.revision_spec()==self.revisions()[entry as int],
    {self.cells[entry].as_ref().unwrap().capture().unwrap()}
    pub(crate) fn route(&self,pc:usize)->(out:Option<usize>)
        requires self.wf(),ensures out.is_some()==(pc<self.routes().len()),
            out.is_some() ==> out.unwrap()==self.routes()[pc as int] && out.unwrap()<self.targets().len(),
    {if pc>=self.bindings.len() {None} else {Some(self.bindings[pc].entry)}}
    pub(crate) fn reserve(&self,count:usize)->(out:Result<(),Error>)
        requires self.wf(),ensures out.is_ok() ==> self.budget(count as nat),
    {
        reveal(Context::budget);
        let mut i=0;
        while i<self.cells.len()
            invariant self.wf(),i<=self.cells.len(),forall|j:int|0<=j<i ==> (#[trigger] self.revisions()[j]) as int+self.states()[j].depth as int+2*count<=u64::MAX,
            decreases self.cells.len()-i,
        {
            let capture=self.cells[i].as_ref().unwrap().capture().unwrap();
            let revision=capture.revision();let depth=capture.depth();
            if 2*(count as u128)+(revision as u128)+(depth as u128)>u64::MAX as u128 {return Err(Error::Capacity {entry:i});}
            i+=1;
        }Ok(())
    }
    pub(crate) fn bind(&mut self,bindings:Vec<Binding>)
        requires old(self).wf(),forall|i:int|0<=i<bindings.len() ==> (#[trigger] bindings@[i]).entry<old(self).targets().len(),
        ensures final(self).wf(),final(self).targets()==old(self).targets(),final(self).states()==old(self).states(),final(self).revisions()==old(self).revisions(),
            final(self).slots()==old(self).slots(),final(self).bindings()==bindings@,
    {self.bindings=bindings;}
    #[allow(clippy::type_complexity)]
    pub(crate) fn apply<C,G,A,R,X>(&mut self,owner:&mut Owner<C,G,A,R,T,M,X>,id:usize,pc:usize,_port:Port,value:Arc<T>,Tracked(cause):Tracked<&crate::reversible_value::registration::ReceiptMap>)->(out:Result<Admission<T>,(AccessError,Arc<T>,Ghost<Option<crate::reversible_value::payload::restoration::ForwardRejection<T>>>)>)
        requires old(self).wf(),old(owner).wf(),old(owner).value_state().is_some(),
            old(self).for_call(old(owner).value_state().unwrap(),pc,_port),crate::reversible_value::registration::witnesses(*cause),
        ensures final(self).wf(),final(self).shape(old(self)),
            out.is_err() ==> final(self).states()==old(self).states() && final(self).revisions()==old(self).revisions(),
            old(owner).work_state().accepts() && old(owner).cleanup_state().acquisition_open(id)
                && old(self).revisions()[old(self).routes()[pc as int] as int] as int+old(self).states()[old(self).routes()[pc as int] as int].depth as int+2<=u64::MAX ==> out.is_ok(),
            out.is_ok() ==> {
                let index=old(self).routes()[pc as int] as int;let inv=out->Ok_0.inverse();
                &&& inv.owner()==old(self).targets()[index]
                &&& inv.before().state()==old(self).states()[index] && inv.before().revision==old(self).revisions()[index]
                &&& final(self).states()==old(self).states().update(index,inv.after().state())
                &&& final(self).revisions()==old(self).revisions().update(index,inv.after().revision)
            },
            final(owner).cleanup_state().frame(&old(owner).cleanup_state(),id),
            final(owner).cleanup_state().queues().dom()==old(owner).cleanup_state().queues().dom(),
            final(owner).cleanup_state().domain_ids()==old(owner).cleanup_state().domain_ids(),
            old(owner).cleanup_state().live(id) ==> final(owner).cleanup_state().queues()[id].link()==old(owner).cleanup_state().queues()[id].link()
                && final(owner).cleanup_state().queues()[id].issued()==old(owner).cleanup_state().queues()[id].issued()
                && final(owner).cleanup_state().queues()[id].protocol().selected()==old(owner).cleanup_state().queues()[id].protocol().selected(),
            out.is_err() ==> cleanup::access_failed(old(owner).value_state(),old(owner).work_state().accepts() && old(owner).cleanup_state().acquisition_open(id),_port,out->Err_0.0,out->Err_0.2@),
            out.is_ok() ==> forall|k:(int,bool)|cause.contains_key(k) && #[trigger] cause[k].journal()==out->Ok_0.inverse().owner().journal_spec() ==> out->Ok_0.inverse().after().commit.follows(&cause[k]),
            final(owner).wf(),final(owner).execution_journal()==old(owner).execution_journal(),
            final(owner).cleanup_state().link()==old(owner).cleanup_state().link(),
            final(owner).work_state()==old(owner).work_state(),final(owner).value_state()==old(owner).value_state(),
            final(owner).capture()==old(owner).capture(),final(owner).phase_spec()==old(owner).phase_spec(),
            final(owner).value_attempts()==old(owner).value_attempts(),final(owner).status_links()==old(owner).status_links(),
            out.is_err() ==> *final(owner)==*old(owner) && out->Err_0.1==value,
            out.is_ok() ==> final(owner).cleanup_state().queues()[id].link()==old(owner).cleanup_state().queues()[id].link(),
            out.is_ok() ==> out->Ok_0.registered(final(owner).cleanup_state().queues()[id].link(),final(owner).cleanup_state().queues()[id].observation()),
            out.is_ok() ==> joint::groups::registration(out->Ok_0.registration_receipt(),final(owner).cleanup_state().link(),id),
            out.is_ok() ==> out->Ok_0.witnessed() && out->Ok_0.inverse().wf() && out->Ok_0.inverse().after().value==value
                && old(owner).value_state().is_some()
                && cleanup::selected(old(owner).value_state().unwrap(),_port,out->Ok_0.inverse().owner())
                && final(owner).cleanup_state().live(id) && final(owner).cleanup_state().acquisition_open(id)==old(owner).cleanup_state().acquisition_open(id)
                && out->Ok_0.token_spec()==old(owner).cleanup_state().queues()[id].slots().len()
                && final(owner).cleanup_state().queues()[id].slots().len()==old(owner).cleanup_state().queues()[id].slots().len()+1
                && final(owner).cleanup_state().queues()[id].slots().take(out->Ok_0.token_spec() as int)==old(owner).cleanup_state().queues()[id].slots()
                && final(owner).cleanup_state().queues()[id].protocol().waiting()==old(owner).cleanup_state().queues()[id].protocol().waiting().push(out->Ok_0.token_spec())
                && exists|retained:Arc<Slot<T,M>>| #[trigger] out->Ok_0.queued(final(owner).cleanup_state().queues()[id],retained)
                    && retained.opaque_spec()==Some(out->Ok_0.inverse().owner()),
    {
        proof {self.call_facts(pc);}
        let index=self.bindings[pc].entry;
        let retained=self.slots[index].clone();
        proof {assert(self.cells@[index as int].is_some());assert(retained.opaque_spec()==Some(self.cells@[index as int]->Some_0.target()));}
        let target=retained.opaque().unwrap().clone();
        proof {
            assert(target==self.targets()[index as int]);
            assert(cleanup::selected(owner.value_state().unwrap(),_port,target)) by {
                let episode=owner.value_state().unwrap();
                if !episode.provisions().contains(_port) {assert(episode.bindings().contains(crate::Binding {provider:self.bindings@[pc as int].provider@,key:_port.key,realm:_port.realm}));}
            }
        }
        let result=owner.apply_payload_captured_in(id,&target,None,value,retained,Tracked(cause),&mut self.cells[index]);
        proof {
            assert(self.targets() =~= old(self).targets());assert(self.routes() =~= old(self).routes());
            assert(self.states() =~= old(self).states().update(index as int,self.cells@[index as int]->Some_0.state().unwrap()));
            assert(self.revisions() =~= old(self).revisions().update(index as int,self.cells@[index as int]->Some_0.revision().unwrap()));
        }
        match result {Ok((a,_capture))=>{
            proof {a.inverse().provenance();}
            assert(a.queued(owner.cleanup_state().queues()[id],retained));
            assert(retained.opaque_spec()==Some(a.inverse().owner()));
            Ok(a)
        },Err((error,value,_retained,rejection))=>Err((AccessError::Value(error),value,rejection))}
    }
    pub(crate) fn release(self) requires self.wf(), {release_cells(self.cells);}
}
}

#[cfg(test)]
mod tests {
    use super::{Context, Error};
    use crate::reversible_value::{managed::Slot, payload::SharedPayload};
    use std::{
        sync::{mpsc, Arc},
        thread,
        time::Duration,
    };

    #[test]
    fn ordinary_typed_writes_wait_for_the_real_execution_scope() {
        let value = SharedPayload::new(Arc::new("old".to_owned()));
        let values = [value.clone()];
        let slots = vec![Arc::new(Slot::new_opaque(value.clone(), ()))];
        let held = Context::acquire(&values, slots).unwrap();
        let (ready_tx, ready_rx) = mpsc::channel();
        let (done_tx, done_rx) = mpsc::channel();
        let writer = thread::spawn(move || {
            ready_tx.send(()).unwrap();
            let ok = value.apply(Arc::new("new".to_owned())).is_ok();
            done_tx.send(ok).unwrap();
        });
        ready_rx.recv_timeout(Duration::from_secs(2)).unwrap();
        assert!(matches!(
            done_rx.recv_timeout(Duration::from_millis(50)),
            Err(mpsc::RecvTimeoutError::Timeout)
        ));
        held.release();
        assert!(done_rx.recv_timeout(Duration::from_secs(2)).unwrap());
        writer.join().unwrap();
    }

    #[test]
    fn retired_later_payload_releases_all_earlier_guards() {
        let first = SharedPayload::new(Arc::new("first".to_owned()));
        let retired = SharedPayload::new(Arc::new("retired".to_owned()));
        retired.retire().unwrap();
        let values = [first.clone(), retired.clone()];
        let slots = vec![
            Arc::new(Slot::new_opaque(first.clone(), ())),
            Arc::new(Slot::new_opaque(retired, ())),
        ];
        assert!(matches!(
            Context::acquire(&values, slots),
            Err(Error::Retired { entry: 1 })
        ));
        let (tx, rx) = mpsc::channel();
        let writer = thread::spawn(move || {
            tx.send(first.replace(Arc::new("usable".to_owned())).is_ok())
                .unwrap()
        });
        assert!(rx.recv_timeout(Duration::from_secs(2)).unwrap());
        writer.join().unwrap();
    }
}
