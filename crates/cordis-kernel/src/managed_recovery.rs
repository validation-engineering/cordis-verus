//! Recovery inputs derived from authentic heterogeneous function histories.
//! Allocation addresses, not service names, identify shared inverse domains.
#[cfg(verus_keep_ghost)]
use super::{histories_recorded, Call, ResultStep, Slot};
use super::{Report, Step};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{effect::ScalarEffect, joint, payload};
#[cfg(verus_keep_ghost)]
use crate::{lifecycle_state::services::NativeEpisode, Port};
use vstd::prelude::*;

verus! {
/// The actual interval contains no change to this allocation. Rejected
/// scalar attempts are allowed, as are all commits to unrelated objects.
pub open spec fn quiet(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat)->bool {
    start<=end<=frames.len() && forall|i:int| start<=i<end ==> {
        let e=#[trigger] frames[i].event;
        e.key!=key || joint::state_at(frames,i as nat).contains_pair(key,e.after)
    }
}
pub(crate) proof fn frame_update(frames:Seq<joint::Frame>,n:nat)
    requires joint::valid(frames),n<frames.len(),
    ensures joint::state_at(frames,n+1)==joint::state_at(frames,n).insert(frames[n as int].event.key,frames[n as int].event.after),
        joint::step(joint::state_at(frames,n),frames[n as int].state,frames[n as int].event),
{assert(joint::step(joint::state_at(frames,n),frames[n as int].state,frames[n as int].event));}
pub proof fn quiet_record(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat)
    requires joint::valid(frames),quiet(frames,start,end,key),joint::state_at(frames,start).contains_key(key),
    ensures joint::state_at(frames,end).contains_pair(key,joint::state_at(frames,start)[key]),
    decreases end-start,
{
    hide(joint::valid);hide(joint::step);
    if start<end {
        quiet_record(frames,start,(end-1) as nat,key);
        let i=(end-1) as int;
        frame_update(frames,i as nat);
    }
}
impl<T:?Sized> Step<T> {
    pub open spec fn recorded_values(&self)->bool {
        let r=self.write();let input=joint::state_at(r.events(),r.at());
        r.wf() && r.same(&self.forward_inverse().write()) && input.contains_key(r.event().key) && match self.result {
            ResultStep::Scalar {inverse,..}=>inverse@.recorded()
                && r.event().after is Object && input[r.event().key] is Object
                && r.event().after->Object_state==inverse@.state().after
                && input[r.event().key]->Object_state==inverse@.state().before,
            ResultStep::Payload(a)=>a.inverse().wf()
                && r.event().after==(joint::Record::Payload {source:a.inverse().owner().source(),revision:a.inverse().after().revision})
                && input[r.event().key]==(joint::Record::Payload {source:a.inverse().owner().source(),revision:a.inverse().before().revision}),
        }
    }
    pub proof fn record_values<E:ScalarEffect,M>(&self,call:Call<E,T>,port:Port,episode:NativeEpisode<Slot<T,M>>)
        requires self.corresponds(call,port,episode),ensures self.recorded_values(),
    {
        hide(joint::valid);hide(joint::step);
        reveal(Step::corresponds);
        if let ResultStep::Payload(a)=self.result {a.inverse().provenance();a.inverse().source_history();}
        self.write().transition();frame_update(self.write().events(),self.write().at());
        reveal(joint::step);reveal(joint::changes);
    }
}
/// An actual later typed input can return to the earlier semantic head while
/// its anti-stale revision advances. The head alone supplies no value equality;
/// linked_pair derives that equality from the retained source witnesses.
pub open spec fn restored_head<T:?Sized>(earlier:Step<T>,later:Step<T>)->bool {
    match (earlier.result,later.result) {
        (ResultStep::Payload(a),ResultStep::Payload(b))=>a.inverse().after().state().head==b.inverse().before().state().head,
        _=>false,
    }
}
pub open spec fn gap<T:?Sized>(earlier:Step<T>,later:Step<T>)->bool {
    quiet(later.write().events(),earlier.write().at()+1,later.write().at(),earlier.address().key)
        || restored_head(earlier,later)
}
impl<T:?Sized> Report<T> {
    /// Histories agree even for two distinct service names selecting the same
    /// typed owner. Numeric keys in different Journals remain different.
    pub proof fn linked_pair(&self,i:int,j:int)
        requires self.witnessed(),self.ordered(),crate::reversible_value::history::compatible(self.histories@),0<=i<j<self.steps.len(),
            self.steps@[i].recorded_values(),self.steps@[j].recorded_values(),
            self.steps@[i].address()==self.steps@[j].address(),gap(self.steps@[i],self.steps@[j]),
        ensures self.steps@[i].after()==self.steps@[j].before(),
    {
        hide(joint::valid);hide(joint::step);
        let a=self.steps@[i];let b=self.steps@[j];let ar=a.write();let br=b.write();let frames=br.events();let key=ar.event().key;
        reveal(histories_recorded);
        assert(br.follows(&ar));br.included(&ar);frame_update(frames,ar.at());
        assert(joint::state_at(frames,ar.at()+1)[key]==ar.event().after);
        let unchanged=quiet(frames,ar.at()+1,br.at(),key);
        if unchanged {quiet_record(frames,ar.at()+1,br.at(),key);}
        match (&a.result,&b.result) {
            (ResultStep::Payload(x),ResultStep::Payload(y))=>{
                x.inverse().provenance();y.inverse().provenance();x.inverse().source_history();y.inverse().source_history();
                joint::payload::retained(frames,ar.at()+1,br.at(),key);
                assert(x.inverse().after().revision<=y.inverse().before().revision);
                assert(x.inverse().owner().source()==y.inverse().owner().source());
                assert(histories_recorded(self.steps@,self.histories@));
                assert(self.histories@.contains_key(i) && self.histories@.contains_key(j));
                assert(crate::reversible_value::history::agree(self.histories@,i,j));
                assert(y.inverse().after().states.take(x.inverse().after().states.len() as int)==x.inverse().after().states);
                if unchanged {
                    assert(x.inverse().after().revision==y.inverse().before().revision);
                    assert(y.inverse().before().states =~= x.inverse().after().states);
                } else {
                    assert(restored_head(a,b));
                    let head=x.inverse().after().state().head as int;
                    assert(y.inverse().before().states[head]==y.inverse().after().states[head]);
                    assert(y.inverse().after().states[head]==x.inverse().after().states[head]);
                    assert(y.inverse().before().state()==x.inverse().after().state());
                }
            },_=>{},
        }
    }
    #[verifier::opaque]
    pub open spec fn recovery_history(&self)->bool {
        (forall|i:int|0<=i<self.steps.len() ==> (#[trigger] self.steps@[i]).recorded_values())
        && forall|i:int,j:int|#![trigger self.steps@[i],self.steps@[j]] 0<=i<j<self.steps.len()
            && self.steps@[i].address()==self.steps@[j].address() && gap(self.steps@[i],self.steps@[j])
            ==> self.steps@[i].after()==self.steps@[j].before()
        && forall|i:int,j:int|#![trigger self.steps@[i],self.steps@[j]] 0<=i<j<self.steps.len()
            && self.steps@[i].address()==self.steps@[j].address() && restored::interference(self.steps@[i],self.steps@[j])
            ==> exists|index:nat|restored::origin(self.steps@[i],self.steps@[j],index)
    }
    /// Called by the real interpreter for both normal and failed prefixes.
    /// No desired input heap, composable stack or inverse success is supplied.
    pub proof fn establish_recovery<E:ScalarEffect,M>(tracked &self,code:Seq<Call<E,T>>,ports:Seq<Port>,episode:NativeEpisode<Slot<T,M>>)
        requires self.certified(code,ports,episode),self.ordered(),ensures self.recovery_history(),
    {
        crate::reversible_value::history::compatible_map(self.histories.borrow());
        assert forall|i:int|0<=i<self.steps.len() implies (#[trigger] self.steps@[i]).recorded_values() by {
            self.steps@[i].record_values(code[self.steps@[i].pc as int],ports[self.steps@[i].pc as int],episode);
        }
        assert forall|i:int,j:int|#![trigger self.steps@[i],self.steps@[j]] 0<=i<j<self.steps.len()
            && self.steps@[i].address()==self.steps@[j].address() && gap(self.steps@[i],self.steps@[j])
            implies self.steps@[i].after()==self.steps@[j].before() by {self.linked_pair(i,j);}
        assert forall|i:int,j:int|#![trigger self.steps@[i],self.steps@[j]] 0<=i<j<self.steps.len()
            && self.steps@[i].address()==self.steps@[j].address() && restored::interference(self.steps@[i],self.steps@[j])
            implies exists|index:nat|restored::origin(self.steps@[i],self.steps@[j],index) by {
            let index=restored::between(self.steps@[i],self.steps@[j]);
        }
        reveal(Report::recovery_history);
    }
}
}

#[path = "managed_recovery_word.rs"]
pub mod word;

#[path = "managed_restored.rs"]
pub mod restored;
