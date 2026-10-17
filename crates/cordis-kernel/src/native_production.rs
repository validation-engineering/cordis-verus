//! Total interpretation of a real native checkpoint, including every interleaved
//! record and pending inverse. Paper labels describe the control projection;
//! other observable changes retain their exact executable extension contracts.
use super::history::Snapshot;
use crate::refinement as r;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint;
use crate::reversible_value::joint::classification as c;
use vstd::prelude::*;
verus! {
pub enum Kind {Paper {actor:usize,rule:r::Rule},Restart {actor:usize},Internal,Extension {class:c::Class}}
pub open spec fn control(frames:Seq<joint::Frame>,index:nat,key:nat)->r::State {
    let state=joint::state_at(frames,index);
    if state.contains_key(key) && state[key] is Native {state[key]->Native_state.control}
    else {r::State {fibers:IMap::empty()}}
}
pub open spec fn label(frames:Seq<joint::Frame>,index:int,key:nat)->(usize,r::Rule) {
    let e=frames[index].event;
    if e.key==key && e.change is Native {(e.change->Native_actor,e.change->Native_rule)}
    else {(0,r::Rule::Stutter)}
}
pub open spec fn kind(frames:Seq<joint::Frame>,index:int,key:nat)->Kind {
    let e=frames[index].event;
    if c::at(frames,index as nat)==c::at(frames,(index+1) as nat) {Kind::Internal}
    else if e.key==key && e.change is Native && e.change->Native_rule!=r::Rule::Stutter {
        if e.change->Native_rule==r::Rule::Restart {Kind::Restart {actor:e.change->Native_actor}}
        else {Kind::Paper {actor:e.change->Native_actor,rule:e.change->Native_rule}}
    } else {Kind::Extension {class:c::class(e)}}
}
pub open spec fn controls(frames:Seq<joint::Frame>,key:nat)->Seq<r::State> {
    Seq::new(frames.len()+1,|i:int|control(frames,i as nat,key))
}
pub open spec fn labels(frames:Seq<joint::Frame>,key:nat)->Seq<(usize,r::Rule)> {
    Seq::new(frames.len(),|i:int|label(frames,i,key))
}
pub open spec fn base_only(frames:Seq<joint::Frame>,key:nat)->bool {
    forall|i:int|0<=i<frames.len() ==> label(frames,i,key).1!=r::Rule::Restart
}
#[verifier::opaque]
pub open spec fn classified(frames:Seq<joint::Frame>,index:int,key:nat)->bool {
    &&& c::classified(frames,index as nat)
    &&& r::labelled_step(control(frames,index as nat,key),control(frames,(index+1) as nat,key),label(frames,index,key),true)
    &&& (kind(frames,index,key) is Internal) == (c::at(frames,index as nat)==c::at(frames,(index+1) as nat))
    &&& match kind(frames,index,key) {
        Kind::Paper {actor,rule}=>rule!=r::Rule::Restart && rule!=r::Rule::Stutter
            && r::step(control(frames,index as nat,key),control(frames,(index+1) as nat,key),actor,rule),
        Kind::Restart {actor}=>r::step(control(frames,index as nat,key),control(frames,(index+1) as nat,key),actor,r::Rule::Restart),
        Kind::Internal=>c::stutters(c::at(frames,index as nat),c::at(frames,(index+1) as nat)),
        Kind::Extension {class}=>class==c::class(frames[index].event)
            && c::record_law(joint::state_at(frames,index as nat),joint::state_at(frames,(index+1) as nat),frames[index].event),
    }
}
#[verifier::opaque]
pub open spec fn interpreted(frames:Seq<joint::Frame>,key:nat)->bool {
    c::history(frames) && r::execution(controls(frames,key),labels(frames,key),true)
        && forall|i:int|0<=i<frames.len() ==> #[trigger] classified(frames,i,key)
}
impl<V> Snapshot<V> {
    pub proof fn production_step(&self,index:int)
        requires self.certified(),0<=index<self.joint_spec().events().len(),
        ensures classified(self.joint_spec().events(),index,self.key()),
    {
        self.valid_history();
        let frames=self.joint_spec().events();let key=self.key();let e=frames[index].event;
        self.joint_spec().valid_history();self.joint_spec().classified_step(index as nat);
        assert(joint::step(joint::state_at(frames,index as nat),frames[index].state,e));
        if e.key==key {
            self.complete_projection();
            let i=choose|i:int|0<=i<self.history().states.len() && self.positions()[i]==index;
            assert(self.history().indexed(self.positions(),frames,key));
            if i==0 {
                assert(e.change==joint::Change::Allocate);
                assert(!joint::state_at(frames,index as nat).contains_key(key));
                assert(self.history().states[0].control.fibers =~= IMap::empty());
            } else {
                self.history().interval(self.positions(),frames,key,i-1);
                assert(joint::native::at(frames,index as nat,key)==self.history().states[i-1].project((i-1) as nat));
                assert(super::history::step(self.history().states[i-1],self.history().states[i],self.history().labels[i-1].0,self.history().labels[i-1].1));
            }
        }
        reveal(c::classified);reveal(classified);
    }
    /// All actual commits enter the trajectory. Extension-free control labels
    /// yield the strict paper closure; no value or configuration change is erased
    /// from the full observation to obtain that control-only result.
    pub proof fn production_trace(&self)
        requires self.certified(),
        ensures interpreted(self.joint_spec().events(),self.key()),
            control(self.joint_spec().events(),self.joint_spec().events().len(),self.key())==self.history().states.last().control,
            base_only(self.joint_spec().events(),self.key()) ==> r::execution(controls(self.joint_spec().events(),self.key()),labels(self.joint_spec().events(),self.key()),false),
    {
        self.valid_history();
        let frames=self.joint_spec().events();let key=self.key();
        self.joint_spec().classify();
        assert forall|i:int|0<=i<frames.len() implies #[trigger] classified(frames,i,key) by {self.production_step(i);}
        assert forall|i:int|0<=i<frames.len() implies r::labelled_step(controls(frames,key)[i],controls(frames,key)[i+1],labels(frames,key)[i],true) by {
            assert(classified(frames,i,key));reveal(classified);
        }
        if base_only(frames,key) {
            assert forall|i:int|0<=i<frames.len() implies r::labelled_step(controls(frames,key)[i],controls(frames,key)[i+1],labels(frames,key)[i],false) by {
                assert(classified(frames,i,key));reveal(classified);
            }
        }
        reveal(interpreted);
    }
}
}
