//! Allocation observations at real Journal cuts, decoded using actual writes.
//! The first/last authenticated typed history supplies the value carrier;
//! no expected heap or successful inverse is an input to these constructors.
#[cfg(verus_keep_ghost)]
use super::super::{
    recovery::{self, word},
    semantics::{self as s, Value},
    ResultStep,
};
use super::super::{Report, Step};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, service_composition::Address};
use vstd::prelude::*;

verus! {
pub open spec fn last<T:?Sized>(steps:Seq<Step<T>>,i:int)->bool {
    0<=i<steps.len() && forall|j:int|i<j<steps.len() ==> (#[trigger] steps[j]).address()!=steps[i].address()
}
pub open spec fn keys<T:?Sized>(steps:Seq<Step<T>>)->Set<Address> {word::initial(steps).dom()}
pub open spec fn basis<T:?Sized>(steps:Seq<Step<T>>,key:Address,latest:bool)->int {
    choose|i:int|0<=i<steps.len() && (#[trigger] steps[i]).address()==key && if latest {last(steps,i)} else {word::first(steps,i)}
}
proof fn first_writer<T:?Sized>(steps:Seq<Step<T>>,key:Address)->(i:int)
    requires keys(steps).contains(key),
    ensures word::first(steps,i),steps[i].address()==key,
    decreases steps.len(),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    word::initial_inputs(steps);assert(steps.len()>0);let prefix=steps.drop_last();word::initial_inputs(prefix);
    if keys(prefix).contains(key) {
        let i=first_writer(prefix,key);
        assert forall|j:int|0<=j<i implies (#[trigger] steps[j]).address()!=steps[i].address() by {assert(prefix[j].address()!=prefix[i].address());}
        i
    } else {
        let i=steps.len()-1;
        assert forall|j:int|0<=j<i implies (#[trigger] steps[j]).address()!=steps[i].address() by {assert(prefix[j]==steps[j]);}
        i
    }
}
pub proof fn basis_exists<T:?Sized>(steps:Seq<Step<T>>,key:Address,latest:bool)
    requires keys(steps).contains(key),
    ensures 0<=basis(steps,key,latest)<steps.len(),steps[basis(steps,key,latest)].address()==key,
        latest ==> last(steps,basis(steps,key,latest)),!latest ==> word::first(steps,basis(steps,key,latest)),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    if latest {
        word::initial_inputs(steps);let i=word::last_writer(steps,Map::empty(),key);assert(last(steps,i));
    } else {let i=first_writer(steps,key);}
}
pub proof fn last_value<T:?Sized>(steps:Seq<Step<T>>,key:Address,heap:Map<Address,Value<T>>)
    requires keys(steps).contains(key),
    ensures word::landed(steps,heap).contains_pair(key,steps[basis(steps,key,true)].after()),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    word::initial_inputs(steps);basis_exists(steps,key,true);
    let i=word::last_writer(steps,heap,key);let j=basis(steps,key,true);
    if i<j {assert(steps[j].address()!=key);}else if j<i {assert(steps[i].address()!=key);}
}
pub proof fn landed_domain<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>)
    ensures word::landed(steps,heap).dom()==heap.dom().union(keys(steps)),
    decreases steps.len(),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    word::initial_inputs(steps);
    if steps.len()>0 {
        let prefix=steps.drop_last();landed_domain(prefix,heap);word::initial_inputs(prefix);
        assert(keys(steps) =~= keys(prefix).insert(steps.last().address())) by {
            assert forall|key:Address|keys(steps).contains(key) <==> keys(prefix).insert(steps.last().address()).contains(key) by {
                if keys(steps).contains(key) {
                    let i=choose|i:int|0<=i<steps.len() && (#[trigger] steps[i]).address()==key;
                    if i<prefix.len() {assert(prefix[i].address()==key);}
                }
            }
        }
        assert(word::landed(steps,heap).dom() =~= heap.dom().union(keys(steps)));
    }
}
impl<T:?Sized> Step<T> {
    /// Decode the real revision through the retained typed history. A missing,
    /// retired, or unavailable typed revision has no value here; typed sources
    /// must agree with the actual inverse that supplies the history.
    pub open spec fn decode(&self,record:joint::Record)->Option<Value<T>> {
        match (self.result,record) {
            (ResultStep::Scalar {..},joint::Record::Object {state,..})=>Some(Value::Scalar(state)),
            (ResultStep::Payload(a),joint::Record::Payload {source,revision})=>{
                if source==a.inverse().owner().source() && revision<a.inverse().after().states.len() {
                    Some(Value::Payload(a.inverse().after().states[revision as int]))
                } else {None}
            },_=>None,
        }
    }
    pub proof fn decoded_write(&self)
        requires self.recorded_values(),
        ensures self.decode(joint::state_at(self.write().events(),self.write().at())[self.address().key])==Some(self.before()),
            self.decode(self.write().event().after)==Some(self.after()),
    {
        if let ResultStep::Payload(a)=self.result {a.inverse().source_history();}
    }
}
pub open spec fn value_at<T:?Sized>(step:Step<T>,frames:Seq<joint::Frame>,cut:nat)->Option<Value<T>> {
    let state=joint::state_at(frames,cut);
    if state.contains_key(step.address().key) {step.decode(state[step.address().key])} else {None}
}
/// Domain is the allocations touched by this real function in the stated
/// Journal for which the retained source actually explains the chosen cut.
pub open spec fn observe<T:?Sized>(steps:Seq<Step<T>>,frames:Seq<joint::Frame>,cut:nat,journal:joint::Journal,latest:bool)->Map<Address,Value<T>> {
    Map::new(keys(steps).filter(|key:Address|key.journal==journal && value_at(steps[basis(steps,key,latest)],frames,cut).is_some()),
        |key:Address|value_at(steps[basis(steps,key,latest)],frames,cut).unwrap())
}
pub open spec fn bounded<T:?Sized>(steps:Seq<Step<T>>,end:joint::Receipt)->bool {
    end.wf() && forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).recorded_values()
        && steps[i].write().journal()==end.journal() && end.covers(&steps[i].write())
}
pub open spec fn quiet_start<T:?Sized>(steps:Seq<Step<T>>,frames:Seq<joint::Frame>,start:nat)->bool {
    forall|i:int| #[trigger] word::first(steps,i) ==> recovery::quiet(frames,start,steps[i].write().at(),steps[i].address().key)
}
pub open spec fn quiet_end<T:?Sized>(steps:Seq<Step<T>>,frames:Seq<joint::Frame>)->bool {
    forall|i:int| #[trigger] last(steps,i) ==> recovery::quiet(frames,steps[i].write().at()+1,frames.len(),steps[i].address().key)
}
/// Unlike quiet_record, this also excludes allocation appearing from nowhere
/// inside the gap, so earlier membership need not be an extra assumption.
pub proof fn quiet_domain(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat)
    requires joint::valid(frames),recovery::quiet(frames,start,end,key),
    ensures joint::state_at(frames,start).contains_key(key)==joint::state_at(frames,end).contains_key(key),
        joint::state_at(frames,end).contains_key(key) ==> joint::state_at(frames,start)[key]==joint::state_at(frames,end)[key],
    decreases end-start,
{
    hide(joint::valid);hide(joint::step);
    if start<end {
        let previous=(end-1) as nat;quiet_domain(frames,start,previous,key);recovery::frame_update(frames,previous);
    }
}
proof fn input<T:?Sized>(steps:Seq<Step<T>>,end:joint::Receipt,start:nat,key:Address)
    requires bounded(steps,end),quiet_start(steps,end.events(),start),keys(steps).contains(key),
    ensures key.journal==end.journal(),
        value_at(steps[basis(steps,key,false)],end.events(),start)==Some(word::initial(steps)[key]),
{
    hide(joint::valid);hide(joint::step);hide(Step::address);hide(Step::before);hide(Step::after);
    basis_exists(steps,key,false);let i=basis(steps,key,false);let step=steps[i];let write=step.write();let frames=end.events();
    assert(key==Address {journal:write.journal(),key:write.event().key}) by {reveal(Step::address);}
    word::initial_inputs(steps);assert(word::first(steps,i));
    end.included(&write);step.decoded_write();
    assert(joint::state_at(frames,write.at())==joint::state_at(write.events(),write.at()));
    assert(joint::state_at(frames,write.at()).contains_key(key.key));
    quiet_domain(frames,start,write.at(),key.key);
}
pub proof fn initial_observation<T:?Sized>(steps:Seq<Step<T>>,end:joint::Receipt,start:nat)
    requires bounded(steps,end),quiet_start(steps,end.events(),start),
    ensures observe(steps,end.events(),start,end.journal(),false)==word::initial(steps),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    hide(bounded);hide(quiet_start);hide(Step::decode);hide(value_at);hide(word::initial);
    assert forall|key:Address|keys(steps).contains(key) implies key.journal==end.journal()
        && value_at(steps[basis(steps,key,false)],end.events(),start)==Some(word::initial(steps)[key]) by {input(steps,end,start,key);}
    assert(observe(steps,end.events(),start,end.journal(),false) =~= word::initial(steps));
}
proof fn output<T:?Sized>(steps:Seq<Step<T>>,end:joint::Receipt,key:Address)
    requires bounded(steps,end),quiet_end(steps,end.events()),keys(steps).contains(key),
    ensures key.journal==end.journal(),
        value_at(steps[basis(steps,key,true)],end.events(),end.events().len())==Some(word::landed(steps,word::initial(steps))[key]),
{
    hide(joint::valid);hide(joint::step);hide(Step::address);hide(Step::before);hide(Step::after);
    basis_exists(steps,key,true);let i=basis(steps,key,true);let step=steps[i];let write=step.write();let frames=end.events();
    assert(key==Address {journal:write.journal(),key:write.event().key}) by {reveal(Step::address);}
    end.included(&write);step.decoded_write();recovery::frame_update(frames,write.at());
    recovery::quiet_record(frames,write.at()+1,frames.len(),key.key);
    last_value(steps,key,word::initial(steps));
}
pub proof fn final_observation<T:?Sized>(steps:Seq<Step<T>>,end:joint::Receipt)
    requires bounded(steps,end),quiet_end(steps,end.events()),
    ensures observe(steps,end.events(),end.events().len(),end.journal(),true)==word::landed(steps,word::initial(steps)),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    hide(bounded);hide(quiet_end);hide(Step::decode);hide(value_at);hide(word::initial);hide(word::landed);
    landed_domain(steps,word::initial(steps));
    assert forall|key:Address|keys(steps).contains(key) implies key.journal==end.journal()
        && value_at(steps[basis(steps,key,true)],end.events(),end.events().len())==Some(word::landed(steps,word::initial(steps))[key]) by {output(steps,end,key);}
    assert(observe(steps,end.events(),end.events().len(),end.journal(),true) =~= word::landed(steps,word::initial(steps)));
}
impl<T:?Sized> Report<T> {
    /// End is a real invocation-return receipt covering this function. The
    /// boundary premises inspect its source frames, never an expected heap.
    pub proof fn recover_observed(&self,end:joint::Receipt,start:nat)
        requires self.recovery_history(),bounded(self.steps@,end),word::admissible(self.steps@),
            quiet_start(self.steps@,end.events(),start),quiet_end(self.steps@,end.events()),
        ensures s::replay(self.steps@,observe(self.steps@,end.events(),start,end.journal(),false))==Some(observe(self.steps@,end.events(),end.events().len(),end.journal(),true)),
            s::undo(self.steps@,observe(self.steps@,end.events(),end.events().len(),end.journal(),true))==Some(observe(self.steps@,end.events(),start,end.journal(),false)),
    {self.recovery_word();initial_observation(self.steps@,end,start);final_observation(self.steps@,end);}
}
}
