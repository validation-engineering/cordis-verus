//! Reference integrity of actual slot commits, including concurrent swaps.
//! Local references resolve in every state of the authoritative execution;
//! foreign references carry identity only, never an invented local value.
use super::Object;
#[cfg(verus_keep_ghost)]
use super::{changes, state_at, step, valid, Frame, Receipt, Record, Step};
use vstd::prelude::*;
use vstd::resource::Loc;

verus! {
pub open spec fn present(state:Map<nat,Record>,object:Object,domain:Loc)->bool {
    object.domain!=domain || state.contains_key(object.key) && state[object.key] is Object
}
pub open spec fn linked(state:Map<nat,Record>,record:Record,domain:Loc)->bool {
    record is Slot ==> present(state,record->Slot_object,domain)
}
pub open spec fn closed(state:Map<nat,Record>,domain:Loc)->bool {
    forall|key:nat| state.contains_key(key) ==> linked(state,#[trigger] state[key],domain)
}
pub open spec fn history(frames:Seq<Frame>,domain:Loc)->bool {
    forall|i:int| 0<=i<frames.len() ==> linked(state_at(frames,i as nat),#[trigger] frames[i].event.after,domain)
}
/// Only an authentic receipt of this exact object can justify a new target.
pub open spec fn evidence(record:Record,receipt:Option<Receipt>)->bool {
    record is Slot ==> receipt.is_some() && receipt.unwrap().wf()
        && receipt.unwrap().journal().source()==record->Slot_object.domain
        && receipt.unwrap().event().key==record->Slot_object.key
        && receipt.unwrap().event().after is Object
}
pub proof fn object_step(before:Map<nat,Record>,after:Map<nat,Record>,event:Step,key:nat)
    requires step(before,after,event),before.contains_key(key),before[key] is Object,
    ensures after.contains_key(key),after[key] is Object,after[key]->Object_source==before[key]->Object_source,
{if event.key==key {reveal(changes);}}
pub proof fn object_retained(frames:Seq<Frame>,start:nat,end:nat,key:nat)
    requires valid(frames),start<=end<=frames.len(),state_at(frames,start).contains_key(key),state_at(frames,start)[key] is Object,
    ensures state_at(frames,end).contains_key(key),state_at(frames,end)[key] is Object,
        state_at(frames,end)[key]->Object_source==state_at(frames,start)[key]->Object_source,
    decreases end-start,
{
    if start<end {
        object_retained(frames,start,(end-1) as nat,key);
        assert(step(state_at(frames,(end-1) as nat),frames[end-1].state,frames[end-1].event));
        object_step(state_at(frames,(end-1) as nat),frames[end-1].state,frames[end-1].event,key);
    }
}
pub proof fn preserve(before:Map<nat,Record>,after:Map<nat,Record>,event:Step,domain:Loc)
    requires step(before,after,event),closed(before,domain),linked(before,event.after,domain),
    ensures closed(after,domain),
{
    assert forall|key:nat| after.contains_key(key) implies linked(after,#[trigger] after[key],domain) by {
        if after[key] is Slot {
            let object=after[key]->Slot_object;
            if key!=event.key {assert(linked(before,before[key],domain));}
            if object.domain==domain {object_step(before,after,event,object.key);}
        }
    }
}
pub proof fn at(frames:Seq<Frame>,n:nat,domain:Loc)
    requires valid(frames),history(frames,domain),n<=frames.len(),
    ensures closed(state_at(frames,n),domain),
    decreases n,
{
    if n>0 {
        at(frames,(n-1) as nat,domain);
        assert(step(state_at(frames,(n-1) as nat),frames[n-1].state,frames[n-1].event));
        assert(linked(state_at(frames,(n-1) as nat),frames[n-1].event.after,domain));
        preserve(state_at(frames,(n-1) as nat),frames[n-1].state,frames[n-1].event,domain);
    }
}
pub proof fn append(frames:Seq<Frame>,frame:Frame,domain:Loc)
    requires history(frames,domain),linked(state_at(frames,frames.len()),frame.event.after,domain),
    ensures history(frames.push(frame),domain),
{
    assert forall|i:int| 0<=i<frames.push(frame).len() implies
        linked(state_at(frames.push(frame),i as nat),#[trigger] frames.push(frame)[i].event.after,domain) by {
        if i<frames.len() {assert(state_at(frames.push(frame),i as nat)==state_at(frames,i as nat));}
        else {assert(state_at(frames.push(frame),i as nat)==state_at(frames,frames.len()));}
    }
}
/// A selection identifies both the current slot version and its allocation.
pub struct Selection {pub slot:Loc,pub revision:u64,pub object:Object}
pub enum Resolution {Local {selection:Selection,source:Loc,state:super::ValueState},Foreign {selection:Selection}}
pub open spec fn selection(record:Record)->Selection
    recommends record is Slot,
{Selection {slot:record->Slot_source,revision:record->Slot_revision,object:record->Slot_object}}
pub open spec fn resolve(state:Map<nat,Record>,domain:Loc,key:nat)->Option<Resolution> {
    if !state.contains_key(key) || !(state[key] is Slot) {None} else {
        let selected=selection(state[key]);let object=selected.object;
        if object.domain!=domain {Some(Resolution::Foreign {selection:selected})}
        else if state.contains_key(object.key) && state[object.key] is Object {
            Some(Resolution::Local {selection:selected,source:state[object.key]->Object_source,state:state[object.key]->Object_state})
        } else {None}
    }
}
pub proof fn resolves(state:Map<nat,Record>,domain:Loc,key:nat)
    requires closed(state,domain),state.contains_key(key),state[key] is Slot,
    ensures resolve(state,domain,key).is_some(),
        resolve(state,domain,key).unwrap() is Local <==> state[key]->Slot_object.domain==domain,
{assert(linked(state,state[key],domain));}
/// Distinct service slots can select one allocation. Their current scalar
/// values agree even if the slots have different revision counters.
pub proof fn aliases(state:Map<nat,Record>,domain:Loc,a:nat,b:nat)
    requires closed(state,domain),state.contains_key(a),state[a] is Slot,state.contains_key(b),state[b] is Slot,
        state[a]->Slot_object==state[b]->Slot_object,state[a]->Slot_object.domain==domain,
    ensures resolve(state,domain,a).is_some(),resolve(state,domain,b).is_some(),
        resolve(state,domain,a).unwrap() is Local,resolve(state,domain,b).unwrap() is Local,
        resolve(state,domain,a).unwrap()->Local_state==resolve(state,domain,b).unwrap()->Local_state,
        resolve(state,domain,a).unwrap()->Local_source==resolve(state,domain,b).unwrap()->Local_source,
{resolves(state,domain,a);resolves(state,domain,b);}
/// Every actual write/restore updates all aliases of its object; other slots'
/// observations are framed. A slot replacement is a separate transition.
pub proof fn value_step(before:Map<nat,Record>,after:Map<nat,Record>,event:Step,domain:Loc,key:nat)
    requires step(before,after,event),closed(before,domain),event.change is Value,
        before.contains_key(key),before[key] is Slot,
    ensures after.contains_key(key),after[key]==before[key],resolve(after,domain,key).is_some(),
        if before[key]->Slot_object.domain==domain && before[key]->Slot_object.key==event.key {
            resolve(after,domain,key)==Some(Resolution::Local {selection:selection(before[key]),
                source:before[event.key]->Object_source,state:event.change->Value_event.after()})
        } else {resolve(after,domain,key)==resolve(before,domain,key)},
{
    reveal(changes);resolves(before,domain,key);
    assert(before[event.key] is Object);assert(event.key!=key);
}
impl super::Snapshot {
    pub open spec fn slot(&self,key:nat)->Option<Resolution> {resolve(self.last(),self.domain(),key)}
    pub proof fn slot_resolves(&self,key:nat)
        requires self.certified(),self.last().contains_key(key),self.last()[key] is Slot,
        ensures self.slot(key).is_some(),self.slot(key).unwrap() is Local <==> self.last()[key]->Slot_object.domain==self.domain(),
    {self.references();resolves(self.last(),self.domain(),key);}
    pub proof fn retained_reference(&self,receipt:Receipt)
        requires self.certified(),receipt.wf(),receipt.journal()==self.journal_spec(),receipt.event().after is Slot,
            receipt.events().len()<=self.events().len(),self.events().take(receipt.events().len() as int)==receipt.events(),
        ensures present(self.last(),receipt.event().after->Slot_object,self.domain()),
            receipt.event().after->Slot_object.domain==self.domain() ==> self.resolve(receipt.event().after->Slot_object).is_some(),
    {
        self.valid_history();let object=receipt.event().after->Slot_object;let i=receipt.at();
        assert(self.events()[i as int]==receipt.events()[i as int]);
        assert(linked(state_at(self.events(),i),self.events()[i as int].event.after,self.domain()));
        if object.domain==self.domain() {object_retained(self.events(),i,self.events().len(),object.key);}
    }
    /// Apply the alias/frame law to a position in a real certified execution.
    pub proof fn value_observation_step(&self,i:nat,key:nat)
        requires self.certified(),i<self.events().len(),self.events()[i as int].event.change is Value,
            state_at(self.events(),i).contains_key(key),state_at(self.events(),i)[key] is Slot,
        ensures ({let before=state_at(self.events(),i);let after=state_at(self.events(),i+1);let event=self.events()[i as int].event;
            &&& after.contains_key(key) && after[key]==before[key] && resolve(after,self.domain(),key).is_some()
            &&& if before[key]->Slot_object.domain==self.domain() && before[key]->Slot_object.key==event.key {
                resolve(after,self.domain(),key)==Some(Resolution::Local {selection:selection(before[key]),
                    source:before[event.key]->Object_source,state:event.change->Value_event.after()})
            } else {resolve(after,self.domain(),key)==resolve(before,self.domain(),key)}
        }),
    {
        self.valid_history();at(self.events(),i,self.domain());
        assert(step(state_at(self.events(),i),self.events()[i as int].state,self.events()[i as int].event));
        value_step(state_at(self.events(),i),state_at(self.events(),i+1),self.events()[i as int].event,self.domain(),key);
    }
}
}
