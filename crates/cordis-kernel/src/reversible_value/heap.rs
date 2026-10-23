//! Alias-aware projection of actual shared-object histories. Ports select slot
//! versions; the heap is keyed by the allocation carried by a real snapshot.
//! A fixed retained view is not an atomic snapshot of all host service slots.
use super::slot::{Capture, Replacement, ServiceBinding};
use super::ValueState;
#[cfg(verus_keep_ghost)]
use super::{Event, Operation, Outcome, Snapshot};
#[cfg(verus_keep_ghost)]
use crate::dependent_grammar as d;
use crate::Port;
use vstd::prelude::*;
use vstd::resource::Loc;

verus! {
pub struct Selection {pub slot:Loc,pub revision:u64,pub object:Loc}
impl Capture {
    pub open spec fn selection(&self)->Selection {Selection {slot:self.slot().source(),revision:self.revision_spec(),object:self.object()}}
}
impl ServiceBinding {
    pub open spec fn selection(&self)->Selection {self.capture_spec().selection()}
}
pub struct Observation {pub bindings:Map<Port,Selection>,pub heap:Map<Loc,ValueState>}
impl Observation {
    pub open spec fn wf(&self)->bool {
        forall|port:Port| #[trigger] self.bindings.contains_key(port) ==> self.heap.contains_key(self.bindings[port].object)
    }
    pub open spec fn values(&self)->Map<Port,ValueState> {
        Map::new(self.bindings.dom(),|port:Port|self.heap[self.bindings[port].object])
    }
    pub open spec fn affected(&self,object:Loc)->Set<Port> {
        self.bindings.dom().filter(|port:Port|self.bindings[port].object==object)
    }
    pub open spec fn write(&self,object:Loc,state:ValueState)->Self {Self {bindings:self.bindings,heap:self.heap.insert(object,state)}}
}
pub open spec fn library()->d::Library<Loc,(Loc,Operation),(),ValueState,Outcome> {
    d::Library {values:|_:Loc,_:ValueState|true,arguments:|_:(Loc,Operation),_:()|true,
        outcomes:|_:(Loc,Operation),_:Outcome|true,key:|a:(Loc,Operation)|a.0,allowed:ISet::full(),
        apply:|a:(Loc,Operation),_:()|super::operation(a.1)}
}
pub proof fn primitive_theory()
    ensures d::primitive_theory(|_:Loc,a:ValueState,b:ValueState|a==b,library()),
{ }
pub open spec fn step(event:Event,object:Loc,before:Observation,after:Observation)->bool {
    &&& event.valid() && before.wf() && before.heap.contains_key(object) && before.heap[object]==event.before()
    &&& after==before.write(object,event.after())
    &&& match event {
        Event::Forward {operation,branch,next,..}=>{
            let run=d::run(library(),d::Node::Operation {operation:(object,operation),argument:(),select:|out:Outcome|branch.selected(out)},before.heap);
            run.is_some() && run.unwrap().state==after.heap && run.unwrap().next==next
        },
        Event::Computed {code,before:input,after:output,outcome,next,branch}=>{
            let run=super::effect::operation(code)(input);
            run.is_some() && run.unwrap().value==output && run.unwrap().outcome==outcome && next==branch.selected(outcome)
        },
        Event::Restore {inverse,..}=>d::inverse(object,|state:ValueState|inverse.undo(state))(before.heap)==Some(after.heap),
        _=>before==after,
    }
}
/// Writes affect every alias of this object, and frame exactly the other
/// objects/ports. This includes successful inverses targeting old allocations.
pub proof fn interpret(event:Event,object:Loc,before:Observation)
    requires before.wf(),event.valid(),before.heap.contains_key(object),before.heap[object]==event.before(),
    ensures step(event,object,before,before.write(object,event.after())),before.write(object,event.after()).wf(),
        before.write(object,event.after()).values().dom()==before.values().dom(),
        forall|port:Port| #[trigger] before.bindings.contains_key(port) ==>
            before.write(object,event.after()).values()[port]==
                if before.affected(object).contains(port) {event.after()} else {before.values()[port]},
        forall|other:Loc| before.heap.contains_key(other) && other!=object ==>
            #[trigger] before.write(object,event.after()).heap[other]==before.heap[other],
    {
        if event.before()==event.after() {
            assert(before.heap.insert(object,event.after()) =~= before.heap);
        }
    }
/// The old port-local frame is false for a changing event when another port
/// aliases its object. Distinct port names alone cannot justify independence.
pub proof fn alias_changes(event:Event,object:Loc,before:Observation,alias:Port)
    requires before.wf(),event.valid(),before.heap.contains_key(object),before.heap[object]==event.before(),
        before.affected(object).contains(alias),event.before()!=event.after(),
    ensures before.write(object,event.after()).values()[alias]!=before.values()[alias],
{interpret(event,object,before);}

/// Construct a continuous trace from a real certified object's entire history.
/// Bindings here denote retained selections. A live registry changing its
/// bindings needs its own interleaving/linearization argument.
pub proof fn history(snapshot:&Snapshot,initial:Observation)->(states:Seq<Observation>)
    requires snapshot.certified(),initial.wf(),initial.heap.contains_key(snapshot.source()),initial.heap[snapshot.source()]==snapshot.initial(),
    ensures states.len()==snapshot.history().len()+1,states.first()==initial,
        states.last()==initial.write(snapshot.source(),snapshot.state()),
        forall|i:int| 0<=i<snapshot.history().len() ==> {
            let event=snapshot.history()[i];
            &&& #[trigger] states[i]==initial.write(snapshot.source(),event.before())
            &&& states[i+1]==initial.write(snapshot.source(),event.after())
            &&& step(event,snapshot.source(),states[i],states[i+1]) && states[i+1].wf()
        },
{
    snapshot.execution();let events=snapshot.history();let object=snapshot.source();
    let states=Seq::new(events.len()+1,|i:int|if i==0 {initial} else {initial.write(object,events[i-1].after())});
    if events.len()==0 {assert(initial.heap.insert(object,snapshot.state()) =~= initial.heap);}
    assert forall|i:int| 0<=i<events.len() implies {
        let event=events[i];
        &&& #[trigger] states[i]==initial.write(object,event.before())
        &&& states[i+1]==initial.write(object,event.after())
        &&& step(event,object,states[i],states[i+1]) && states[i+1].wf()
    } by {
        let event=events[i];
        if i==0 {assert(initial.heap.insert(object,event.before()) =~= initial.heap);}
        else {assert(events[i-1].after()==event.before());}
        interpret(event,object,states[i]);
        assert(states[i].heap.insert(object,event.after()) =~= states[i+1].heap);
    }
    states
}
impl Replacement {
    /// All *current* views of the same slot advance together. Other slots may
    /// still alias the previous object and keep their own revision. Retained
    /// captures are separate immutable observations and are never rewritten.
    pub proof fn rebind(&self,bindings:Map<Port,Selection>)->(after:Map<Port,Selection>)
        requires self.wf(),
            forall|port:Port| #[trigger] bindings.contains_key(port) && bindings[port].slot==self.previous().selection().slot
                ==> bindings[port]==self.previous().selection(),
        ensures after.dom()==bindings.dom(),
            forall|port:Port| #[trigger] bindings.contains_key(port) ==> after[port]==
                if bindings[port].slot==self.previous().selection().slot {self.current().selection()} else {bindings[port]},
            self.current().selection().slot==self.previous().selection().slot,
            self.current().selection().revision==self.previous().selection().revision+1,
            self.current().history()[self.previous().revision_spec() as int]==self.previous().value_spec(),
    {
        self.previous().retained_object(&self.current());
        Map::new(bindings.dom(),|port:Port|if bindings[port].slot==self.previous().selection().slot {self.current().selection()} else {bindings[port]})
    }
}
}
