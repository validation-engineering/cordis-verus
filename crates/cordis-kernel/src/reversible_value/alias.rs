//! Allocation-key interpretation of Definition 29 and its exact single-key
//! specialization. Dynamic service aliases are an explicit observation layer;
//! different names alone never imply independent mutable bindings.
#[cfg(verus_keep_ghost)]
use super::{access, effect, joint, Branch, Event, Outcome, ValueState};
#[cfg(verus_keep_ghost)]
use crate::{dependent_grammar as d, lifecycle_state::services::slots};
use vstd::prelude::*;

verus! {
pub open spec fn library<K>()->d::Library<K,(K,effect::Code),(),ValueState,Outcome> {
    d::Library {values:|_:K,_:ValueState|true,arguments:|_:(K,effect::Code),_:()|true,
        outcomes:|_:(K,effect::Code),_:Outcome|true,key:|a:(K,effect::Code)|a.0,allowed:ISet::full(),
        apply:|a:(K,effect::Code),_:()|effect::operation(a.1)}
}
pub proof fn primitive_theory<K>()
    ensures d::primitive_theory(|_:K,a:ValueState,b:ValueState|a==b,library::<K>()),
{ }
pub open spec fn node<K>(key:K,code:effect::Code,branch:Branch)->d::Node<K,(K,effect::Code),(),ValueState,Outcome,usize> {
    d::Node::Operation {operation:(key,code),argument:(),select:|out:Outcome|branch.selected(out)}
}
pub open spec fn operation_code(op:super::Operation)->effect::Code {
    <super::Operation as effect::ScalarEffect>::model(&op)
}
pub proof fn operation_agrees(op:super::Operation,input:ValueState)
    ensures effect::operation(operation_code(op))(input)==super::operation(op)(input),
{ }
pub open spec fn event_code(event:Event)->effect::Code {
    match event {Event::Forward {operation,..}=>operation_code(operation),Event::Computed {code,..}=>code,_=>|_:u64|None}
}
pub open spec fn event_branch(event:Event)->Branch {
    match event {Event::Forward {branch,..}|Event::Computed {branch,..}=>branch,_=>Branch {matched:None,unmatched:None}}
}
pub open spec fn event_outcome(event:Event)->Outcome {
    match event {Event::Forward {outcome,..}|Event::Computed {outcome,..}=>outcome,_=>Outcome {before:0,after:0,matched:false}}
}
/// Fixed built-in operations and extensible computations share this one
/// interpretation of actual writes and their captured strict inverses.
pub proof fn managed_step(before:Map<nat,joint::Record>,after:Map<nat,joint::Record>,step:joint::Step)
    requires joint::step(before,after,step),step.change is Value,
        step.change->Value_event is Forward || step.change->Value_event is Computed,
    ensures {
        let event=step.change->Value_event;let code=event_code(event);let branch=event_branch(event);
        let run=d::run(library(),node(step.key,code,branch),access::objects(before));
        &&& run.is_some() && run.unwrap().state==access::objects(after)
        &&& run.unwrap().next==branch.selected(event_outcome(event))
        &&& effect::operation(code)(access::objects(before)[step.key]).unwrap().outcome==event_outcome(event)
        &&& forall|state:Map<nat,ValueState>| #[trigger] (run.unwrap().undo)(state)==
            if state.contains_key(step.key) && state[step.key]==event.after() {Some(state.insert(step.key,event.before()))} else {None}
    },
{
    let event=step.change->Value_event;
    if event is Computed {computed(before,after,step);}
    else {
        reveal(joint::changes);
        operation_agrees(event->Forward_operation,event.before());
        assert(access::objects(after) =~= access::objects(before).insert(step.key,event.after()));
    }
}

pub open spec fn terminal(key:nat,code:effect::Code)->d::Program<nat,(nat,effect::Code),(),ValueState,Outcome,()> {
    |_:()|d::Node::Operation {operation:(key,code),argument:(),select:|_:Outcome|None}
}
/// Least-grammar membership is universal over inputs, rather than inferred
/// from a single successful trace. The key here is a captured allocation.
pub proof fn terminal_member(key:nat,code:effect::Code,keys:ISet<nat>,provisions:ISet<nat>)
    requires keys.contains(key),
    ensures d::member(library(),terminal(key,code),keys,provisions,()),
{d::constructor_member(library(),terminal(key,code),keys,provisions,());}

pub open spec fn grammar(key:nat,code:effect::Code)->crate::dependent_independence::Grammar<nat,(nat,effect::Code),(),ValueState,Outcome,()> {
    crate::dependent_independence::Grammar {library:library(),program:terminal(key,code),keys:ISet::new(|k:nat|k==key),provisions:ISet::empty(),root:()}
}
/// Strict independence covers generated forward/inverse words, actual outcomes
/// and continuation stability. Equal port names are irrelevant; allocation
/// separation is the premise that makes this a valid instance of the theorem.
pub proof fn allocation_independence(left:nat,right:nat,a:effect::Code,b:effect::Code)
    requires left!=right,
    ensures crate::iterator_bridge::independent(
        crate::dependent_independence::equality(|_:nat,x:ValueState,y:ValueState|x==y),
        d::family(library(),terminal(left,a)),(),d::family(library(),terminal(right,b)),()),
{
    let eq=|_:nat,x:ValueState,y:ValueState|x==y;
    primitive_theory::<nat>();crate::observational_grammar::exact_theory(eq,library());
    let l=grammar(left,a);let r=grammar(right,b);
    terminal_member(left,a,l.keys,l.provisions);terminal_member(right,b,r.keys,r.provisions);
    crate::dependent_independence::grammar_independence(eq,l,r);
}

pub open spec fn coherent<K>(targets:Map<K,nat>,heap:Map<nat,ValueState>)->bool {
    forall|key:K| targets.contains_key(key) ==> heap.contains_key(#[trigger] targets[key])
}
pub open spec fn view<K>(targets:Map<K,nat>,heap:Map<nat,ValueState>)->Map<K,ValueState> {
    Map::new(targets.dom(),|key:K|heap[targets[key]])
}
pub open spec fn aliases<K>(targets:Map<K,nat>,object:nat)->Set<K> {targets.dom().filter(|key:K|targets[key]==object)}
pub open spec fn single_binding<K>(targets:Map<K,nat>,key:K,object:nat)->bool {
    targets.contains_key(key) && targets[key]==object && aliases(targets,object)==set![key]
}
/// Every alias changes together; the argument is an arbitrary heap, not just
/// the reachable initial state of one example plugin.
pub proof fn write_projection<K>(targets:Map<K,nat>,heap:Map<nat,ValueState>,object:nat,value:ValueState)
    requires coherent(targets,heap),heap.contains_key(object),
    ensures coherent(targets,heap.insert(object,value)),
        view(targets,heap.insert(object,value)).dom()==view(targets,heap).dom(),
        forall|key:K| targets.contains_key(key) ==> #[trigger] view(targets,heap.insert(object,value))[key]==
            if aliases(targets,object).contains(key) {value} else {view(targets,heap)[key]},
{ }
/// The precise additional law needed to recover a single named binding.
pub proof fn single_key_write<K>(targets:Map<K,nat>,heap:Map<nat,ValueState>,key:K,object:nat,value:ValueState)
    requires coherent(targets,heap),single_binding(targets,key,object),
    ensures view(targets,heap.insert(object,value))==view(targets,heap).insert(key,value),
{
    write_projection(targets,heap,object,value);
    assert(view(targets,heap.insert(object,value)) =~= view(targets,heap).insert(key,value));
}
/// Equation (31), including failure, actual outcome-selected continuation and
/// the strict inverse on every coherent recovery input. It applies only while
/// the selected service really denotes this sole binding of the allocation.
pub proof fn single_key_refinement<K>(targets:Map<K,nat>,heap:Map<nat,ValueState>,key:K,object:nat,code:effect::Code,branch:Branch)
    requires coherent(targets,heap),single_binding(targets,key,object),
    ensures {
        let actual=d::run(library(),node(object,code,branch),heap);
        let paper=d::run(library(),node(key,code,branch),view(targets,heap));
        &&& actual.is_some()==paper.is_some()
        &&& actual.is_some() ==> {
            &&& view(targets,actual.unwrap().state)==paper.unwrap().state
            &&& actual.unwrap().next==paper.unwrap().next
            &&& forall|recovery:Map<nat,ValueState>| coherent(targets,recovery) ==> {
                let left=(actual.unwrap().undo)(recovery);
                let right=(paper.unwrap().undo)(view(targets,recovery));
                &&& left.is_some()==right.is_some()
                &&& left.is_some() ==> view(targets,left.unwrap())==right.unwrap()
            }
        }
    },
{
    let actual=d::run(library(),node(object,code,branch),heap);
    let paper=d::run(library(),node(key,code,branch),view(targets,heap));
    if actual.is_some() {
        single_key_write(targets,heap,key,object,actual.unwrap().state[object]);
        assert forall|recovery:Map<nat,ValueState>| coherent(targets,recovery) implies {
            let left=(actual.unwrap().undo)(recovery);let right=(paper.unwrap().undo)(view(targets,recovery));
            &&& left.is_some()==right.is_some()
            &&& left.is_some() ==> view(targets,left.unwrap())==right.unwrap()
        } by {
            let left=(actual.unwrap().undo)(recovery);let right=(paper.unwrap().undo)(view(targets,recovery));
            if left.is_some() {single_key_write(targets,recovery,key,object,heap[object]);}
        }
    }
}
/// A successful managed effect changes depth even if its scalar value stays
/// equal. An alias at another key therefore refutes the literal single-key lift.
pub proof fn other_alias_changes<K>(targets:Map<K,nat>,heap:Map<nat,ValueState>,key:K,other:K,code:effect::Code,branch:Branch)
    requires coherent(targets,heap),targets.contains_key(key),targets.contains_key(other),key!=other,targets[key]==targets[other],
        d::run(library(),node(targets[key],code,branch),heap).is_some(),
    ensures view(targets,d::run(library(),node(targets[key],code,branch),heap).unwrap().state)[other]!=view(targets,heap)[other],
        d::run(library(),node(key,code,branch),view(targets,heap)).unwrap().state[other]==view(targets,heap)[other],
{ }
/// Distinct actual allocations commute, preserving rejection domains and
/// outcomes. This does not certify arbitrary operations on a shared allocation.
pub proof fn disjoint_effects(left:nat,right:nat,a:effect::Code,b:effect::Code,heap:Map<nat,ValueState>)
    requires left!=right,
    ensures {
        let f=|s:Map<nat,ValueState>|match d::run(library(),node(left,a,Branch {matched:None,unmatched:None}),s) {Some(r)=>Some(r.state),None=>None};
        let g=|s:Map<nat,ValueState>|match d::run(library(),node(right,b,Branch {matched:None,unmatched:None}),s) {Some(r)=>Some(r.state),None=>None};
        &&& crate::partial_independence::compose(f,g)(heap)==crate::partial_independence::compose(g,f)(heap)
        &&& f(heap).is_some() ==> g(f(heap).unwrap()).is_some()==g(heap).is_some()
        &&& g(heap).is_some() ==> f(g(heap).unwrap()).is_some()==f(heap).is_some()
    },
{
    if heap.contains_key(left) && heap.contains_key(right) && effect::operation(a)(heap[left]).is_some() && effect::operation(b)(heap[right]).is_some() {
        let x=effect::operation(a)(heap[left]).unwrap().value;let y=effect::operation(b)(heap[right]).unwrap().value;
        assert(heap.insert(left,x).insert(right,y) =~= heap.insert(right,y).insert(left,x));
    }
}

/// Local managed targets come from the actual slot records. Opaque and foreign
/// entries stay explicit in slots::projection; they are outside this scalar map.
pub open spec fn targets<K,T,M>(values:Map<K,std::sync::Arc<super::slot::ServiceSlot<T,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>)->Map<K,nat> {
    Map::new(values.dom().filter(|key:K| match slots::service(values[key],journal,state) {
        Some(slots::ServiceObservation::Managed {resolution:joint::references::Resolution::Local {..}})=>true,_=>false,
    }),|key:K|slots::service(values[key],journal,state).unwrap()->Managed_resolution->Local_selection.object.key)
}
pub proof fn production_targets<K,T,M>(values:Map<K,std::sync::Arc<super::slot::ServiceSlot<T,M>>>,journal:joint::Journal,state:Map<nat,joint::Record>)
    ensures coherent(targets(values,journal,state),access::objects(state)),
        forall|object:nat| #[trigger] aliases(targets(values,journal,state),object)==slots::affected(values,journal,state,object),
{ }
/// A real object commit changes values of all current aliases but no targets.
/// The current target can differ from the capture retained by this call.
pub proof fn production_value<K,T,M>(values:Map<K,std::sync::Arc<super::slot::ServiceSlot<T,M>>>,journal:joint::Journal,before:Map<nat,joint::Record>,after:Map<nat,joint::Record>,event:joint::Step)
    requires joint::step(before,after,event),event.change is Value,
    ensures targets(values,journal,after)==targets(values,journal,before),
        access::objects(after)==access::objects(before).insert(event.key,event.change->Value_event.after()),
        forall|key:K| targets(values,journal,before).contains_key(key) ==>
            #[trigger] view(targets(values,journal,after),access::objects(after))[key]==
                if slots::affected(values,journal,before,event.key).contains(key) {event.change->Value_event.after()}
                else {view(targets(values,journal,before),access::objects(before))[key]},
{
    slots::project_value_step(values,journal,before,after,event);production_targets(values,journal,before);
    reveal(joint::changes);
    assert(access::objects(after) =~= access::objects(before).insert(event.key,event.change->Value_event.after()));
    assert(targets(values,journal,after) =~= targets(values,journal,before));
    write_projection(targets(values,journal,before),access::objects(before),event.key,event.change->Value_event.after());
}
/// Slot replacement is a separate semantic transition: it leaves object state
/// intact and can change exactly the observations selecting that real slot.
pub proof fn production_replace<K,T,M>(values:Map<K,std::sync::Arc<super::slot::ServiceSlot<T,M>>>,journal:joint::Journal,before:Map<nat,joint::Record>,after:Map<nat,joint::Record>,event:joint::Step)
    requires joint::step(before,after,event),event.change is Replace,
    ensures access::objects(after)==access::objects(before),
        forall|key:K| values.contains_key(key) && (values[key].managed().is_none()
            || values[key].managed().unwrap().journal_spec()!=journal || values[key].managed().unwrap().key()!=event.key) ==>
            #[trigger] slots::projection(values,journal,after)[key]==slots::projection(values,journal,before)[key],
{
    reveal(joint::changes);
    assert(access::objects(after) =~= access::objects(before));
}
/// The actual computed event instantiates the full allocation-key primitive.
/// Its strict returned inverse is the same before/after check retained by the
/// executable cleanup owner, not an inverse supplied by the plugin.
pub proof fn computed(before:Map<nat,joint::Record>,after:Map<nat,joint::Record>,step:joint::Step)
    requires joint::step(before,after,step),step.change is Value,step.change->Value_event is Computed,
    ensures {
        let event=step.change->Value_event;
        let run=d::run(library(),node(step.key,event->Computed_code,event->Computed_branch),access::objects(before));
        &&& run.is_some() && run.unwrap().state==access::objects(after) && run.unwrap().next==event->Computed_next
        &&& effect::operation(event->Computed_code)(access::objects(before)[step.key]).unwrap().outcome==event->Computed_outcome
        &&& forall|state:Map<nat,ValueState>| #[trigger] (run.unwrap().undo)(state)==
            if state.contains_key(step.key) && state[step.key]==event.after() {Some(state.insert(step.key,event.before()))} else {None}
    },
{
    reveal(joint::changes);
    assert(access::objects(after) =~= access::objects(before).insert(step.key,step.change->Value_event.after()));
}
}
