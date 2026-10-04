//! Reachable reverse witnesses for authentic foreign inverse calls.
//!
//! A returned inverse is not assumed to have a global inverse. Its original
//! forward is proved to be a local reverse witness at actual reachable inputs
//! by transporting the original call witness through commuting real events.
use crate::mediated as m;
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, child_history as ch, dependent_grammar as d, dependent_lift as dep,
    grammar_lift as lift, mixed_grammar as g, observational_grammar as og,
    observational_lift as ol, partial_domains as domains, partial_independence as p,
    preservation as inv, projection as project, recovery_examples as ex, refinement as r,
    semantics as full, shared_execution as shared, shared_replay as replay, strict_journal as sj,
    Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(S)]
pub struct Pair<S> {pub forward:m::PartialMap<S>,pub inverse:m::PartialMap<S>,pub own:bool}
#[verifier::reject_recursive_types(S)]
pub enum Action<S> {Forward {call:Pair<S>},Inverse {token:nat},Identity}

pub open spec fn retracts<S>(eq:spec_fn(S,S)->bool,call:Pair<S>,state:S)->bool {
    &&& (call.inverse)(state).is_some()
    &&& (call.forward)((call.inverse)(state).unwrap()).is_some()
    &&& eq((call.forward)((call.inverse)(state).unwrap()).unwrap(),state)
}
pub open spec fn respectful<S>(eq:spec_fn(S,S)->bool,call:Pair<S>)->bool {
    p::respects(eq,call.forward) && p::respects(eq,call.inverse)
}
pub open spec fn compatible<S>(eq:spec_fn(S,S)->bool,left:Pair<S>,right:Pair<S>)->bool {
    &&& p::commutes(eq,left.forward,right.forward) && p::commutes(eq,left.forward,right.inverse)
    &&& p::commutes(eq,left.inverse,right.forward) && p::commutes(eq,left.inverse,right.inverse)
}
pub open spec fn catalog<S>(actions:Seq<Action<S>>)->Seq<Pair<S>>
    decreases actions.len(),
{
    if actions.len()==0 {Seq::empty()} else {
        let before=catalog(actions.drop_last());
        match actions.last() {Action::Forward {call}=>before.push(call),_=>before}
    }
}
pub open spec fn identity<S>()->m::PartialMap<S> {|state:S|Some(state)}
pub open spec fn event<S>(prior:Seq<Pair<S>>,action:Action<S>)->sj::Event<S> {
    match action {
        Action::Forward {call}=>sj::Event {forward:call.forward,inverse:call.inverse,own:call.own},
        Action::Inverse {token}=>sj::Event {forward:prior[token as int].inverse,inverse:prior[token as int].forward,own:false},
        Action::Identity=>sj::Event {forward:identity(),inverse:identity(),own:false},
    }
}
pub open spec fn events<S>(actions:Seq<Action<S>>)->Seq<sj::Event<S>>
    decreases actions.len(),
{
    if actions.len()==0 {Seq::empty()}
    else {events(actions.drop_last()).push(event(catalog(actions.drop_last()),actions.last()))}
}
pub open spec fn theory<S>(eq:spec_fn(S,S)->bool,records:Seq<Pair<S>>)->bool {
    &&& forall|i:int| 0<=i<records.len() ==> respectful(eq,#[trigger] records[i])
    &&& forall|i:int,j:int| 0<=i<records.len() && 0<=j<records.len() ==> compatible(eq,#[trigger] records[i],#[trigger] records[j])
}
pub open spec fn catalog_retracts<S>(eq:spec_fn(S,S)->bool,records:Seq<Pair<S>>,state:S)->bool {
    forall|i:int| 0<=i<records.len() ==> retracts(eq,#[trigger] records[i],state)
}

/// Only new actual forward calls supply their ordinary local inverse witness.
/// Authentic inverse calls select a prior record; their enabledness and reverse
/// witness are conclusions. No whole restore or surviving trace is a premise.
pub open spec fn local_source<S>(eq:spec_fn(S,S)->bool,actions:Seq<Action<S>>,initial:S)->bool
    decreases actions.len(),
{
    actions.len()==0 || {
        let prefix=actions.drop_last();let records=catalog(prefix);let input=sj::trace(events(prefix),initial);
        &&& local_source(eq,prefix,initial)
        &&& match actions.last() {
            Action::Forward {call}=>{
                &&& input.is_some() && (call.forward)(input.unwrap()).is_some()
                &&& (call.inverse)((call.forward)(input.unwrap()).unwrap()).is_some()
                &&& eq((call.inverse)((call.forward)(input.unwrap()).unwrap()).unwrap(),input.unwrap())
                &&& respectful(eq,call) && compatible(eq,call,call)
                &&& forall|i:int| 0<=i<records.len() ==> compatible(eq,#[trigger] records[i],call) && compatible(eq,call,#[trigger] records[i])
            },
            Action::Inverse {token}=>token<records.len() && !records[token as int].own,
            Action::Identity=>true,
        }
    }
}

pub proof fn local_forward_retracts<S>(eq:spec_fn(S,S)->bool,call:Pair<S>,input:S)
    requires (call.forward)(input).is_some(),(call.inverse)((call.forward)(input).unwrap()).is_some(),
        eq((call.inverse)((call.forward)(input).unwrap()).unwrap(),input),p::respects(eq,call.forward),
    ensures retracts(eq,call,(call.forward)(input).unwrap()),
{ }

/// Transport a historical call's reverse witness through one actual event.
/// Partial enabledness is derived using the event's actual inverse witness.
pub proof fn transport_retraction<S>(eq:spec_fn(S,S)->bool,call:Pair<S>,f:m::PartialMap<S>,undo:m::PartialMap<S>,input:S)
    requires c::equivalence(eq),retracts(eq,call,input),respectful(eq,call),p::respects(eq,f),
        f(input).is_some(),undo(f(input).unwrap()).is_some(),eq(undo(f(input).unwrap()).unwrap(),input),
        p::commutes(eq,f,call.inverse),p::commutes(eq,undo,call.inverse),p::commutes(eq,call.forward,f),
    ensures retracts(eq,call,f(input).unwrap()),
{
    let after=f(input).unwrap();let before_inverse=(call.inverse)(input).unwrap();
    domains::enabled_diamond(eq,f,call.inverse,undo,input);
    let shifted_inverse=f(before_inverse).unwrap();let actual_inverse=(call.inverse)(after).unwrap();
    assert(eq(shifted_inverse,actual_inverse));assert(eq(actual_inverse,shifted_inverse));
    let restored=(call.forward)(before_inverse).unwrap();assert(eq(restored,input));
    assert(f(restored).is_some());assert(eq(f(restored).unwrap(),after));
    assert(p::optional_equal(eq,p::compose(call.forward,f)(before_inverse),p::compose(f,call.forward)(before_inverse)));
    assert((call.forward)(shifted_inverse).is_some());
    assert(eq((call.forward)(shifted_inverse).unwrap(),f(restored).unwrap()));
    assert((call.forward)(actual_inverse).is_some());
    assert(eq((call.forward)(actual_inverse).unwrap(),(call.forward)(shifted_inverse).unwrap()));
    assert(eq((call.forward)(actual_inverse).unwrap(),after));
}

pub proof fn catalog_theory<S>(eq:spec_fn(S,S)->bool,actions:Seq<Action<S>>,initial:S)
    requires local_source(eq,actions,initial),
    ensures theory(eq,catalog(actions)),
    decreases actions.len(),
{
    if actions.len()>0 {
        let prefix=actions.drop_last();catalog_theory(eq,prefix,initial);
        let before=catalog(prefix);let records=catalog(actions);
        if let Action::Forward {call}=actions.last() {
            assert forall|i:int| 0<=i<records.len() implies respectful(eq,#[trigger] records[i]) by {
                if i<before.len() {assert(records[i]==before[i]);} else {assert(i==before.len());}
            }
            assert forall|i:int,j:int| 0<=i<records.len() && 0<=j<records.len() implies compatible(eq,#[trigger] records[i],#[trigger] records[j]) by {
                if i<before.len() {assert(records[i]==before[i]);}
                if j<before.len() {assert(records[j]==before[j]);}
            }
        }
    }
}
pub open spec fn catalog_origin<S>(records:Seq<Pair<S>>,inverse:m::PartialMap<S>)->bool {
    exists|j:int| 0<=j<records.len() && records[j].own && records[j].inverse==inverse
}
pub open spec fn journal_from_catalog<S>(actions:Seq<Action<S>>)->bool {
    let word=sj::journal(events(actions));let records=catalog(actions);
    forall|i:int| #![trigger word[i]] 0<=i<word.len() ==> catalog_origin(records,word[i])
}
pub proof fn journal_origins<S>(actions:Seq<Action<S>>)
    ensures journal_from_catalog(actions),
    decreases actions.len(),
{
    if actions.len()>0 {
        let prefix=actions.drop_last();journal_origins(prefix);
        let before=catalog(prefix);let records=catalog(actions);let old=sj::journal(events(prefix));let word=sj::journal(events(actions));
        let e=event(before,actions.last());assert(events(actions).drop_last() =~= events(prefix));
        assert forall|i:int| #![trigger word[i]] 0<=i<word.len() implies catalog_origin(records,word[i]) by {
            if e.own && i==0 {assert(records[records.len()-1].own);assert(records[records.len()-1].inverse==word[i]);}
            else {
                let at=if e.own {i-1} else {i};assert(0<=at<old.len());assert(word[i]==old[at]);
                let j=choose|j:int| 0<=j<before.len() && before[j].own && before[j].inverse==old[at];
                assert(0<=j<records.len());assert(records[j]==before[j]);
                assert(records[j].own && records[j].inverse==word[i]);
            }
        }
    }
}
pub proof fn identity_contract<S>(eq:spec_fn(S,S)->bool,f:m::PartialMap<S>)
    requires c::equivalence(eq),
    ensures p::respects(eq,identity::<S>()),p::commutes(eq,f,identity::<S>()),
{
    assert forall|state:S| #[trigger] p::optional_equal(eq,p::compose(f,identity())(state),p::compose(identity(),f)(state)) by {
        if f(state).is_some() {assert(eq(f(state).unwrap(),f(state).unwrap()));}
    }
}

/// Induction over actual new calls and authentic inverse tokens derives every
/// inverse's current local reverse witness, including repeated foreign Unload
/// fragments. It also discharges strict_journal's whole event admissibility.
pub proof fn source_invariant<S>(eq:spec_fn(S,S)->bool,actions:Seq<Action<S>>,initial:S)
    requires c::equivalence(eq),local_source(eq,actions,initial),
    ensures sj::trace(events(actions),initial).is_some(),catalog_retracts(eq,catalog(actions),sj::trace(events(actions),initial).unwrap()),
        sj::admissible(eq,events(actions),initial),
    decreases actions.len(),
{
    catalog_theory(eq,actions,initial);journal_origins(actions);
    if actions.len()>0 {
        let prefix=actions.drop_last();source_invariant(eq,prefix,initial);catalog_theory(eq,prefix,initial);journal_origins(prefix);
        let records=catalog(prefix);let all=catalog(actions);let es=events(prefix);let e=event(records,actions.last());let before=sj::trace(es,initial).unwrap();
        assert(events(actions).drop_last() =~= es);
        match actions.last() {
            Action::Forward {call}=>{local_forward_retracts(eq,call,before);},
            Action::Inverse {token}=>{assert(retracts(eq,records[token as int],before));},
            Action::Identity=>{identity_contract(eq,identity::<S>());assert(eq(before,before));},
        }
        assert((e.forward)(before).is_some());let after=(e.forward)(before).unwrap();
        assert((e.inverse)(after).is_some());assert(eq((e.inverse)(after).unwrap(),before));
        assert(p::respects(eq,e.forward));
        assert forall|i:int| 0<=i<all.len() implies retracts(eq,#[trigger] all[i],after) by {
            if i<records.len() {
                assert(all[i]==records[i]);assert(retracts(eq,records[i],before));
                match actions.last() {
                    Action::Forward {call}=>{assert(compatible(eq,call,records[i]));assert(compatible(eq,records[i],call));},
                    Action::Inverse {token}=>{assert(compatible(eq,records[token as int],records[i]));assert(compatible(eq,records[i],records[token as int]));},
                    Action::Identity=>{identity_contract(eq,records[i].forward);identity_contract(eq,records[i].inverse);p::commute_symmetric(eq,records[i].inverse,identity());},
                }
                transport_retraction(eq,records[i],e.forward,e.inverse,before);
            } else {assert(i==records.len());}
        }
        if !e.own {
            assert forall|i:int| 0<=i<sj::journal(es).len() implies p::commutes(eq,#[trigger] sj::journal(es)[i],e.forward)
                && p::commutes(eq,sj::journal(es)[i],e.inverse) by {
                let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];
                match actions.last() {
                    Action::Forward {call}=>{assert(compatible(eq,records[j],call));},
                    Action::Inverse {token}=>{assert(compatible(eq,records[j],records[token as int]));},
                    Action::Identity=>{identity_contract(eq,records[j].inverse);},
                }
            }
        }
    }
}

pub proof fn recovery_with_foreign_inverses<S>(eq:spec_fn(S,S)->bool,actions:Seq<Action<S>>,initial:S)
    requires c::equivalence(eq),local_source(eq,actions,initial),
    ensures sj::recovered(eq,events(actions),initial),
{
    source_invariant(eq,actions,initial);sj::recovery(eq,events(actions),initial);
}

/// Provenance required of a newly minted history entry. It names the actual
/// source input and raw interpreter result, not an unchecked callback promise.
pub open spec fn historical<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>)->bool {
    let actor=g::owner(entry.landed.receipt);let node=programs(actor)(entry.iterator);
    &&& inv::well_formed(entry.input) && replay::operational_mixed(node)
    &&& d::permitted(lib,dep::declarations(entry.input,actor),entry.input.control.fibers[actor].provisions,replay::dependent(node))
    &&& g::run(lib,node,entry.input,actor)==Some(entry.landed)
}
pub open spec fn entry_pair<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>,owner:usize)->Pair<IMap<Port,U>> {
    let actor=g::owner(entry.landed.receipt);let node=replay::dependent(programs(actor)(entry.iterator));
    Pair {forward:p::forward(dep::stage(lib,node)),inverse:crate::shared_execution::flat(entry.landed.receipt),own:actor==owner}
}
pub proof fn historical_contract<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),historical(lib,programs,entry),
    ensures {
        let call=entry_pair(lib,programs,entry,owner);let input=project::project(entry.input,ISet::full());let output=project::project(entry.landed.state,ISet::full());
        &&& respectful(p::context_eq(eq),call) && compatible(p::context_eq(eq),call,call)
        &&& (call.forward)(input)==Some(output) && (call.inverse)(output).is_some() && p::context_eq(eq)((call.inverse)(output).unwrap(),input)
    },
{
    let actor=g::owner(entry.landed.receipt);let node=replay::dependent(programs(actor)(entry.iterator));
    replay::call_contract(eq,lib,node,entry.input,actor,actor==owner);
    replay::actual_receipt_projects(lib,node,entry.input,actor);
    replay::stages_independent(eq,lib,node,node,dep::declarations(entry.input,actor),entry.input.control.fibers[actor].provisions,
        dep::declarations(entry.input,actor),entry.input.control.fibers[actor].provisions);
    assert(p::generators(dep::stage(lib,node)).contains(p::forward(dep::stage(lib,node))));
}
pub proof fn historical_independence<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,left:g::Entry<U,I>,right:g::Entry<U,I>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),historical(lib,programs,left),historical(lib,programs,right),
    ensures compatible(p::context_eq(eq),entry_pair(lib,programs,left,owner),entry_pair(lib,programs,right,owner)),
{
    let a=g::owner(left.landed.receipt);let b=g::owner(right.landed.receipt);
    let first=replay::dependent(programs(a)(left.iterator));let second=replay::dependent(programs(b)(right.iterator));
    replay::actual_receipt_projects(lib,first,left.input,a);replay::actual_receipt_projects(lib,second,right.input,b);
    replay::stages_independent(eq,lib,first,second,dep::declarations(left.input,a),left.input.control.fibers[a].provisions,
        dep::declarations(right.input,b),right.input.control.fibers[b].provisions);
    assert(p::generators(dep::stage(lib,first)).contains(p::forward(dep::stage(lib,first))));
    assert(p::generators(dep::stage(lib,second)).contains(p::forward(dep::stage(lib,second))));
}
pub proof fn landing_historical<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),
        replay::operational_mixed(programs(actor)(a.current[actor].unwrap())),
    ensures historical(lib,programs,g::entry(lib,programs,a,actor)),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());
}
pub open spec fn operational_trace<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)->bool {
    forall|i:int| 0<=i<labels.len() && g::landing(source[i],source[i+1],labels[i].1)
        ==> replay::operational_mixed(programs(labels[i].0)(source[i].current[labels[i].0].unwrap()))
}
pub proof fn fresh_historical<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),operational_trace(programs,source,labels),
    ensures g::well_formed(lib,programs,source.last()),source.first().history.len()<=source.last().history.len(),
        forall|i:int| 0<=i<source.first().history.len() ==> source.last().history[i]==source.first().history[i],
        forall|i:int| source.first().history.len()<=i<source.last().history.len() ==> historical(lib,programs,#[trigger] source.last().history[i]),
    decreases labels.len(),
{
    if labels.len()==0 {assert(source.first()==source.last());}
    else {
        let prefix=source.drop_last();let previous=labels.drop_last();let label=labels.last();
        assert(g::execution(lib,programs,prefix,previous));assert(operational_trace(programs,prefix,previous));
        fresh_historical(eq,lib,programs,prefix,previous);
        let a=prefix.last();let z=source.last();ol::frame(eq,lib,programs,a,z,label.0,label.1);
        ol::configuration_preservation(eq,lib,programs,a,z,label.0,label.1);
        if g::landing(a,z,label.1) {landing_historical(eq,lib,programs,a,z,label.0,label.1);}
        assert forall|i:int| source.first().history.len()<=i<z.history.len() implies historical(lib,programs,#[trigger] z.history[i]) by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());}
        }
    }
}

/// Map only entries minted in this execution segment. Older authentic history
/// remains in the source; it is not silently admitted as a reachable witness.
pub open spec fn fresh_records<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,history:Seq<g::Entry<U,I>>,offset:nat,owner:usize)->Seq<Pair<IMap<Port,U>>> {
    history.subrange(offset as int,history.len() as int).map(|_i:int,entry:g::Entry<U,I>|entry_pair(lib,programs,entry,owner))
}
pub open spec fn inverse_actions<S>(tokens:Seq<nat>,offset:nat)->Seq<Action<S>>
    decreases tokens.len(),
{
    if tokens.len()==0 {Seq::empty()}
    else {seq![Action::Inverse {token:(tokens.last()-offset) as nat}]+inverse_actions(tokens.drop_last(),offset)}
}
pub open spec fn step_actions<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,offset:nat,owner:usize)->Seq<Action<IMap<Port,U>>> {
    if g::landing(a,z,rule) {seq![Action::Forward {call:entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)}]}
    else if rule==r::Rule::Unload {inverse_actions(a.state.accumulators[actor],offset)}
    else {seq![Action::Identity]}
}
pub open spec fn trace_actions<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,offset:nat,owner:usize)->Seq<Action<IMap<Port,U>>>
    decreases labels.len(),
{
    if labels.len()==0 {Seq::empty()}
    else {trace_actions(lib,programs,source.drop_last(),labels.drop_last(),offset,owner)
        +step_actions(lib,programs,source[source.len()-2],source.last(),labels.last().0,labels.last().1,offset,owner)}
}
pub open spec fn tracked_tokens<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,actor:usize)->bool {
    forall|i:int| 0<=i<tokens.len() ==> offset<=tokens[i]<history.len() && g::owner(#[trigger] history[tokens[i] as int].landed.receipt)==actor
}
/// Foreign Unload is unrestricted in length and interleaving, but consumes
/// actual tokens minted in this segment. This explicit origin boundary avoids
/// assuming a reverse witness for an arbitrary pre-existing live journal.
pub open spec fn fragment<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,offset:nat,owner:usize)->bool {
    &&& operational_trace(programs,source,labels)
    &&& forall|i:int| #![trigger labels[i]] 0<=i<labels.len() ==> {
        let label=labels[i];
        &&& label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
        &&& (label.1==r::Rule::Unload ==> label.0!=owner && tracked_tokens(source[i].history,source[i].state.accumulators[label.0],offset,label.0))
    }
}
pub proof fn table_inverse_projects<U>(receipt:g::Receipt<U>,input:full::State<U>)
    requires inv::well_formed(input),g::undo(receipt,input).is_some(),match receipt {g::Receipt::Table {..}=>true,_=>false},
    ensures inv::well_formed(g::undo(receipt,input).unwrap()),
        crate::shared_execution::flat(receipt)(project::project(input,ISet::full()))==Some(project::project(g::undo(receipt,input).unwrap(),ISet::full())),
{
    if let g::Receipt::Table {receipt}=receipt {lift::undo_preservation(receipt,input);lift::inverse_projects(receipt,input);}
}

/// Unfold the actual LIFO restore. Every inverse action acquires the original
/// forward as its current reverse witness through source_invariant; source
/// success merely identifies the observed full-state result of that real step.
#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn actual_restore_actions<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,actor:usize,owner:usize,input:full::State<U>,prefix:Seq<Action<IMap<Port,U>>>,initial:IMap<Port,U>)
    requires og::primitive_theory(eq,lib),inv::well_formed(input),actor!=owner,offset<=history.len(),tracked_tokens(history,tokens,offset,actor),
        forall|i:int| offset<=i<history.len() ==> historical(lib,programs,#[trigger] history[i]),
        local_source(p::context_eq(eq),prefix,initial),catalog(prefix)==fresh_records(lib,programs,history,offset,owner),
        sj::trace(events(prefix),initial)==Some(project::project(input,ISet::full())),g::restore(history,tokens,input,actor).is_some(),
    ensures {
        let extended=prefix+inverse_actions(tokens,offset);
        &&& local_source(p::context_eq(eq),extended,initial) && catalog(extended)==catalog(prefix)
        &&& sj::trace(events(extended),initial)==Some(project::project(g::restore(history,tokens,input,actor).unwrap(),ISet::full()))
    },
    decreases tokens.len(),
{
    replay::context_equivalence(eq,lib);
    if tokens.len()==0 {assert(prefix+inverse_actions::<IMap<Port,U>>(tokens,offset) =~= prefix);}
    else {
        let token=tokens.last();let at=(token-offset) as nat;let entry=history[token as int];let action=Action::Inverse {token:at};let next_prefix=prefix.push(action);
        assert(offset<=token<history.len());assert(g::owner(entry.landed.receipt)==actor);assert(historical(lib,programs,entry));
        assert(0<=at<catalog(prefix).len());assert(catalog(prefix)[at as int]==entry_pair(lib,programs,entry,owner));
        assert(next_prefix.drop_last() =~= prefix);assert(local_source(p::context_eq(eq),next_prefix,initial));
        assert(catalog(next_prefix)==catalog(prefix));
        assert(events(next_prefix) =~= events(prefix).push(event(catalog(prefix),action)));
        assert(events(next_prefix).drop_last() =~= events(prefix));
        let after=g::undo(entry.landed.receipt,input).unwrap();
        table_inverse_projects(entry.landed.receipt,input);
        assert(sj::trace(events(next_prefix),initial)==Some(project::project(after,ISet::full())));
        actual_restore_actions(eq,lib,programs,history,tokens.drop_last(),offset,actor,owner,after,next_prefix,initial);
        assert(next_prefix+inverse_actions::<IMap<Port,U>>(tokens.drop_last(),offset) =~= prefix+inverse_actions::<IMap<Port,U>>(tokens,offset));
    }
}

pub proof fn forward_extension<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,offset:nat,owner:usize,prefix:Seq<Action<IMap<Port,U>>>,initial:IMap<Port,U>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),
        replay::operational_mixed(programs(actor)(a.current[actor].unwrap())),offset<=a.history.len(),
        forall|i:int| offset<=i<a.history.len() ==> historical(lib,programs,#[trigger] a.history[i]),
        local_source(p::context_eq(eq),prefix,initial),catalog(prefix)==fresh_records(lib,programs,a.history,offset,owner),
        sj::trace(events(prefix),initial)==Some(project::project(a.state,ISet::full())),
    ensures {
        let actions=prefix.push(Action::Forward {call:entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)});
        &&& local_source(p::context_eq(eq),actions,initial) && catalog(actions)==fresh_records(lib,programs,z.history,offset,owner)
        &&& sj::trace(events(actions),initial)==Some(project::project(z.state,ISet::full()))
    },
{
    ol::frame(eq,lib,programs,a,z,actor,rule);
    let entry=g::entry(lib,programs,a,actor);let call=entry_pair(lib,programs,entry,owner);let records=catalog(prefix);
    let actions=prefix.push(Action::Forward {call});
    landing_historical(eq,lib,programs,a,z,actor,rule);historical_contract(eq,lib,programs,entry,owner);
    assert(actions.drop_last() =~= prefix);assert(events(actions).drop_last() =~= events(prefix));
    assert forall|i:int| 0<=i<records.len() implies compatible(p::context_eq(eq),#[trigger] records[i],call) && compatible(p::context_eq(eq),call,#[trigger] records[i]) by {
        let old=a.history[offset as int+i];assert(historical(lib,programs,old));assert(records[i]==entry_pair(lib,programs,old,owner));
        historical_independence(eq,lib,programs,old,entry,owner);historical_independence(eq,lib,programs,entry,old,owner);
    }
    assert(local_source(p::context_eq(eq),actions,initial));
    assert(fresh_records(lib,programs,z.history,offset,owner) =~= records.push(call));
    lift::run_preservation(dep::stage(lib,replay::dependent(programs(actor)(entry.iterator))),a.state,actor);
    project::unique_owner(entry.landed.state);
    project::lifecycle_edit(entry.landed.state,actor,z.state.control.fibers[actor].phase,a.state.control.fibers[actor].committed,
        z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
}
pub proof fn identity_extension<S>(eq:spec_fn(S,S)->bool,prefix:Seq<Action<S>>,initial:S)
    requires local_source(eq,prefix,initial),
    ensures local_source(eq,prefix.push(Action::Identity),initial),catalog(prefix.push(Action::Identity))==catalog(prefix),
        sj::trace(events(prefix.push(Action::Identity)),initial)==sj::trace(events(prefix),initial),
{
    assert(prefix.push(Action::Identity).drop_last() =~= prefix);assert(events(prefix.push(Action::Identity)).drop_last() =~= events(prefix));
}

/// Interpret a real mixed execution, flattening successful foreign Unloads in
/// their exact LIFO order. New operation witnesses and pairwise library laws
/// derive the catalog and event invariants rather than requiring a profile.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_source<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fragment(programs,source,labels,source.first().history.len(),owner),
    ensures {
        let offset=source.first().history.len();let actions=trace_actions(lib,programs,source,labels,offset,owner);let initial=project::project(source.first().state,ISet::full());
        &&& local_source(p::context_eq(eq),actions,initial)
        &&& catalog(actions)==fresh_records(lib,programs,source.last().history,offset,owner)
        &&& sj::trace(events(actions),initial)==Some(project::project(source.last().state,ISet::full()))
        &&& g::well_formed(lib,programs,source.last())
    },
    decreases labels.len(),
{
    replay::context_equivalence(eq,lib);fresh_historical(eq,lib,programs,source,labels);
    let offset=source.first().history.len();let actions=trace_actions(lib,programs,source,labels,offset,owner);let initial=project::project(source.first().state,ISet::full());
    if labels.len()==0 {
        assert(source.first()==source.last());assert(fresh_records(lib,programs,source.last().history,offset,owner) =~= Seq::empty());
    } else {
        let states=source.drop_last();let previous=labels.drop_last();let label=labels.last();let a=states.last();let z=source.last();let actor=label.0;let rule=label.1;
        assert(g::execution(lib,programs,states,previous));assert(fragment(programs,states,previous,offset,owner));
        actual_source(eq,lib,programs,states,previous,owner);fresh_historical(eq,lib,programs,states,previous);
        let prefix=trace_actions(lib,programs,states,previous,offset,owner);let records=catalog(prefix);
        ol::frame(eq,lib,programs,a,z,actor,rule);
        if g::landing(a,z,rule) {
            assert(actions =~= prefix.push(Action::Forward {call:entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)}));
            forward_extension(eq,lib,programs,a,z,actor,rule,offset,owner,prefix,initial);
        } else if rule==r::Rule::Unload {
            actual_restore_actions(eq,lib,programs,a.history,a.state.accumulators[actor],offset,actor,owner,a.state,prefix,initial);
            g::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
            let restored=g::restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();project::unique_owner(restored);
            project::lifecycle_edit(restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
        } else {
            assert(actions =~= prefix.push(Action::Identity));identity_extension(p::context_eq(eq),prefix,initial);
            replay::event_contract(eq,lib,programs,a,z,actor,rule,owner);
            assert(project::project(a.state,ISet::full())==project::project(z.state,ISet::full()));
        }
    }
}

pub proof fn actual_foreign_unload_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fragment(programs,source,labels,source.first().history.len(),owner),
    ensures {
        let actions=trace_actions(lib,programs,source,labels,source.first().history.len(),owner);let initial=project::project(source.first().state,ISet::full());
        &&& sj::foreign(events(actions),initial).is_some()
        &&& p::run(sj::journal(events(actions)),project::project(source.last().state,ISet::full())).is_some()
        &&& p::context_eq(eq)(p::run(sj::journal(events(actions)),project::project(source.last().state,ISet::full())).unwrap(),sj::foreign(events(actions),initial).unwrap())
        &&& catalog_retracts(p::context_eq(eq),catalog(actions),project::project(source.last().state,ISet::full()))
    },
{
    actual_source(eq,lib,programs,source,labels,owner);replay::context_equivalence(eq,lib);
    let actions=trace_actions(lib,programs,source,labels,source.first().history.len(),owner);let initial=project::project(source.first().state,ISet::full());
    source_invariant(p::context_eq(eq),actions,initial);recovery_with_foreign_inverses(p::context_eq(eq),actions,initial);
}

pub proof fn inverse_actions_journal<S>(prefix:Seq<Action<S>>,tokens:Seq<nat>,offset:nat)
    ensures catalog(prefix+inverse_actions(tokens,offset))==catalog(prefix),
        sj::journal(events(prefix+inverse_actions(tokens,offset)))==sj::journal(events(prefix)),
    decreases tokens.len(),
{
    if tokens.len()==0 {assert(prefix+inverse_actions::<S>(tokens,offset) =~= prefix);}
    else {
        let action=Action::Inverse {token:(tokens.last()-offset) as nat};let next=prefix.push(action);
        assert(next.drop_last() =~= prefix);assert(events(next).drop_last() =~= events(prefix));
        inverse_actions_journal(next,tokens.drop_last(),offset);
        assert(next+inverse_actions::<S>(tokens.drop_last(),offset) =~= prefix+inverse_actions::<S>(tokens,offset));
    }
}
/// Actual operational receipts have no control effect. This follows from the
/// recorded syntax; a Child retirement is never silently erased by this frame.
pub proof fn restore_control<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,input:full::State<U>,actor:usize)
    requires inv::well_formed(input),tracked_tokens(history,tokens,offset,actor),g::restore(history,tokens,input,actor).is_some(),
        forall|i:int| offset<=i<history.len() ==> historical(lib,programs,#[trigger] history[i]),
    ensures g::restore(history,tokens,input,actor).unwrap().control==input.control,
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let entry=history[tokens.last() as int];assert(historical(lib,programs,entry));
        let next=g::undo(entry.landed.receipt,input).unwrap();table_inverse_projects(entry.landed.receipt,input);
        if let g::Receipt::Table {receipt}=entry.landed.receipt {lift::undo_preservation(receipt,input);}
        assert(next.control==input.control);restore_control(lib,programs,history,tokens.drop_last(),offset,next,actor);
    }
}

/// Link the abstract pending owner word to its actual live journal, even while
/// foreign journals are being strictly unloaded in arbitrary LIFO lengths.
pub proof fn actual_journal<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fragment(programs,source,labels,source.first().history.len(),owner),full::registered(source.first().state,owner),source.first().state.control.fibers[owner].phase==Phase::Inactive,
    ensures {
        let last=source.last();let actions=trace_actions(lib,programs,source,labels,source.first().history.len(),owner);
        &&& g::well_formed(lib,programs,last) && full::registered(last.state,owner)
        &&& r::interface_same(source.first().state.control.fibers[owner],last.state.control.fibers[owner])
        &&& shared::pinned_tokens(last.history,last.state.accumulators[owner],last.state,owner)
        &&& shared::receipt_word(last.history,last.state.accumulators[owner])==sj::journal(events(actions))
    },
    decreases labels.len(),
{
    fresh_historical(eq,lib,programs,source,labels);
    if labels.len()==0 {assert(source.first()==source.last());assert(source.first().state.accumulators[owner].len()==0);}
    else {
        let states=source.drop_last();let previous=labels.drop_last();let label=labels.last();let a=states.last();let z=source.last();let actor=label.0;let rule=label.1;
        let offset=source.first().history.len();let prefix=trace_actions(lib,programs,states,previous,offset,owner);let actions=trace_actions(lib,programs,source,labels,offset,owner);
        assert(g::execution(lib,programs,states,previous));assert(fragment(programs,states,previous,offset,owner));
        actual_journal(eq,lib,programs,states,previous,owner);fresh_historical(eq,lib,programs,states,previous);
        ol::frame(eq,lib,programs,a,z,actor,rule);
        if rule!=r::Rule::Unload {
            assert(replay::fragment_step(programs,a,z,actor,rule));shared::journal_step(eq,lib,programs,a,z,events(prefix),owner,actor,rule);
            if g::landing(a,z,rule) {
                assert(actions =~= prefix.push(Action::Forward {call:entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)}));
                assert(event(catalog(prefix),actions.last())==replay::event(lib,programs,a,z,actor,rule,owner));
            } else {
                assert(actions =~= prefix.push(Action::Identity));
                assert(identity::<IMap<Port,U>>() =~= replay::identity::<U>());
                assert(event(catalog(prefix),actions.last())==replay::event(lib,programs,a,z,actor,rule,owner));
            }
            assert(actions.drop_last() =~= prefix);
            assert(events(actions) =~= events(prefix).push(replay::event(lib,programs,a,z,actor,rule,owner)));
        } else {
            restore_control(lib,programs,a.history,a.state.accumulators[actor],offset,a.state,actor);
            inverse_actions_journal(prefix,a.state.accumulators[actor],offset);
            assert(z.history==a.history);assert(z.state.accumulators[owner]==a.state.accumulators[owner]);
            assert(z.state.control.fibers[owner]==a.state.control.fibers[owner]);
            shared::resolution_frame(a.state,z.state,owner);
            assert forall|i:int| 0<=i<z.state.accumulators[owner].len() implies z.state.accumulators[owner][i]<z.history.len()
                && shared::pinned(#[trigger] z.history[z.state.accumulators[owner][i] as int].landed.receipt,z.state,owner) by {
                let token=z.state.accumulators[owner][i];assert(shared::pinned(a.history[token as int].landed.receipt,a.state,owner));
                match a.history[token as int].landed.receipt {
                    g::Receipt::Table {receipt}=>{match receipt.inverse {lift::Inverse::Operation {key,..}=>{assert(lift::resolve(a.state,owner,key)==lift::resolve(z.state,owner,key));},_=>{}}},_=>{},
                }
            }
        }
    }
}

/// Foreign inverses now contribute proved local reverse witnesses, so a final
/// own Unload is also enabled after those foreign Unloads. The final comparison
/// is a strict value replay; constructing the surviving target journals is a
/// separate lifecycle-transport theorem, not inferred by this result.
pub proof fn terminal_with_foreign_unloads<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        fragment(programs,source,labels,source.first().history.len(),owner),full::registered(source.first().state,owner),source.first().state.control.fibers[owner].phase==Phase::Inactive,
        source.first().state.control.fibers[owner].provisions.is_empty(),source.last().state.control.fibers[owner].phase==Phase::Unloading,
    ensures {
        let last=source.last();let terminal=g::unload(last,owner);let actions=trace_actions(lib,programs,source,labels,source.first().history.len(),owner);let initial=project::project(source.first().state,ISet::full());
        &&& g::restore(last.history,last.state.accumulators[owner],last.state,owner).is_some()
        &&& g::step(lib,programs,last,terminal,owner,r::Rule::Unload) && g::well_formed(lib,programs,terminal)
        &&& sj::foreign(events(actions),initial).is_some()
        &&& p::context_eq(eq)(project::project(terminal.state,ISet::full()),sj::foreign(events(actions),initial).unwrap())
    },
{
    actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);actual_journal(eq,lib,programs,source,labels,owner);
    let last=source.last();shared::restore_definedness(last.history,last.state.accumulators[owner],last.state,owner);
    assert(last.state.control.fibers[owner].provisions.is_empty());
    assert(!r::relied(last.state.control,owner)) by {
        if r::relied(last.state.control,owner) {
            let (n,b)=choose|n:usize,b:Binding| full::registered(last.state,n) && n!=owner && last.state.control.fibers[n].phase!=Phase::Inactive
                && last.state.control.fibers[n].committed.contains(b) && b.provider==owner;
            let key=Port {key:b.key,realm:b.realm};assert(last.state.control.fibers[owner].provisions.contains(key));
        }
    }
    let terminal=g::unload(last,owner);assert(g::step(lib,programs,last,terminal,owner,r::Rule::Unload));
    ol::configuration_preservation(eq,lib,programs,last,terminal,owner,r::Rule::Unload);
    let restored=g::restore(last.history,last.state.accumulators[owner],last.state,owner).unwrap();project::unique_owner(restored);
    project::lifecycle_edit(restored,owner,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
}

#[verifier::opaque]
pub open spec fn mixed_trace()->Seq<g::Configuration<int,bool>> {
    let before=shared::example_trace();let retired=shared::retire(before.last(),2);
    let leaving=g::edit(retired,2,Phase::Unloading,retired.state.control.fibers[2usize].committed,None,retired.state.accumulators[2usize]);
    before.push(retired).push(leaving).push(g::unload(leaving,2))
}
pub open spec fn mixed_labels()->Seq<(usize,r::Rule)> {
    shared::example_labels().push((2usize,r::Rule::Retire)).push((2usize,r::Rule::Leave)).push((2usize,r::Rule::Unload))
}
#[verifier::rlimit(30)]
pub proof fn mixed_execution()
    ensures g::execution(ex::library(),shared::example_programs(),mixed_trace(),mixed_labels()),
        g::well_formed(ex::library(),shared::example_programs(),mixed_trace().first()),
        fragment(shared::example_programs(),mixed_trace(),mixed_labels(),mixed_trace().first().history.len(),1),
        mixed_trace().first().history.len()==1,mixed_trace().last().history.len()==3,
        full::registered(mixed_trace().first().state,1),mixed_trace().first().state.control.fibers[1usize].phase==Phase::Inactive,
        mixed_trace().first().state.control.fibers[1usize].provisions.is_empty(),mixed_trace().last().state.control.fibers[1usize].phase==Phase::Unloading,
{
    reveal(mixed_trace);reveal(shared::example_trace);shared::example_execution();shared::example_interface();
    let states=mixed_trace();let labels=mixed_labels();let lib=ex::library();let programs=shared::example_programs();let old=shared::example_trace();
    assert(old.len()==7);assert(labels.len()==9);assert(states.len()==10);
    ch::concrete_child_retirement(old.last().state,2);assert(g::step(lib,programs,states[6],states[7],2,r::Rule::Retire));
    assert(g::step(lib,programs,states[7],states[8],2,r::Rule::Leave));
    let before=states.drop_last();let previous=labels.drop_last();
    assert(g::execution(lib,programs,before,previous)) by {
        assert forall|i:int| 0<=i<previous.len() implies g::step(lib,programs,before[i],before[i+1],previous[i].0,previous[i].1) by {
            if i<6 {assert(before[i]==old[i]);assert(before[i+1]==old[i+1]);assert(previous[i]==shared::example_labels()[i]);}
            else if i==6 {} else {assert(i==7);}
        }
    }
    assert(replay::fragment(programs,before,previous)) by {
        assert forall|i:int| 0<=i<previous.len() implies replay::fragment_step(programs,before[i],before[i+1],previous[i].0,previous[i].1) by {
            if i<6 {assert(before[i]==old[i]);assert(before[i+1]==old[i+1]);assert(previous[i]==shared::example_labels()[i]);}
            else if i==6 {} else {assert(i==7);}
        }
    }
    reveal(shared::example_trace);
    shared::terminal_deletion(ex::equality(),lib,programs,before,previous,2);
    assert(g::step(lib,programs,states[8],states[9],2,r::Rule::Unload));
    assert(g::execution(lib,programs,states,labels)) by {
        assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,states[i],states[i+1],labels[i].0,labels[i].1) by {
            if i<8 {assert(states[i]==before[i]);assert(states[i+1]==before[i+1]);assert(labels[i]==previous[i]);} else {assert(i==8);}
        }
    }
    ol::execution_preservation(ex::equality(),lib,programs,states,labels);
    g::restore_preservation(lib,programs,states[8].history,states[8].state.accumulators[2usize],states[8].state,2);
    let restored=g::restore(states[8].history,states[8].state.accumulators[2usize],states[8].state,2).unwrap();
    assert(full::registered(states[8].state,1));
    assert(ch::recovery_frame(states[8].state,restored));
    assert(restored.control.fibers[1usize].phase==states[8].state.control.fibers[1usize].phase);
    assert(states[9].state.control.fibers[1usize].phase==states[8].state.control.fibers[1usize].phase);
    assert(states[8].state.accumulators[2usize] =~= seq![2nat]);
    assert forall|i:int| 0<=i<labels.len() && g::landing(states[i],states[i+1],labels[i].1)
        implies replay::operational_mixed(programs(labels[i].0)(states[i].current[labels[i].0].unwrap())) by {
        if i<8 {assert(before[i]==states[i]);assert(before[i+1]==states[i+1]);assert(previous[i]==labels[i]);} else {assert(i==8);}
    }
    assert forall|i:int| #![trigger labels[i]] 0<=i<labels.len() implies {
        let label=labels[i];
        &&& label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
        &&& (label.1==r::Rule::Unload ==> label.0!=1 && tracked_tokens(states[i].history,states[i].state.accumulators[label.0],1,label.0))
    } by {
        if i<6 {assert(labels[i]==shared::example_labels()[i]);}
        else if i==6 {} else if i==7 {} else {assert(i==8);}
    }
}

/// Actual shared-key trace: foreign +7 is genuinely unloaded before the owner's
/// final -5. Both strict domains and the owner's final lifecycle guard follow
/// from original receipts; the nonempty initial provider history is retained.
pub proof fn mixed_foreign_unload_example()
    ensures {
        let source=mixed_trace();let final_state=g::unload(source.last(),1);
        let actions=trace_actions(ex::library(),shared::example_programs(),source,mixed_labels(),1,1);
        let initial=project::project(source.first().state,ISet::full());
        &&& g::step(ex::library(),shared::example_programs(),source.last(),final_state,1,r::Rule::Unload)
        &&& g::well_formed(ex::library(),shared::example_programs(),final_state)
        &&& source.first().history.len()==1 && final_state.history.len()==3
        &&& sj::foreign(events(actions),initial).is_some()
        &&& p::context_eq(ex::equality())(project::project(final_state.state,ISet::full()),sj::foreign(events(actions),initial).unwrap())
    },
{
    mixed_execution();shared::example_interface();terminal_with_foreign_unloads(ex::equality(),ex::library(),shared::example_programs(),mixed_trace(),mixed_labels(),1);
}

pub open spec fn shift_call(amount:int,own:bool)->Pair<(bool,int)> {Pair {forward:sj::shift(amount),inverse:sj::shift(-amount),own}}
pub proof fn shift_compatible(left:int,right:int,a:bool,b:bool)
    ensures respectful(|a:(bool,int),b:(bool,int)|a==b,shift_call(left,a)),
        compatible(|a:(bool,int),b:(bool,int)|a==b,shift_call(left,a),shift_call(right,b)),
{
    sj::shift_commutes(left,right);sj::shift_commutes(left,-right);sj::shift_commutes(-left,right);sj::shift_commutes(-left,-right);
}
pub proof fn actual_foreign_inverse_example()
    ensures {
        let actions=seq![Action::Forward {call:shift_call(5,true)},Action::Forward {call:shift_call(3,false)},
            Action::Forward {call:shift_call(2,true)},Action::Inverse {token:1nat},Action::Forward {call:shift_call(4,false)}];
        let eq=|a:(bool,int),b:(bool,int)|a==b;
        &&& local_source(eq,actions,(true,0int))
        &&& sj::trace(events(actions),(true,0int))==Some((true,11int))
        &&& sj::foreign(events(actions),(true,0int))==Some((true,4int))
        &&& p::run(sj::journal(events(actions)),(true,11int))==Some((true,4int))
        &&& sj::trace(events(actions),(false,0int)).is_none()
    },
{
    let actions=seq![Action::Forward {call:shift_call(5,true)},Action::Forward {call:shift_call(3,false)},
        Action::Forward {call:shift_call(2,true)},Action::Inverse {token:1nat},Action::Forward {call:shift_call(4,false)}];
    let eq=|a:(bool,int),b:(bool,int)|a==b;
    assert(c::equivalence(eq));
    shift_compatible(5,5,true,true);shift_compatible(3,3,false,false);shift_compatible(2,2,true,true);shift_compatible(4,4,false,false);
    shift_compatible(5,3,true,false);shift_compatible(3,5,false,true);shift_compatible(5,2,true,true);shift_compatible(2,5,true,true);
    shift_compatible(5,4,true,false);shift_compatible(4,5,false,true);shift_compatible(3,2,false,true);shift_compatible(2,3,true,false);
    shift_compatible(3,4,false,false);shift_compatible(4,3,false,false);shift_compatible(2,4,true,false);shift_compatible(4,2,false,true);
    reveal_with_fuel(events,6);reveal_with_fuel(catalog,6);reveal_with_fuel(local_source,6);reveal_with_fuel(sj::trace,6);
    assert(local_source(eq,actions,(true,0int)));
    recovery_with_foreign_inverses(eq,actions,(true,0int));reveal_with_fuel(sj::foreign,6);
}

/// A historical primitive witness alone says nothing about an arbitrary later
/// input. Reachability/transport is essential to deriving inverse-of-inverse.
pub proof fn history_alone_is_insufficient()
    ensures {
        let forward=|v:int|if v==0 {Some(0int)} else {None};let inverse=|v:int|Some(v);
        &&& forward(0).is_some() && inverse(forward(0).unwrap())==Some(0int)
        &&& p::commutes(|a:int,b:int|a==b,forward,inverse)
        &&& inverse(1).is_some() && forward(inverse(1).unwrap()).is_none()
    },
{
    let forward=|v:int|if v==0 {Some(0int)} else {None};let inverse=|v:int|Some(v);let eq=|a:int,b:int|a==b;
    assert forall|v:int| #[trigger] p::optional_equal(eq,p::compose(forward,inverse)(v),p::compose(inverse,forward)(v)) by {}
}

} // verus!
