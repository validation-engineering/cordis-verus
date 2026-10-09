//! Recovery infrastructure for deleting an owner that provisions private keys.
//!
//! Other declared interfaces avoid the owner's provisions, while operations on
//! shared dependencies retain the strict value-independence contract. Own
//! Provision calls use their actual local inverse; no self-commutation is added.
#[cfg(verus_keep_ghost)]
use crate::foreign_unload::{
    catalog, entry_pair, event, events, fresh_records, inverse_actions, table_inverse_projects,
    trace_actions, tracked_tokens, Action,
};
#[cfg(verus_keep_ghost)]
use crate::selective_foreign_recovery::{
    catalog_retracts, local_source, recovery_with_foreign_inverses, source_invariant,
};
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, dependent_grammar as d, dependent_lift as dep, foreign_unload as fu,
    grammar_lift as lift, mediated as m, mixed_grammar as g, mixed_observational_runs as obs,
    observational_grammar as og, observational_lift as ol, partial_independence as p,
    preservation as inv, projection as project, refinement as r,
    selective_foreign_recovery as selective, semantics as full, shared_execution as shared,
    shared_replay as replay, shared_unload_execution as sue, strict_journal as sj, Binding, Phase,
    Port,
};
use vstd::prelude::*;

verus! {
pub open spec fn separated<U>(a:full::State<U>,owner:usize)->bool {
    &&& full::registered(a,owner)
    &&& forall|n:usize| full::registered(a,n) && n!=owner ==> dep::declarations(a,n).disjoint(a.control.fibers[owner].provisions)
}
pub open spec fn table_node<A,X,U,B,I>(node:g::Node<A,X,U,B,I>)->bool {match node {g::Node::Dependent {..}=>true,_=>false}}
pub open spec fn fragment<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,offset:nat,owner:usize)->bool {
    &&& forall|i:int| 0<=i<labels.len() && g::landing(source[i],source[i+1],labels[i].1) ==> {
        let node=programs(labels[i].0)(source[i].current[labels[i].0].unwrap());
        table_node(node) && (labels[i].0!=owner ==> replay::operational_mixed(node))
    }
    &&& forall|i:int| #![trigger labels[i]] 0<=i<labels.len() ==> {
        let label=labels[i];
        &&& label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
        &&& (label.1==r::Rule::Unload ==> label.0!=owner && fu::tracked_tokens(source[i].history,source[i].state.accumulators[label.0],offset,label.0))
    }
}
pub proof fn interface_frame<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),separated(a.state,owner),
        rule!=r::Rule::Insert,rule!=r::Rule::Remove,g::landing(a,z,rule) ==> table_node(programs(actor)(a.current[actor].unwrap())),
    ensures separated(z.state,owner),a.state.control.fibers.dom()==z.state.control.fibers.dom(),
        forall|n:usize| full::registered(a.state,n) ==> r::interface_same(a.state.control.fibers[n],z.state.control.fibers[n]),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);
    if g::landing(a,z,rule) {lift::run_preservation(dep::stage(lib,replay::dependent(programs(actor)(a.current[actor].unwrap()))),a.state,actor);}
    if rule==r::Rule::Unload {g::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    assert(full::registered(a.state,actor));assert(full::registered(z.state,actor));
    assert(a.state.control.fibers.dom() =~= z.state.control.fibers.dom()) by {
        assert forall|n:usize| a.state.control.fibers.dom().contains(n)==z.state.control.fibers.dom().contains(n) by {
            if n!=actor && full::registered(z.state,n) && !full::registered(a.state,n) {assert(g::landing(a,z,rule));assert(g::entry(lib,programs,a,actor).landed.spawn.is_none());}
        }
    }
    assert forall|n:usize| full::registered(z.state,n) && n!=owner implies dep::declarations(z.state,n).disjoint(z.state.control.fibers[owner].provisions) by {
        assert(full::registered(a.state,n));assert(dep::declarations(a.state,n)==dep::declarations(z.state,n));
    }
}

/// Entries retain their actual typed input, raw result, and private-interface
/// classification; this is derived for every newly appended source entry.
pub open spec fn historical<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>,owner:usize,private:ISet<Port>)->bool {
    let actor=g::owner(entry.landed.receipt);let node=programs(actor)(entry.iterator);
    &&& inv::well_formed(entry.input) && dep::typed(lib,entry.input) && dep::finite_context(entry.input)
    &&& table_node(node) && (actor!=owner ==> replay::operational_mixed(node) && dep::declarations(entry.input,actor).disjoint(private))
    &&& (actor==owner ==> entry.input.control.fibers[actor].provisions==private)
    &&& d::permitted(lib,dep::declarations(entry.input,actor),entry.input.control.fibers[actor].provisions,replay::dependent(node))
    &&& g::run(lib,node,entry.input,actor)==Some(entry.landed)
}
pub proof fn landing_historical<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),separated(a.state,owner),
        table_node(programs(actor)(a.current[actor].unwrap())),actor!=owner ==> replay::operational_mixed(programs(actor)(a.current[actor].unwrap())),
    ensures historical(lib,programs,g::entry(lib,programs,a,actor),owner,a.state.control.fibers[owner].provisions),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());
}
pub proof fn stage_respects<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,keys:ISet<Port>,provided:ISet<Port>)
    requires og::primitive_theory(eq,lib),d::permitted(lib,keys,provided,node),
    ensures m::stage_respects(eq,ISet::full(),dep::stage(lib,node)),
{
    if let d::Node::Provision {key,value,next}=node {
        assert(m::key_equivalence(eq,key));let local=|a:U,b:U|eq(key,a,b);assert(c::equivalence(local));assert(local(value,value));m::provision_admissible::<Port,U,B>(eq,ISet::full(),key,value,dep::marker(next));
    } else {replay::stage_respects(eq,lib,node,keys,provided);}
}
pub proof fn historical_contract<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>,owner:usize,private:ISet<Port>)
    requires og::primitive_theory(eq,lib),historical(lib,programs,entry,owner,private),
    ensures {
        let call=fu::entry_pair(lib,programs,entry,owner);let input=project::project(entry.input,ISet::full());let output=project::project(entry.landed.state,ISet::full());
        &&& fu::respectful(p::context_eq(eq),call)
        &&& (call.forward)(input)==Some(output) && (call.inverse)(output).is_some() && p::context_eq(eq)((call.inverse)(output).unwrap(),input)
    },
{
    let actor=g::owner(entry.landed.receipt);let node=replay::dependent(programs(actor)(entry.iterator));let stage=dep::stage(lib,node);let call=fu::entry_pair(lib,programs,entry,owner);
    replay::context_equivalence(eq,lib);replay::actual_receipt_projects(lib,node,entry.input,actor);
    stage_respects(eq,lib,node,dep::declarations(entry.input,actor),entry.input.control.fibers[actor].provisions);
    assert(p::generators(stage).contains(p::forward(stage)));p::generator_respects(eq,stage,call.forward);p::generator_respects(eq,stage,call.inverse);
    ol::dependent_run_admissible(eq,lib,node,entry.input,actor);fu::table_inverse_projects(entry.landed.receipt,entry.landed.state);
    lift::run_projects(stage,entry.input,actor);
}

pub proof fn stages_cross<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,left:dep::Node<A,X,U,B,I>,right:dep::Node<A,X,U,B,J>,
    left_keys:ISet<Port>,left_provided:ISet<Port>,right_keys:ISet<Port>,right_provided:ISet<Port>,left_own:bool,right_own:bool)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),!left_own || !right_own,
        !left_own ==> replay::operational(left),!right_own ==> replay::operational(right),
        left_own ==> left_provided.disjoint(right_keys),right_own ==> right_provided.disjoint(left_keys),
        d::permitted(lib,left_keys,left_provided,left),d::permitted(lib,right_keys,right_provided,right),
    ensures p::independent(eq,dep::stage(lib,left),dep::stage(lib,right)),
{
    replay::context_equivalence(eq,lib);stage_respects(eq,lib,left,left_keys,left_provided);stage_respects(eq,lib,right,right_keys,right_provided);
    if replay::operational(left) && replay::operational(right) {replay::stages_independent(eq,lib,left,right,left_keys,left_provided,right_keys,right_provided);}
    else {
        match left {
            d::Node::Unit=>{p::unit_independence::<Port,U,B,B>(eq,dep::stage(lib,right));},
            _=>{match right {
                d::Node::Unit=>{p::unit_independence::<Port,U,B,B>(eq,dep::stage(lib,left));},
                _=>{p::distinct_nodes(eq,dep::stage(lib,left),dep::stage(lib,right));},
            }},
        }
    }
}
pub proof fn historical_independence<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,left:g::Entry<U,I>,right:g::Entry<U,I>,owner:usize,private:ISet<Port>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),historical(lib,programs,left,owner,private),historical(lib,programs,right,owner,private),
        g::owner(left.landed.receipt)!=owner || g::owner(right.landed.receipt)!=owner,
    ensures fu::compatible(p::context_eq(eq),fu::entry_pair(lib,programs,left,owner),fu::entry_pair(lib,programs,right,owner)),
{
    let a=g::owner(left.landed.receipt);let b=g::owner(right.landed.receipt);let first=replay::dependent(programs(a)(left.iterator));let second=replay::dependent(programs(b)(right.iterator));
    replay::actual_receipt_projects(lib,first,left.input,a);replay::actual_receipt_projects(lib,second,right.input,b);
    if a==owner {assert(left.input.control.fibers[a].provisions.disjoint(dep::declarations(right.input,b)));}
    if b==owner {assert(right.input.control.fibers[b].provisions.disjoint(dep::declarations(left.input,a)));}
    stages_cross(eq,lib,first,second,dep::declarations(left.input,a),left.input.control.fibers[a].provisions,
        dep::declarations(right.input,b),right.input.control.fibers[b].provisions,a==owner,b==owner);
    assert(p::generators(dep::stage(lib,first)).contains(p::forward(dep::stage(lib,first))));
    assert(p::generators(dep::stage(lib,second)).contains(p::forward(dep::stage(lib,second))));
}

pub proof fn fresh_historical<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),separated(source.first().state,owner),
        fragment(programs,source,labels,source.first().history.len(),owner),
    ensures g::well_formed(lib,programs,source.last()),separated(source.last().state,owner),
        source.first().state.control.fibers.dom()==source.last().state.control.fibers.dom(),
        forall|n:usize| full::registered(source.first().state,n) ==> r::interface_same(source.first().state.control.fibers[n],source.last().state.control.fibers[n]),
        source.first().history.len()<=source.last().history.len(),
        forall|i:int| 0<=i<source.first().history.len() ==> source.last().history[i]==source.first().history[i],
        forall|i:int| source.first().history.len()<=i<source.last().history.len() ==> historical(lib,programs,#[trigger] source.last().history[i],owner,source.first().state.control.fibers[owner].provisions),
    decreases labels.len(),
{
    if labels.len()==0 {assert(source.first()==source.last());}
    else {
        let prefix=source.drop_last();let previous=labels.drop_last();let label=labels.last();
        assert(g::execution(lib,programs,prefix,previous));assert(fragment(programs,prefix,previous,source.first().history.len(),owner));
        fresh_historical(eq,lib,programs,prefix,previous,owner);
        let a=prefix.last();let z=source.last();ol::frame(eq,lib,programs,a,z,label.0,label.1);
        ol::configuration_preservation(eq,lib,programs,a,z,label.0,label.1);interface_frame(eq,lib,programs,a,z,label.0,label.1,owner);
        if g::landing(a,z,label.1) {landing_historical(eq,lib,programs,a,z,label.0,label.1,owner);}
        assert forall|i:int| source.first().history.len()<=i<z.history.len() implies historical(lib,programs,#[trigger] z.history[i],owner,source.first().state.control.fibers[owner].provisions) by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());}
        }
        assert forall|n:usize| full::registered(source.first().state,n) implies r::interface_same(source.first().state.control.fibers[n],z.state.control.fibers[n]) by {assert(full::registered(a.state,n));}
    }
}
/// Appending an authentic foreign inverse only needs its existing catalogue
/// position. Keep the recursive forward compatibility theory out of restoration.
#[verifier::spinoff_prover]
proof fn inverse_source_extension<S>(eq:spec_fn(S,S)->bool,prefix:Seq<Action<S>>,initial:S,token:nat)
    requires local_source(eq,prefix,initial),token<catalog(prefix).len(),!catalog(prefix)[token as int].own,
    ensures local_source(eq,prefix.push(Action::Inverse {token}),initial),
        catalog(prefix.push(Action::Inverse {token}))==catalog(prefix),
        events(prefix.push(Action::Inverse {token}))==events(prefix).push(event(catalog(prefix),Action::Inverse {token})),
{
    assert(prefix.push(Action::Inverse {token}).drop_last() =~= prefix);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn actual_restore_actions<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,actor:usize,owner:usize,input:full::State<U>,prefix:Seq<Action<IMap<Port,U>>>,initial:IMap<Port,U>,private:ISet<Port>)
    requires og::primitive_theory(eq,lib),inv::well_formed(input),actor!=owner,offset<=history.len(),tracked_tokens(history,tokens,offset,actor),
        forall|i:int| offset<=i<history.len() ==> historical(lib,programs,#[trigger] history[i],owner,private),
        local_source(p::context_eq(eq),prefix,initial),catalog(prefix)==fresh_records(lib,programs,history,offset,owner),
        sj::trace(events(prefix),initial)==Some(project::project(input,ISet::full())),g::restore(history,tokens,input,actor).is_some(),
    ensures {
        let extended=prefix+inverse_actions(tokens,offset);
        &&& local_source(p::context_eq(eq),extended,initial) && catalog(extended)==catalog(prefix)
        &&& sj::trace(events(extended),initial)==Some(project::project(g::restore(history,tokens,input,actor).unwrap(),ISet::full()))
    },
    decreases tokens.len(),
{
    hide(local_source);
    hide(g::undo);
    replay::context_equivalence(eq,lib);
    if tokens.len()==0 {assert(prefix+inverse_actions::<IMap<Port,U>>(tokens,offset) =~= prefix);}
    else {
        let token=tokens.last();let at=(token-offset) as nat;let entry=history[token as int];let action=Action::Inverse {token:at};let next_prefix=prefix.push(action);
        assert(offset<=token<history.len());assert(g::owner(entry.landed.receipt)==actor);assert(historical(lib,programs,entry,owner,private));
        assert(0<=at<catalog(prefix).len());assert(catalog(prefix)[at as int]==entry_pair(lib,programs,entry,owner));
        inverse_source_extension(p::context_eq(eq),prefix,initial,at);
        assert(next_prefix.drop_last() =~= prefix);
        assert(catalog(next_prefix)==catalog(prefix));
        assert(events(next_prefix) =~= events(prefix).push(event(catalog(prefix),action)));
        assert(events(next_prefix).drop_last() =~= events(prefix));
        let after=g::undo(entry.landed.receipt,input).unwrap();
        table_inverse_projects(entry.landed.receipt,input);
        assert(sj::trace(events(next_prefix),initial)==Some(project::project(after,ISet::full())));
        actual_restore_actions(eq,lib,programs,history,tokens.drop_last(),offset,actor,owner,after,next_prefix,initial,private);
        assert(next_prefix+inverse_actions::<IMap<Port,U>>(tokens.drop_last(),offset) =~= prefix+inverse_actions::<IMap<Port,U>>(tokens,offset));
    }
}

pub proof fn forward_extension<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,offset:nat,owner:usize,prefix:Seq<Action<IMap<Port,U>>>,initial:IMap<Port,U>,private:ISet<Port>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),
        separated(a.state,owner),a.state.control.fibers[owner].provisions==private,
        table_node(programs(actor)(a.current[actor].unwrap())),actor!=owner ==> replay::operational_mixed(programs(actor)(a.current[actor].unwrap())),offset<=a.history.len(),
        forall|i:int| offset<=i<a.history.len() ==> historical(lib,programs,#[trigger] a.history[i],owner,private),
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
    landing_historical(eq,lib,programs,a,z,actor,rule,owner);historical_contract(eq,lib,programs,entry,owner,private);
    if actor!=owner {historical_independence(eq,lib,programs,entry,entry,owner,private);}
    assert(actions.drop_last() =~= prefix);assert(events(actions).drop_last() =~= events(prefix));
    assert forall|i:int| 0<=i<records.len() && (!records[i].own || !call.own) implies fu::compatible(p::context_eq(eq),#[trigger] records[i],call) && fu::compatible(p::context_eq(eq),call,#[trigger] records[i]) by {
        let old=a.history[offset as int+i];assert(historical(lib,programs,old,owner,private));assert(records[i]==entry_pair(lib,programs,old,owner));
        historical_independence(eq,lib,programs,old,entry,owner,private);historical_independence(eq,lib,programs,entry,old,owner,private);
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
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),separated(source.first().state,owner),
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
    replay::context_equivalence(eq,lib);fresh_historical(eq,lib,programs,source,labels,owner);
    let offset=source.first().history.len();let actions=trace_actions(lib,programs,source,labels,offset,owner);let initial=project::project(source.first().state,ISet::full());
    if labels.len()==0 {
        assert(source.first()==source.last());assert(fresh_records(lib,programs,source.last().history,offset,owner) =~= Seq::empty());
    } else {
        let states=source.drop_last();let previous=labels.drop_last();let label=labels.last();let a=states.last();let z=source.last();let actor=label.0;let rule=label.1;
        assert(g::execution(lib,programs,states,previous));assert(fragment(programs,states,previous,offset,owner));
        actual_source(eq,lib,programs,states,previous,owner);fresh_historical(eq,lib,programs,states,previous,owner);
        let prefix=trace_actions(lib,programs,states,previous,offset,owner);let records=catalog(prefix);
        ol::frame(eq,lib,programs,a,z,actor,rule);
        if g::landing(a,z,rule) {
            assert(actions =~= prefix.push(Action::Forward {call:entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)}));
            forward_extension(eq,lib,programs,a,z,actor,rule,offset,owner,prefix,initial,source.first().state.control.fibers[owner].provisions);
        } else if rule==r::Rule::Unload {
            actual_restore_actions(eq,lib,programs,a.history,a.state.accumulators[actor],offset,actor,owner,a.state,prefix,initial,source.first().state.control.fibers[owner].provisions);
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
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),separated(source.first().state,owner),
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



pub open spec fn pinned<U>(receipt:g::Receipt<U>,a:full::State<U>,actor:usize)->bool {
    match receipt {g::Receipt::Table {receipt}=>receipt.actor==actor && match receipt.inverse {
        lift::Inverse::Unit=>true,
        lift::Inverse::Operation {provider,key,..}=>lift::resolve(a,actor,key)==Some(provider),
        lift::Inverse::Provision {key}=>a.control.fibers[actor].provisions.contains(key),
    },_=>false}
}
pub open spec fn pinned_tokens<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,a:full::State<U>,actor:usize)->bool {
    forall|i:int| 0<=i<tokens.len() ==> tokens[i]<history.len() && pinned(#[trigger] history[tokens[i] as int].landed.receipt,a,actor)
}
pub proof fn inverse_definedness<U>(receipt:g::Receipt<U>,a:full::State<U>,actor:usize)
    requires inv::well_formed(a),full::registered(a,actor),pinned(receipt,a,actor),shared::flat(receipt)(project::project(a,ISet::full())).is_some(),
    ensures g::undo(receipt,a).is_some(),inv::well_formed(g::undo(receipt,a).unwrap()),g::undo(receipt,a).unwrap().control==a.control,
        forall|n:usize| full::registered(a,n) && n!=actor ==> g::undo(receipt,a).unwrap().tables[n].dom()==a.tables[n].dom(),
        project::project(g::undo(receipt,a).unwrap(),ISet::full())==shared::flat(receipt)(project::project(a,ISet::full())).unwrap(),
{
    match receipt {
        g::Receipt::Table {receipt}=>{
            match receipt.inverse {
                lift::Inverse::Operation {provider,key,undo}=>{
                    lift::resolution_sound(a,actor,key);project::unique_owner(a);
                    assert(project::project(a,ISet::full()).dom().contains(key));
                    let actual=choose|n:usize|project::owns(a,key,n);
                    assert(a.control.fibers[actual].provisions.contains(key));assert(actual==provider);
                    project::lookup(a,ISet::full(),key,provider);
                    assert(a.tables[provider].insert(key,undo(a.tables[provider][key]).unwrap()).dom() =~= a.tables[provider].dom());
                },
                lift::Inverse::Provision {key}=>{
                    project::unique_owner(a);assert(project::project(a,ISet::full()).dom().contains(key));
                    let actual=choose|n:usize|project::owns(a,key,n);assert(a.control.fibers[actual].provisions.contains(key));assert(actual==actor);
                    project::lookup(a,ISet::full(),key,actor);
                },_=>{},
            }
            assert(lift::undo(receipt,a).is_some());lift::undo_preservation(receipt,a);lift::inverse_projects(receipt,a);
        },_=>{},
    }
}

/// A strict projected word's derived domain suffices for the actual full-state
/// LIFO interpreter once actual receipts retain their committed providers.
pub proof fn restore_definedness<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,a:full::State<U>,actor:usize)
    requires inv::well_formed(a),full::registered(a,actor),pinned_tokens(history,tokens,a,actor),
        p::run(shared::receipt_word(history,tokens),project::project(a,ISet::full())).is_some(),
    ensures g::restore(history,tokens,a,actor).is_some(),inv::well_formed(g::restore(history,tokens,a,actor).unwrap()),
        g::restore(history,tokens,a,actor).unwrap().control==a.control,
        forall|n:usize| full::registered(a,n) && n!=actor ==> g::restore(history,tokens,a,actor).unwrap().tables[n].dom()==a.tables[n].dom(),
        project::project(g::restore(history,tokens,a,actor).unwrap(),ISet::full())==p::run(shared::receipt_word(history,tokens),project::project(a,ISet::full())).unwrap(),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;
        assert(pinned(receipt,a,actor));
        sj::run_prepend(shared::flat(receipt),shared::receipt_word(history,tokens.drop_last()),project::project(a,ISet::full()));
        inverse_definedness(receipt,a,actor);let next=g::undo(receipt,a).unwrap();
        assert(pinned_tokens(history,tokens.drop_last(),next,actor));
        restore_definedness(history,tokens.drop_last(),next,actor);
        assert forall|n:usize| full::registered(a,n) && n!=actor implies g::restore(history,tokens,a,actor).unwrap().tables[n].dom()==a.tables[n].dom() by {
            assert(full::registered(next,n));
            assert(g::restore(history,tokens.drop_last(),next,actor).unwrap().tables[n].dom()==next.tables[n].dom());
        }
    }
}

pub proof fn journal_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,es:Seq<sj::Event<IMap<Port,U>>>,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),full::registered(a.state,owner),
        g::step(lib,programs,a,z,actor,rule),separated(a.state,owner),rule!=r::Rule::Insert,rule!=r::Rule::Remove,rule!=r::Rule::Unload,
        g::landing(a,z,rule) ==> table_node(programs(actor)(a.current[actor].unwrap())),
        shared::receipt_word(a.history,a.state.accumulators[owner])==sj::journal(es),pinned_tokens(a.history,a.state.accumulators[owner],a.state,owner),
    ensures full::registered(z.state,owner),pinned_tokens(z.history,z.state.accumulators[owner],z.state,owner),
        shared::receipt_word(z.history,z.state.accumulators[owner])==sj::journal(es.push(replay::event(lib,programs,a,z,actor,rule,owner))),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);interface_frame(eq,lib,programs,a,z,actor,rule,owner);
    let old=a.state.accumulators[owner];let new=z.state.accumulators[owner];let e=replay::event(lib,programs,a,z,actor,rule,owner);
    assert(es.push(e).drop_last() =~= es);
    if actor==owner && rule==r::Rule::Begin {
        assert(old.len()==0);assert(sj::journal(es).len()==0);assert(new.len()==0);
    } else {
        assert(a.state.control.fibers[owner].committed==z.state.control.fibers[owner].committed);
        shared::resolution_frame(a.state,z.state,owner);
        assert forall|i:int| 0<=i<old.len() implies a.history[old[i] as int].landed.receipt==z.history[old[i] as int].landed.receipt by {
            assert(old[i]<a.history.len());
        }
        shared::receipt_word_extensional(a.history,z.history,old);
        assert forall|i:int| 0<=i<old.len() implies old[i]<z.history.len() && pinned(#[trigger] z.history[old[i] as int].landed.receipt,z.state,owner) by {
            assert(pinned(a.history[old[i] as int].landed.receipt,a.state,owner));
            match a.history[old[i] as int].landed.receipt {
                g::Receipt::Table {receipt}=>{match receipt.inverse {lift::Inverse::Operation {key,..}=>{assert(lift::resolve(a.state,owner,key)==lift::resolve(z.state,owner,key));},_=>{}}},_=>{},
            }
        }
        if g::landing(a,z,rule) && actor==owner {
            let node=replay::dependent(programs(actor)(a.current[actor].unwrap()));let call=g::entry(lib,programs,a,actor);
            lift::run_preservation(dep::stage(lib,node),a.state,actor);
            assert(new==old.push(a.history.len()));assert(new.drop_last() =~= old);
            assert(z.history[new.last() as int]==call);
            assert(pinned(call.landed.receipt,z.state,owner)) by {
                match node {crate::dependent_grammar::Node::Operation {operation,..}=>{
                    let key=(lib.key)(operation);assert(lift::resolve(a.state,owner,key)==lift::resolve(z.state,owner,key));
                },_=>{},}
            }
            assert(shared::flat(call.landed.receipt)==e.inverse);
            assert forall|i:int| 0<=i<new.len() implies new[i]<z.history.len() && pinned(#[trigger] z.history[new[i] as int].landed.receipt,z.state,owner) by {
                if i<old.len() {assert(new[i]==old[i]);} else {assert(i==old.len());}
            }
        } else {assert(new==old);assert(!e.own);}
    }
}

pub proof fn restore_control<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,input:full::State<U>,actor:usize)
    requires inv::well_formed(input),g::restore(history,tokens,input,actor).is_some(),
        forall|i:int| 0<=i<tokens.len() ==> match #[trigger] history[tokens[i] as int].landed.receipt {g::Receipt::Table {..}=>true,_=>false},
    ensures g::restore(history,tokens,input,actor).unwrap().control==input.control,
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;fu::table_inverse_projects(receipt,input);
        if let g::Receipt::Table {receipt}=receipt {lift::undo_preservation(receipt,input);}
        restore_control(history,tokens.drop_last(),g::undo(receipt,input).unwrap(),actor);
    }
}
pub proof fn actual_journal<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),separated(source.first().state,owner),
        fragment(programs,source,labels,source.first().history.len(),owner),full::registered(source.first().state,owner),source.first().state.control.fibers[owner].phase==Phase::Inactive,
    ensures {
        let last=source.last();let actions=trace_actions(lib,programs,source,labels,source.first().history.len(),owner);
        &&& g::well_formed(lib,programs,last) && full::registered(last.state,owner)
        &&& r::interface_same(source.first().state.control.fibers[owner],last.state.control.fibers[owner])
        &&& pinned_tokens(last.history,last.state.accumulators[owner],last.state,owner)
        &&& shared::receipt_word(last.history,last.state.accumulators[owner])==sj::journal(events(actions))
    },
    decreases labels.len(),
{
    fresh_historical(eq,lib,programs,source,labels,owner);
    if labels.len()==0 {assert(source.first()==source.last());assert(source.first().state.accumulators[owner].len()==0);}
    else {
        let states=source.drop_last();let previous=labels.drop_last();let label=labels.last();let a=states.last();let z=source.last();let actor=label.0;let rule=label.1;
        let offset=source.first().history.len();let prefix=trace_actions(lib,programs,states,previous,offset,owner);let actions=trace_actions(lib,programs,source,labels,offset,owner);
        assert(g::execution(lib,programs,states,previous));assert(fragment(programs,states,previous,offset,owner));
        actual_journal(eq,lib,programs,states,previous,owner);fresh_historical(eq,lib,programs,states,previous,owner);
        ol::frame(eq,lib,programs,a,z,actor,rule);
        if rule!=r::Rule::Unload {
            journal_step(eq,lib,programs,a,z,events(prefix),owner,actor,rule);
            if g::landing(a,z,rule) {
                assert(actions =~= prefix.push(Action::Forward {call:entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)}));
                assert(event(catalog(prefix),actions.last())==replay::event(lib,programs,a,z,actor,rule,owner));
            } else {
                assert(actions =~= prefix.push(Action::Identity));
                assert(fu::identity::<IMap<Port,U>>() =~= replay::identity::<U>());
                assert(event(catalog(prefix),actions.last())==replay::event(lib,programs,a,z,actor,rule,owner));
            }
            assert(actions.drop_last() =~= prefix);
            assert(events(actions) =~= events(prefix).push(replay::event(lib,programs,a,z,actor,rule,owner)));
        } else {
            assert forall|i:int| 0<=i<a.state.accumulators[actor].len() implies match #[trigger] a.history[a.state.accumulators[actor][i] as int].landed.receipt {g::Receipt::Table {..}=>true,_=>false} by {
                let token=a.state.accumulators[actor][i];assert(offset<=token<a.history.len());assert(historical(lib,programs,a.history[token as int],owner,source.first().state.control.fibers[owner].provisions));
            }
            restore_control(a.history,a.state.accumulators[actor],a.state,actor);
            fu::inverse_actions_journal(prefix,a.state.accumulators[actor],offset);
            assert(z.history==a.history);assert(z.state.accumulators[owner]==a.state.accumulators[owner]);
            assert(z.state.control.fibers[owner]==a.state.control.fibers[owner]);
            shared::resolution_frame(a.state,z.state,owner);
            assert forall|i:int| 0<=i<z.state.accumulators[owner].len() implies z.state.accumulators[owner][i]<z.history.len()
                && pinned(#[trigger] z.history[z.state.accumulators[owner][i] as int].landed.receipt,z.state,owner) by {
                let token=z.state.accumulators[owner][i];assert(pinned(a.history[token as int].landed.receipt,a.state,owner));
                match a.history[token as int].landed.receipt {
                    g::Receipt::Table {receipt}=>{match receipt.inverse {lift::Inverse::Operation {key,..}=>{assert(lift::resolve(a.state,owner,key)==lift::resolve(z.state,owner,key));},_=>{}}},_=>{},
                }
            }
        }
    }
}

pub proof fn terminal_with_foreign_unloads<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),separated(source.first().state,owner),
        fragment(programs,source,labels,source.first().history.len(),owner),full::registered(source.first().state,owner),source.first().state.control.fibers[owner].phase==Phase::Inactive,
        source.last().state.control.fibers[owner].phase==Phase::Unloading,
    ensures {
        let last=source.last();let terminal=g::unload(last,owner);let actions=trace_actions(lib,programs,source,labels,source.first().history.len(),owner);let initial=project::project(source.first().state,ISet::full());
        &&& g::restore(last.history,last.state.accumulators[owner],last.state,owner).is_some()
        &&& g::step(lib,programs,last,terminal,owner,r::Rule::Unload) && g::well_formed(lib,programs,terminal)
        &&& sj::foreign(events(actions),initial).is_some()
        &&& p::context_eq(eq)(project::project(terminal.state,ISet::full()),sj::foreign(events(actions),initial).unwrap())
    },
{
    actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);actual_journal(eq,lib,programs,source,labels,owner);
    let last=source.last();restore_definedness(last.history,last.state.accumulators[owner],last.state,owner);
    fresh_historical(eq,lib,programs,source,labels,owner);
    assert(!r::relied(last.state.control,owner)) by {
        if r::relied(last.state.control,owner) {
            let (n,b)=choose|n:usize,b:Binding| full::registered(last.state,n) && n!=owner && last.state.control.fibers[n].phase!=Phase::Inactive
                && last.state.control.fibers[n].committed.contains(b) && b.provider==owner;
            let key=Port {key:b.key,realm:b.realm};assert(last.state.control.fibers[owner].provisions.contains(key));assert(dep::declarations(last.state,n).contains(key));assert(dep::declarations(last.state,n).disjoint(last.state.control.fibers[owner].provisions));
        }
    }
    let terminal=g::unload(last,owner);assert(g::step(lib,programs,last,terminal,owner,r::Rule::Unload));
    ol::configuration_preservation(eq,lib,programs,last,terminal,owner,r::Rule::Unload);
    let restored=g::restore(last.history,last.state.accumulators[owner],last.state,owner).unwrap();project::unique_owner(restored);
    project::lifecycle_edit(restored,owner,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
}


pub proof fn stable_pending<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,
    node:dep::Node<A,X,U,B,J>,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),separated(source.first().state,owner),actor!=owner,
        fragment(programs,source,labels,source.first().history.len(),owner),replay::operational(node),dep::run(lib,node,source.last().state,actor).is_some(),
        d::permitted(lib,dep::declarations(source.last().state,actor),source.last().state.control.fibers[actor].provisions,node),
    ensures forall|i:int| 0<=i<sj::journal(fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner))).len()
        ==> p::stable(eq,dep::stage(lib,node),#[trigger] sj::journal(fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner)))[i]),
{
    actual_source(eq,lib,programs,source,labels,owner);fresh_historical(eq,lib,programs,source,labels,owner);
    let offset=source.first().history.len();let actions=fu::trace_actions(lib,programs,source,labels,offset,owner);let records=fu::catalog(actions);let word=sj::journal(fu::events(actions));
    fu::journal_origins(actions);
    assert forall|i:int| 0<=i<word.len() implies p::stable(eq,dep::stage(lib,node),#[trigger] word[i]) by {
        let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].inverse==word[i];
        let entry=source.last().history[offset as int+j];let old_actor=g::owner(entry.landed.receipt);let old_node=replay::dependent(programs(old_actor)(entry.iterator));
        assert(historical(lib,programs,entry,owner,source.first().state.control.fibers[owner].provisions));assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        assert(old_actor==owner);let current=source.last().state;
        assert(entry.input.control.fibers[owner].provisions==current.control.fibers[owner].provisions);
        assert(entry.input.control.fibers[owner].provisions.disjoint(dep::declarations(current,actor)));
        stages_cross(eq,lib,old_node,node,dep::declarations(entry.input,old_actor),entry.input.control.fibers[old_actor].provisions,
            dep::declarations(current,actor),current.control.fibers[actor].provisions,true,false);
        replay::actual_receipt_projects(lib,old_node,entry.input,old_actor);
    }
}

#[verifier::spinoff_prover]
pub proof fn next_call<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,
    node:dep::Node<A,X,U,B,J>,target:full::State<U>,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),separated(source.first().state,owner),
        fragment(programs,source,labels,source.first().history.len(),owner),actor!=owner,inv::well_formed(target),full::registered(target,actor),target.control.fibers[actor].phase!=Phase::Inactive,
        source.last().state.control.fibers[actor]==target.control.fibers[actor],replay::operational(node),dep::run(lib,node,source.last().state,actor).is_some(),
        d::permitted(lib,dep::declarations(source.last().state,actor),source.last().state.control.fibers[actor].provisions,node),
        p::context_eq(eq)(sj::foreign(fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner)),project::project(source.first().state,ISet::full())).unwrap(),project::project(target,ISet::full())),
    ensures {
        let old=dep::run(lib,node,source.last().state,actor).unwrap();let new=dep::run(lib,node,target,actor).unwrap();
        let es=fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner));let initial=project::project(source.first().state,ISet::full());let e=replay::call_event(lib,node,source.last().state,actor,false);
        &&& dep::run(lib,node,target,actor).is_some() && new.next==old.next
        &&& obs::receipt_related(eq,g::Receipt::Table {receipt:old.receipt},g::Receipt::Table {receipt:new.receipt})
        &&& (e.forward)(sj::foreign(es,initial).unwrap()).is_some()
        &&& p::context_eq(eq)((e.forward)(sj::foreign(es,initial).unwrap()).unwrap(),project::project(new.state,ISet::full()))
    },
{
    actual_foreign_unload_recovery(eq,lib,programs,source,labels,owner);replay::context_equivalence(eq,lib);fresh_historical(eq,lib,programs,source,labels,owner);
    let es=fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner));let initial=project::project(source.first().state,ISet::full());let word=sj::journal(es);let a=source.last().state;
    stable_pending(eq,lib,programs,source,labels,owner,node,actor);
    assert(p::context_eq(eq)(p::run(word,project::project(a,ISet::full())).unwrap(),project::project(target,ISet::full())));
    replay::run_after_word(eq,lib,node,a,target,actor,word);sue::actual_names(lib,node,a,target,actor);
    let left=g::Receipt::Table {receipt:dep::run(lib,node,a,actor).unwrap().receipt};let right=g::Receipt::Table {receipt:dep::run(lib,node,target,actor).unwrap().receipt};
    obs::projected_receipts(eq,left,right);
    replay::call_contract(eq,lib,node,a,actor,false);lift::run_projects(dep::stage(lib,node),target,actor);
    let e=replay::call_event(lib,node,a,actor,false);assert((e.forward)(project::project(target,ISet::full())).is_some());
    assert((e.forward)(sj::foreign(es,initial).unwrap()).is_some());
}


} // verus!
