//! A new foreign Provision survives deletion of the owner's pending episode.
//!
//! Current table domains derive the real target call. A defined strict own
//! journal on an absent key excludes every historical own call at that key:
//! table inverses never add bindings. This derives the crossing laws without
//! assuming Provision self-independence or declaration-level key separation.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_lift as dep, foreign_unload as fu, grammar_lift as lift,
    mediated as m, mixed_grammar as g, mixed_observational_runs as obs,
    observational_grammar as og, observational_lift as ol, old_journal_unload as old,
    partial_independence as pi, preservation as inv, projection as p,
    providing_owner_deletion as own, providing_owner_execution as deletion,
    providing_owner_transport as transport, refinement as r, semantics as s,
    shared_execution as sh, shared_replay as replay, shared_unload_execution as history,
    strict_batch_recovery as batch, strict_journal as sj, Port,
};
use vstd::prelude::*;

verus! {

/// The minimal metadata extension admits all actual table landings. It does
/// not assert a universal independence relation between foreign provisions.
pub open spec fn historical<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>,owner:usize,private:ISet<Port>)->bool {
    let actor=g::owner(entry.landed.receipt);let node=programs(actor)(entry.iterator);
    &&& inv::well_formed(entry.input) && dep::typed(lib,entry.input) && dep::finite_context(entry.input)
    &&& own::table_node(node) && (actor!=owner ==> dep::declarations(entry.input,actor).disjoint(private))
    &&& (actor==owner ==> entry.input.control.fibers[actor].provisions==private)
    &&& d::permitted(lib,dep::declarations(entry.input,actor),entry.input.control.fibers[actor].provisions,replay::dependent(node))
    &&& g::run(lib,node,entry.input,actor)==Some(entry.landed)
}
pub proof fn old_metadata_implies<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>,owner:usize,private:ISet<Port>)
    requires own::historical(lib,programs,entry,owner,private),
    ensures historical(lib,programs,entry,owner,private),
{ }
/// Existing owner and operational-foreign lemmas remain reusable without
/// strengthening the metadata of unrelated new foreign Provision entries.
pub proof fn restricted_metadata<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>,owner:usize,private:ISet<Port>)
    requires historical(lib,programs,entry,owner,private),
        g::owner(entry.landed.receipt)==owner || replay::operational_mixed(programs(g::owner(entry.landed.receipt))(entry.iterator)),
    ensures own::historical(lib,programs,entry,owner,private),
{ }
pub proof fn landing_historical<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),own::separated(a.state,owner),
        own::table_node(programs(actor)(a.current[actor].unwrap())),
    ensures historical(lib,programs,g::entry(lib,programs,a,actor),owner,a.state.control.fibers[owner].provisions),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());
}
pub proof fn historical_contract<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>,owner:usize,private:ISet<Port>)
    requires og::primitive_theory(eq,lib),historical(lib,programs,entry,owner,private),
    ensures {
        let call=fu::entry_pair(lib,programs,entry,owner);let input=p::project(entry.input,ISet::full());let output=p::project(entry.landed.state,ISet::full());
        &&& fu::respectful(pi::context_eq(eq),call)
        &&& (call.forward)(input)==Some(output) && (call.inverse)(output).is_some() && pi::context_eq(eq)((call.inverse)(output).unwrap(),input)
    },
{
    let actor=g::owner(entry.landed.receipt);let node=replay::dependent(programs(actor)(entry.iterator));let stage=dep::stage(lib,node);let call=fu::entry_pair(lib,programs,entry,owner);
    replay::context_equivalence(eq,lib);replay::actual_receipt_projects(lib,node,entry.input,actor);
    own::stage_respects(eq,lib,node,dep::declarations(entry.input,actor),entry.input.control.fibers[actor].provisions);
    assert(pi::generators(stage).contains(pi::forward(stage)));pi::generator_respects(eq,stage,call.forward);pi::generator_respects(eq,stage,call.inverse);
    ol::dependent_run_admissible(eq,lib,node,entry.input,actor);fu::table_inverse_projects(entry.landed.receipt,entry.landed.state);
    lift::run_projects(stage,entry.input,actor);
}

pub open spec fn shrinks<U>(f:m::PartialMap<IMap<Port,U>>)->bool {
    forall|input:IMap<Port,U>| #[trigger] f(input).is_some() ==> f(input).unwrap().dom().subset_of(input.dom())
}
pub open spec fn needs<U>(f:m::PartialMap<IMap<Port,U>>,key:Port)->bool {
    forall|input:IMap<Port,U>| #[trigger] f(input).is_some() ==> input.dom().contains(key)
}
pub proof fn inverse_shape<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entry:g::Entry<U,I>,owner:usize,private:ISet<Port>)
    requires historical(lib,programs,entry,owner,private),
    ensures shrinks(sh::flat(entry.landed.receipt)),
        pi::key(dep::stage(lib,replay::dependent(programs(g::owner(entry.landed.receipt))(entry.iterator)))).is_some() ==>
            needs(sh::flat(entry.landed.receipt),pi::key(dep::stage(lib,replay::dependent(programs(g::owner(entry.landed.receipt))(entry.iterator)))).unwrap()),
{
    let actor=g::owner(entry.landed.receipt);let node=replay::dependent(programs(actor)(entry.iterator));let f=sh::flat(entry.landed.receipt);
    assert forall|input:IMap<Port,U>| #[trigger] f(input).is_some() implies f(input).unwrap().dom().subset_of(input.dom()) by {
        match node {d::Node::Operation {operation,..}=>{let key=(lib.key)(operation);assert(input.dom().contains(key));},_=>{}}
    }
}

/// This is partial-map reasoning only, not a synthetic lifecycle execution.
pub proof fn absent_word<U>(word:Seq<m::PartialMap<IMap<Port,U>>>,input:IMap<Port,U>,key:Port)
    requires pi::run(word,input).is_some(),!input.dom().contains(key),
        forall|i:int|0<=i<word.len() ==> shrinks(#[trigger] word[i]),
    ensures !pi::run(word,input).unwrap().dom().contains(key),
        forall|i:int|0<=i<word.len() ==> !needs(#[trigger] word[i],key),
    decreases word.len(),
{
    if word.len()>0 {
        absent_word(word.drop_last(),input,key);let middle=pi::run(word.drop_last(),input).unwrap();let f=word.last();
        assert(shrinks(f));assert(f(middle).is_some());assert(!needs(f,key));
        assert forall|i:int|0<=i<word.len() implies !needs(#[trigger] word[i],key) by {
            if i<word.len()-1 {assert(word[i]==word.drop_last()[i]);}else{assert(word[i]==f);}
        }
    }
}

/// Every own record really occurs in the pending inverse word. This converse
/// to journal_origins uses catalogue structure, not a recovery assertion.
pub proof fn inverse_member<S>(actions:Seq<fu::Action<S>>,j:int)
    requires 0<=j<fu::catalog(actions).len(),fu::catalog(actions)[j].own,
    ensures exists|i:int|0<=i<sj::journal(fu::events(actions)).len() && #[trigger] sj::journal(fu::events(actions))[i]==fu::catalog(actions)[j].inverse,
    decreases actions.len(),
{
    let prefix=actions.drop_last();let before=fu::catalog(prefix);let es=fu::events(actions);let old_es=fu::events(prefix);
    assert(actions.len()>0);assert(es.drop_last() =~= old_es);
    if j<before.len() {
        assert(before[j]==fu::catalog(actions)[j]);inverse_member(prefix,j);
        let i=choose|i:int|0<=i<sj::journal(old_es).len() && #[trigger] sj::journal(old_es)[i]==before[j].inverse;
        if es.last().own {assert(sj::journal(es)[i+1]==sj::journal(old_es)[i]);}else{assert(sj::journal(es)[i]==sj::journal(old_es)[i]);}
    } else {assert(j==before.len());assert(es.last().own);assert(sj::journal(es)[0]==fu::catalog(actions)[j].inverse);}
}

pub proof fn pending_avoids<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,private:ISet<Port>,input:IMap<Port,U>,key:Port)
    requires offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int|offset<=i<entries.len() ==> historical(lib,programs,#[trigger] entries[i],owner,private),
        pi::run(sj::journal(fu::events(actions)),input).is_some(),!input.dom().contains(key),
    ensures forall|j:int|0<=j<fu::catalog(actions).len() && fu::catalog(actions)[j].own ==>
        pi::key(dep::stage(lib,replay::dependent(programs(owner)(#[trigger] entries[offset as int+j].iterator))))!=Some(key),
{
    let records=fu::catalog(actions);let word=sj::journal(fu::events(actions));fu::journal_origins(actions);
    assert forall|i:int|0<=i<word.len() implies shrinks(#[trigger] word[i]) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].inverse==word[i];let entry=entries[offset as int+j];
        assert(records[j]==fu::entry_pair(lib,programs,entry,owner));inverse_shape(lib,programs,entry,owner,private);
    }
    absent_word(word,input,key);
    assert forall|j:int|0<=j<records.len() && records[j].own implies
        pi::key(dep::stage(lib,replay::dependent(programs(owner)(#[trigger] entries[offset as int+j].iterator))))!=Some(key) by {
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        inverse_shape(lib,programs,entry,owner,private);inverse_member(actions,j);
        let i=choose|i:int|0<=i<word.len() && #[trigger] word[i]==records[j].inverse;assert(!needs(word[i],key));
    }
}

/// The strict inverse word is already defined at the actual source state by
/// the prefix induction. Fresh-key absence then derives all required crossing.
pub proof fn provision_crosses<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,private:ISet<Port>,input:IMap<Port,U>,key:Port,value:U,next:Option<J>)
    requires og::primitive_theory(eq,lib),(lib.values)(key,value),offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int|offset<=i<entries.len() ==> historical(lib,programs,#[trigger] entries[i],owner,private),
        pi::run(sj::journal(fu::events(actions)),input).is_some(),!input.dom().contains(key),
    ensures {
        let node=dep::stage(lib,d::Node::Provision {key,value,next});let f=pi::forward(node);let es=fu::events(actions);
        &&& pi::respects(pi::context_eq(eq),f)
        &&& pi::commutes(pi::context_eq(eq),f,batch::redo(es)) && pi::commutes(pi::context_eq(eq),f,batch::undo(es))
    },
{
    replay::context_equivalence(eq,lib);pending_avoids(lib,programs,entries,actions,offset,owner,private,input,key);
    let new=d::Node::Provision {key,value,next};let stage=dep::stage(lib,new);let forward=pi::forward(stage);let records=fu::catalog(actions);let es=fu::events(actions);
    own::stage_respects(eq,lib,new,ISet::full(),ISet::full());assert(pi::generators(stage).contains(forward));pi::generator_respects(eq,stage,forward);
    assert forall|j:int|0<=j<records.len() && records[j].own implies pi::commutes(pi::context_eq(eq),records[j].forward,forward)
        && pi::commutes(pi::context_eq(eq),records[j].inverse,forward) && fu::respectful(pi::context_eq(eq),#[trigger] records[j]) by {
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        let node=replay::dependent(programs(owner)(entry.iterator));let own_stage=dep::stage(lib,node);
        historical_contract(eq,lib,programs,entry,owner,private);replay::actual_receipt_projects(lib,node,entry.input,owner);
        own::stage_respects(eq,lib,node,dep::declarations(entry.input,owner),entry.input.control.fibers[owner].provisions);
        if let d::Node::Unit=node {pi::unit_independence::<Port,U,B,B>(eq,stage);}else{pi::distinct_nodes(eq,own_stage,stage);}
        assert(pi::generators(own_stage).contains(records[j].forward));assert(pi::generators(own_stage).contains(records[j].inverse));
    }
    old::forward_origins(actions);fu::journal_origins(actions);
    assert forall|i:int|0<=i<batch::forwards(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] batch::forwards(es)[i]) && pi::commutes(pi::context_eq(eq),batch::forwards(es)[i],forward) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].forward==batch::forwards(es)[i];
    }
    assert forall|i:int|0<=i<sj::journal(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] sj::journal(es)[i]) && pi::commutes(pi::context_eq(eq),sj::journal(es)[i],forward) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];
    }
    sj::word_commutes(pi::context_eq(eq),batch::forwards(es),forward);sj::word_commutes(pi::context_eq(eq),sj::journal(es),forward);
}

/// Same foreign table domain and current permissions suffice for its new
/// Provision. No successful target run or erased-word domain is an input.
pub proof fn run_transport<A,X,U,B,I>(lib:g::Library<A,X,U,B>,source:s::State<U>,target:s::State<U>,actor:usize,key:Port,value:U,next:Option<I>)
    requires s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],source.tables[actor].dom()==target.tables[actor].dom(),
        dep::run(lib,d::Node::Provision {key,value,next},source,actor).is_some(),
    ensures {
        let a=dep::run(lib,d::Node::Provision {key,value,next},source,actor).unwrap();let b=dep::run(lib,d::Node::Provision {key,value,next},target,actor);
        &&& b.is_some() && a.next==b.unwrap().next && a.receipt==b.unwrap().receipt
        &&& b.unwrap().state.tables[actor]==target.tables[actor].insert(key,value)
    },
{ }

/// One complete lifecycle landing with actual history append and token map.
#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn landing_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize,rule:r::Rule,key:Port,value:U,next:Option<I>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),actor!=owner,
        own::separated(a.state,owner),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),
        programs(actor)(a.current[actor].unwrap())==(g::Node::Dependent {node:d::Node::Provision {key,value,next}}),
    ensures {
        let out=transport::advance(lib,programs,a,z,target,actor,rule,owner);
        &&& g::step(lib,programs,target,out,actor,rule) && g::well_formed(lib,programs,out) && transport::related(eq,z,out,offset,owner)
        &&& g::entry(lib,programs,a,actor).landed.receipt==g::entry(lib,programs,target,actor).landed.receipt
        &&& g::entry(lib,programs,a,actor).landed.next==g::entry(lib,programs,target,actor).landed.next
        &&& p::project(out.state,ISet::full())==p::project(g::entry(lib,programs,target,actor).landed.state,ISet::full())
    },
{
    ol::frame(eq,lib,programs,a,z,actor,rule);run_transport(lib,a.state,target.state,actor,key,value,next);
    transport::publication(a,target,owner,actor,a.state.control.fibers[actor].committed);
    let out=transport::advance(lib,programs,a,z,target,actor,rule,owner);assert(g::step(lib,programs,target,out,actor,rule));
    ol::configuration_preservation(eq,lib,programs,target,out,actor,rule);ol::frame(eq,lib,programs,target,out,actor,rule);
    let left=g::entry(lib,programs,a,actor);let right=g::entry(lib,programs,target,actor);
    assert(obs::receipt_related(eq,left.landed.receipt,right.landed.receipt));history::histories_push(eq,a.history,target.history,left,right,offset,owner);
    assert forall|n:usize|s::registered(z.state,n) && n!=owner implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n]
    } by {
        if n==actor {assert(a.state.tables[n].insert(key,value).dom() =~= target.state.tables[n].insert(key,value).dom());}else{assert(a.current[n]==target.current[n]);}
    }
    assert forall|n:usize|s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
        assert(s::registered(a.state,n));assert forall|i:int|0<=i<a.state.accumulators[n].len() implies a.state.accumulators[n][i]<=a.history.len() by {assert(a.state.accumulators[n][i]<a.history.len());}
        if n==actor {history::rename_laws(a.history,offset,owner,a.state.accumulators[n],a.history.len());history::rename_append(a.history,left,offset,owner,a.state.accumulators[n].push(a.history.len()));}
        else {history::rename_append(a.history,left,offset,owner,a.state.accumulators[n]);}
    }
    let landed=right.landed.state;lift::run_preservation(dep::stage(lib,d::Node::Provision {key,value,next}),target.state,actor);p::unique_owner(landed);
    p::lifecycle_edit(landed,actor,z.state.control.fibers[actor].phase,target.state.control.fibers[actor].committed,
        dep::marker(out.current[actor]),target.state.accumulators[actor].push(target.history.len()),ISet::full());
}

/// Append the genuine foreign call to the provenance catalogue. This only
/// changes the catalogue; it does not replay a cleanup as a forward action.
pub proof fn catalogue_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),own::separated(a.state,owner),
        g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),actor!=owner,
        own::table_node(programs(actor)(a.current[actor].unwrap())),offset<=a.history.len(),
        fu::catalog(actions)==fu::fresh_records(lib,programs,a.history,offset,owner),
        forall|i:int|offset<=i<a.history.len() ==> historical(lib,programs,#[trigger] a.history[i],owner,a.state.control.fibers[owner].provisions),
    ensures {
        let extended=actions.push(fu::Action::Forward {call:fu::entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)});
        &&& batch::redo(fu::events(extended))==batch::redo(fu::events(actions)) && batch::undo(fu::events(extended))==batch::undo(fu::events(actions))
        &&& fu::catalog(extended)==fu::fresh_records(lib,programs,z.history,offset,owner)
        &&& forall|i:int|offset<=i<z.history.len() ==> historical(lib,programs,#[trigger] z.history[i],owner,z.state.control.fibers[owner].provisions)
    },
{
    ol::frame(eq,lib,programs,a,z,actor,rule);own::interface_frame(eq,lib,programs,a,z,actor,rule,owner);
    landing_historical(eq,lib,programs,a,z,actor,rule,owner);
    let left=g::entry(lib,programs,a,actor);let action=fu::Action::Forward {call:fu::entry_pair(lib,programs,left,owner)};
    assert(g::owner(left.landed.receipt)==actor);
    assert(!fu::entry_pair(lib,programs,left,owner).own);
    crate::internal_old_unload::own_words_push(actions,action);
    let extended=actions.push(action);
    assert(extended.drop_last() =~= actions);
    assert(fu::catalog(extended)==fu::catalog(actions).push(fu::entry_pair(lib,programs,left,owner)));
    assert(batch::redo(fu::events(extended))==batch::redo(fu::events(actions)));
    assert(batch::undo(fu::events(extended))==batch::undo(fu::events(actions)));
    assert(fu::fresh_records(lib,programs,z.history,offset,owner) =~= fu::catalog(actions).push(fu::entry_pair(lib,programs,left,owner)));
    assert forall|i:int|offset<=i<z.history.len() implies historical(lib,programs,#[trigger] z.history[i],owner,z.state.control.fibers[owner].provisions) by {
        if i<a.history.len(){assert(z.history[i]==a.history[i]);}else{assert(i==a.history.len());}
    }
}

/// Full one-step value/control transport under the prefix's inductive batch
/// invariant. Both the target landing and the updated batch are conclusions.
#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn synchronized_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,rule:r::Rule,key:Port,value:U,next:Option<I>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),actor!=owner,
        own::separated(a.state,owner),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),
        programs(actor)(a.current[actor].unwrap())==(g::Node::Dependent {node:d::Node::Provision {key,value,next}}),
        fu::catalog(actions)==fu::fresh_records(lib,programs,a.history,offset,owner),
        forall|i:int|offset<=i<a.history.len() ==> historical(lib,programs,#[trigger] a.history[i],owner,a.state.control.fibers[owner].provisions),
        batch::batch(pi::context_eq(eq),batch::redo(fu::events(actions)),batch::undo(fu::events(actions)),p::project(a.state,ISet::full())),
        pi::context_eq(eq)(batch::undo(fu::events(actions))(p::project(a.state,ISet::full())).unwrap(),p::project(target.state,ISet::full())),
    ensures {
        let out=transport::advance(lib,programs,a,z,target,actor,rule,owner);let es=fu::events(actions);
        let extended=actions.push(fu::Action::Forward {call:fu::entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)});
        &&& g::step(lib,programs,target,out,actor,rule) && g::well_formed(lib,programs,out) && transport::related(eq,z,out,offset,owner)
        &&& batch::batch(pi::context_eq(eq),batch::redo(es),batch::undo(es),p::project(z.state,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(es)(p::project(z.state,ISet::full())).unwrap(),p::project(out.state,ISet::full()))
        &&& batch::redo(fu::events(extended))==batch::redo(es) && batch::undo(fu::events(extended))==batch::undo(es)
        &&& fu::catalog(extended)==fu::fresh_records(lib,programs,z.history,offset,owner)
        &&& forall|i:int|offset<=i<z.history.len() ==> historical(lib,programs,#[trigger] z.history[i],owner,z.state.control.fibers[owner].provisions)
    },
{
    landing_transport(eq,lib,programs,a,z,target,offset,owner,actor,rule,key,value,next);ol::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());
    let node=d::Node::Provision {key,value,next};let stage=dep::stage(lib,node);let f=pi::forward(stage);let es=fu::events(actions);let input=p::project(a.state,ISet::full());
    replay::context_equivalence(eq,lib);lift::run_projects(stage,a.state,actor);
    provision_crosses(eq,lib,programs,a.history,actions,offset,owner,a.state.control.fibers[owner].provisions,input,key,value,next);
    batch::foreign_cross(pi::context_eq(eq),batch::redo(es),batch::undo(es),f,input);
    let out=transport::advance(lib,programs,a,z,target,actor,rule,owner);let left=g::entry(lib,programs,a,actor);let right=g::entry(lib,programs,target,actor);
    lift::run_preservation(stage,a.state,actor);p::unique_owner(left.landed.state);
    p::lifecycle_edit(left.landed.state,actor,z.state.control.fibers[actor].phase,a.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
    ol::frame(eq,lib,programs,a,z,actor,rule);assert(f(input)==Some(p::project(z.state,ISet::full())));
    lift::run_projects(stage,target.state,actor);
    let reference=batch::undo(es)(input).unwrap();assert(pi::context_eq(eq)(f(reference).unwrap(),f(p::project(target.state,ISet::full())).unwrap()));
    catalogue_landing(eq,lib,programs,a,z,actions,offset,owner,actor,rule);
}

/// An existing owner-only legal prefix establishes this bridge's inductive
/// premises from actual execution and primitive witnesses. The next foreign
/// Provision is outside the old operational-only fragment.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn prefix_batch<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),own::separated(source.first().state,owner),
        own::fragment(programs,source,labels,source.first().history.len(),owner),old::owner_window(source,labels,owner),
        s::registered(source.first().state,owner),source.first().state.tables[owner].is_empty(),source.first().state.control.fibers[owner].phase==crate::Phase::Inactive,
    ensures {
        let target=deletion::delete(lib,programs,source,labels,owner).last();let a=source.last();let offset=source.first().history.len();
        let actions=fu::trace_actions(lib,programs,source,labels,offset,owner);let es=fu::events(actions);
        &&& g::well_formed(lib,programs,a) && g::well_formed(lib,programs,target) && transport::related(eq,a,target,offset,owner)
        &&& own::separated(a.state,owner)
        &&& fu::catalog(actions)==fu::fresh_records(lib,programs,a.history,offset,owner)
        &&& forall|i:int|offset<=i<a.history.len() ==> historical(lib,programs,#[trigger] a.history[i],owner,a.state.control.fibers[owner].provisions)
        &&& batch::batch(pi::context_eq(eq),batch::redo(es),batch::undo(es),p::project(a.state,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(es)(p::project(a.state,ISet::full())).unwrap(),p::project(target.state,ISet::full()))
    },
{
    deletion::delete_execution(eq,lib,programs,source,labels,owner);own::actual_source(eq,lib,programs,source,labels,owner);own::fresh_historical(eq,lib,programs,source,labels,owner);
    old::only_owner_actions(lib,programs,source,labels,owner);replay::context_equivalence(eq,lib);
    let a=source.last();let offset=source.first().history.len();let actions=fu::trace_actions(lib,programs,source,labels,offset,owner);
    old::batch_source(pi::context_eq(eq),actions,p::project(source.first().state,ISet::full()));batch::recovery(pi::context_eq(eq),fu::events(actions),p::project(source.first().state,ISet::full()));
    assert(g::well_formed(lib,programs,deletion::delete(lib,programs,source,labels,owner).last()));
    assert forall|i:int|offset<=i<a.history.len() implies historical(lib,programs,#[trigger] a.history[i],owner,a.state.control.fibers[owner].provisions) by {old_metadata_implies(lib,programs,a.history[i],owner,a.state.control.fibers[owner].provisions);}
}

#[verifier::opaque]
pub open spec fn example_prefix()->Seq<g::Configuration<int,nat>> {
    let a=crate::old_provision_journal_example::setup()[6];
    let b=g::edit(a,1,crate::Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
    let c=g::land(crate::recovery_examples::library(),crate::old_provision_journal_example::programs(),b,1,crate::Phase::Loading);
    let z=g::land(crate::recovery_examples::library(),crate::old_provision_journal_example::programs(),c,1,crate::Phase::Active);
    seq![a,b,c,z]
}
pub open spec fn example_labels()->Seq<(usize,r::Rule)> {seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(1usize,r::Rule::Finish)]}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn actual_prefix()
    ensures {
        let lib=crate::recovery_examples::library();let programs=crate::old_provision_journal_example::programs();
        let setup=crate::old_provision_journal_example::setup().take(7);let setup_labels=crate::old_provision_journal_example::setup_labels().take(6);
        let source=example_prefix();let labels=example_labels();
        &&& g::execution(lib,programs,setup,setup_labels) && setup.first()==g::empty::<int,nat>() && setup.last()==source.first()
        &&& g::execution(lib,programs,source,labels) && g::well_formed(lib,programs,source.first())
        &&& own::separated(source.first().state,1) && own::fragment(programs,source,labels,source.first().history.len(),1) && old::owner_window(source,labels,1)
        &&& source.first().history.len()==1 && source.first().state.control.fibers[1usize].phase==crate::Phase::Inactive && source.first().state.tables[1usize].is_empty()
        &&& source.last().history.len()==3 && source.last().state.accumulators[1usize]==seq![1nat,2nat]
        &&& source.last().state.tables[0usize][crate::recovery_examples::key(0)]==15
        &&& source.last().state.tables[1usize][crate::recovery_examples::key(1)]==99 && source.last().state.tables[2usize].is_empty()
        &&& g::step(lib,programs,source.last(),g::land(lib,programs,source.last(),2,crate::Phase::Loading),2,r::Rule::Iter)
    },
{
    reveal(example_prefix);reveal(crate::old_provision_journal_example::setup);crate::old_provision_journal_example::actual_setup();sh::example_interface();
    let lib=crate::recovery_examples::library();let programs=crate::old_provision_journal_example::programs();
    let setup=crate::old_provision_journal_example::setup().take(7);let setup_labels=crate::old_provision_journal_example::setup_labels().take(6);
    assert(g::execution(lib,programs,setup,setup_labels));ol::from_empty_safe(crate::recovery_examples::equality(),lib,programs,setup,setup_labels);
    let source=example_prefix();let labels=example_labels();
    assert(setup.last()==source.first());
    assert(g::well_formed(lib,programs,setup[6]));
    assert(g::well_formed(lib,programs,source.first()));
    sh::example_target(source[0].state,1);
    assert(g::step(lib,programs,source[0],source[1],1,r::Rule::Begin));assert(g::step(lib,programs,source[1],source[2],1,r::Rule::Iter));
    let binding=crate::Binding {key:0,realm:0,provider:0};assert(lift::names_key(binding,crate::recovery_examples::key(0)));
    assert(source[2].state.control.fibers[1usize].committed.contains(binding));
    assert(exists|b:crate::Binding|source[2].state.control.fibers[1usize].committed.contains(b) && lift::names_key(b,crate::recovery_examples::key(0)));
    assert(lift::resolve(source[2].state,1,crate::recovery_examples::key(0))==Some(0usize));
    assert(g::step(lib,programs,source[2],source[3],1,r::Rule::Finish));
    assert forall|i:int|0<=i<labels.len() implies g::step(lib,programs,source[i],source[i+1],labels[i].0,labels[i].1) by {if i==0{}else if i==1{}else{assert(i==2);}}
    assert(own::separated(source.first().state,1)) by {
        assert forall|n:usize|s::registered(source.first().state,n) && n!=1 implies dep::declarations(source.first().state,n).disjoint(source.first().state.control.fibers[1usize].provisions) by {if n==0{}else{assert(n==2);}}
    }
    assert(own::fragment(programs,source,labels,1,1));assert(old::owner_window(source,labels,1));
    assert(g::execution(lib,programs,source,labels));
    assert(source.first().history.len()==1);
    assert(source.first().state.control.fibers[1usize].phase==crate::Phase::Inactive);
    assert(source.first().state.tables[1usize].is_empty());
    assert(source.last().history.len()==3);
    assert(source.last().state.accumulators[1usize] =~= seq![1nat,2nat]);
    assert(source.last().state.tables[0usize][crate::recovery_examples::key(0)]==15);
    assert(source.last().state.tables[1usize][crate::recovery_examples::key(1)]==99);
    assert(source.last().state.tables[2usize].is_empty());
    sh::example_target(source.last().state,2);assert(g::step(lib,programs,source.last(),g::land(lib,programs,source.last(),2,crate::Phase::Loading),2,r::Rule::Iter));
}

/// Nonempty pending own Provision and shared Operation; the new foreign
/// Provision is minted on both actual traces with the compressed fresh token.
#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn actual_provision_example()
    ensures {
        let lib=crate::recovery_examples::library();let programs=crate::old_provision_journal_example::programs();let eq=crate::recovery_examples::equality();
        let source=example_prefix();let a=source.last();let z=g::land(lib,programs,a,2,crate::Phase::Loading);let target=deletion::delete(lib,programs,source,example_labels(),1).last();
        let out=transport::advance(lib,programs,a,z,target,2,r::Rule::Iter,1);
        let actions=fu::trace_actions(lib,programs,source,example_labels(),1,1);let es=fu::events(actions);
        &&& g::step(lib,programs,a,z,2,r::Rule::Iter) && g::step(lib,programs,target,out,2,r::Rule::Iter)
        &&& g::well_formed(lib,programs,out) && transport::related(eq,z,out,1,1)
        &&& z.state.tables[2usize][crate::recovery_examples::key(2)]==77 && out.state.tables[2usize][crate::recovery_examples::key(2)]==77
        &&& z.history.len()==4 && out.history.len()==2 && z.state.accumulators[2usize]==seq![3nat] && out.state.accumulators[2usize]==seq![1nat]
        &&& z.state.tables[0usize][crate::recovery_examples::key(0)]==15 && out.state.tables[0usize][crate::recovery_examples::key(0)]==10
        &&& batch::batch(pi::context_eq(eq),batch::redo(es),batch::undo(es),p::project(z.state,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(es)(p::project(z.state,ISet::full())).unwrap(),p::project(out.state,ISet::full()))
    },
{
    actual_prefix();sh::example_interface();let lib=crate::recovery_examples::library();let programs=crate::old_provision_journal_example::programs();let eq=crate::recovery_examples::equality();
    let source=example_prefix();let labels=example_labels();let a=source.last();let target=deletion::delete(lib,programs,source,labels,1).last();
    prefix_batch(eq,lib,programs,source,labels,1);
    let actions=fu::trace_actions(lib,programs,source,labels,source.first().history.len(),1);
    reveal(example_prefix);reveal(crate::old_provision_journal_example::setup);reveal_with_fuel(deletion::delete,4);
    assert(target==source.first());let z=g::land(lib,programs,a,2,crate::Phase::Loading);
    synchronized_landing(eq,lib,programs,a,z,target,actions,1,1,2,r::Rule::Iter,crate::recovery_examples::key(2),77,Some(1nat));
    let out=transport::advance(lib,programs,a,z,target,2,r::Rule::Iter,1);
    assert(z.state.accumulators[2usize] =~= seq![3nat]);assert(out.state.accumulators[2usize] =~= seq![1nat]);
}
}
