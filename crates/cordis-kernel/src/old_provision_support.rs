//! Domain-changing old Provision receipts across an installed owner's window.
//!
//! A successful source inverse supplies current permission. The real Unload
//! no-user guard separates the installed owner's declarations from that key.
//! Strict crossing then derives the target inverse's domain; target success is
//! never an input. These are single-receipt and batch-algebra bridges, not a
//! complete old/new-token lifecycle deletion theorem.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, dependent_lift as dep, foreign_unload as fu,
    grammar_lift as lift, mediated as m, mixed_grammar as g, mixed_syntax as syntax,
    mixed_transposition as t, observational_grammar as og, observational_lift as ol,
    old_journal_unload as old, partial_independence as pi, preservation as inv, projection as p,
    providing_owner_deletion as own, providing_owner_execution as deletion,
    providing_owner_transport as transport, recovery_examples as ex, refinement as r,
    semantics as s, shared_execution as sh, shared_replay as replay,
    shared_unload_execution as history, strict_batch_recovery as batch, strict_journal as sj,
    Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn receipt<U>(actor:usize,key:Port)->g::Receipt<U> {
    g::Receipt::Table {receipt:lift::Receipt {actor,inverse:lift::Inverse::Provision {key}}}
}
pub open spec fn cut<U>(key:Port)->m::PartialMap<IMap<Port,U>> {
    |table:IMap<Port,U>|if table.dom().contains(key) {Some(table.remove(key))}else{None}
}
pub proof fn cut_contract<U>(eq:spec_fn(Port,U,U)->bool,actor:usize,key:Port)
    ensures sh::flat(receipt::<U>(actor,key))==cut(key),pi::respects(pi::context_eq(eq),cut(key)),
        cut(key)==pi::lift(key,|slot:Option<U>|if slot.is_some(){Some(None)}else{None}),
{
    assert(sh::flat(receipt::<U>(actor,key)) =~= cut(key));
    assert(cut(key) =~= pi::lift(key,|slot:Option<U>|if slot.is_some(){Some(None)}else{None}));
    assert forall|a:IMap<Port,U>,b:IMap<Port,U>| #![trigger cut(key)(a),cut(key)(b)] pi::context_eq(eq)(a,b) implies {
        &&& cut(key)(a).is_some()==cut(key)(b).is_some()
        &&& cut(key)(a).is_some() ==> pi::context_eq(eq)(cut(key)(a).unwrap(),cut(key)(b).unwrap())
    } by {assert(ISet::<Port>::full().contains(key));assert(a.dom().contains(key)==b.dom().contains(key));m::remove_related(eq,ISet::full(),key,a,b);}
}

/// The two actual interpreters revoke the same actor/key. Their current global
/// observations need not agree: reference is the owner's erased value replay.
pub proof fn one_inverse<U>(eq:spec_fn(Port,U,U)->bool,source:s::State<U>,target:s::State<U>,actor:usize,key:Port,reference:IMap<Port,U>)
    requires inv::well_formed(source),inv::well_formed(target),s::registered(target,actor),
        source.control.fibers[actor]==target.control.fibers[actor],g::undo(receipt::<U>(actor,key),source).is_some(),
        cut(key)(reference).is_some(),pi::context_eq(eq)(reference,p::project(target,ISet::full())),
    ensures {
        let a=g::undo(receipt::<U>(actor,key),source).unwrap();let b=g::undo(receipt::<U>(actor,key),target).unwrap();
        &&& g::undo(receipt::<U>(actor,key),target).is_some() && inv::well_formed(a) && inv::well_formed(b)
        &&& a.control==source.control && b.control==target.control
        &&& a.tables[actor]==source.tables[actor].remove(key) && b.tables[actor]==target.tables[actor].remove(key)
        &&& forall|n:usize| s::registered(source,n) && n!=actor ==> a.tables[n]==source.tables[n]
        &&& forall|n:usize| s::registered(target,n) && n!=actor ==> b.tables[n]==target.tables[n]
        &&& pi::context_eq(eq)(cut(key)(reference).unwrap(),p::project(b,ISet::full()))
    },
{
    cut_contract(eq,actor,key);
    assert(own::pinned(receipt::<U>(actor,key),target,actor));
    own::inverse_definedness(receipt::<U>(actor,key),target,actor);
    fu::table_inverse_projects(receipt::<U>(actor,key),source);
    lift::undo_preservation(lift::Receipt {actor,inverse:lift::Inverse::Provision {key}},source);
}

/// Matching domains survive a simultaneous restriction; only actor loses key.
pub proof fn domains_frame<U>(source:s::State<U>,target:s::State<U>,actor:usize,key:Port)
    requires g::undo(receipt::<U>(actor,key),source).is_some(),g::undo(receipt::<U>(actor,key),target).is_some(),
    ensures {
        let a=g::undo(receipt::<U>(actor,key),source).unwrap();let b=g::undo(receipt::<U>(actor,key),target).unwrap();
        &&& a.control==source.control && b.control==target.control
        &&& forall|n:usize| s::registered(source,n) && s::registered(target,n)
            && source.tables[n].dom()==target.tables[n].dom() ==> a.tables[n].dom()==b.tables[n].dom()
        &&& forall|n:usize| s::registered(source,n) && n!=actor ==> a.tables[n].dom()==source.tables[n].dom()
        &&& forall|n:usize| s::registered(target,n) && n!=actor ==> b.tables[n].dom()==target.tables[n].dom()
    },
{
    assert forall|n:usize| s::registered(source,n) && s::registered(target,n)
        && source.tables[n].dom()==target.tables[n].dom() implies
        g::undo(receipt::<U>(actor,key),source).unwrap().tables[n].dom()==g::undo(receipt::<U>(actor,key),target).unwrap().tables[n].dom() by {
        if n==actor {assert(source.tables[n].remove(key).dom() =~= target.tables[n].remove(key).dom());}
    }
}

/// Strict failure-sensitive commutation with every actual stage generator.
/// Provision is never required to commute with itself: key separation follows
/// from the live provider guard and the installed owner's current permissions.
pub proof fn installed_stage_cross<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,
    current:s::State<U>,owner:usize,actor:usize,key:Port,f:m::PartialMap<IMap<Port,U>>)
    requires og::primitive_theory(eq,lib),inv::well_formed(current),s::registered(current,owner),s::registered(current,actor),owner!=actor,
        current.control.fibers[owner].phase!=Phase::Inactive,!r::relied(current.control,actor),
        g::undo(receipt::<U>(actor,key),current).is_some(),
        d::permitted(lib,dep::declarations(current,owner),current.control.fibers[owner].provisions,node),
        pi::generators(dep::stage(lib,node)).contains(f),
    ensures pi::respects(pi::context_eq(eq),f),pi::commutes(pi::context_eq(eq),f,cut(key)),
{
    replay::context_equivalence(eq,lib);cut_contract(eq,actor,key);
    old::provider_guard_separates_installed_owner(current,owner,actor);
    own::stage_respects(eq,lib,node,dep::declarations(current,owner),current.control.fibers[owner].provisions);
    pi::generator_respects(eq,dep::stage(lib,node),f);
    if let d::Node::Unit=node {
        let identity=|table:IMap<Port,U>|Some(table);
        if f==pi::forward(dep::stage(lib,node)) {assert(f =~= identity);} else {
            let input=choose|table:IMap<Port,U>| #[trigger] m::run(dep::stage(lib,node),table).is_some() && m::run(dep::stage(lib,node),table).unwrap().undo==f;
            assert(f =~= identity);
        }
        fu::identity_contract(pi::context_eq(eq),cut(key));
    } else {
        let own_key=pi::key(dep::stage(lib,node)).unwrap();
        assert(dep::declarations(current,owner).contains(own_key));assert(own_key!=key);
        pi::local_generator(dep::stage(lib,node),f);
        let slot=choose|slot:pi::SlotMap<U>|f==pi::lift(own_key,slot);
        pi::distinct_lifts_commute(eq,own_key,key,slot,|slot:Option<U>|if slot.is_some(){Some(None)}else{None});
    }
}

pub proof fn entry_cross<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    entry:g::Entry<U,I>,current:s::State<U>,owner:usize,actor:usize,key:Port)
    requires og::primitive_theory(eq,lib),inv::well_formed(current),s::registered(current,owner),s::registered(current,actor),owner!=actor,
        current.control.fibers[owner].phase!=Phase::Inactive,!r::relied(current.control,actor),g::undo(receipt::<U>(actor,key),current).is_some(),
        own::historical(lib,programs,entry,owner,current.control.fibers[owner].provisions),g::owner(entry.landed.receipt)==owner,
        r::interface_same(entry.input.control.fibers[owner],current.control.fibers[owner]),
    ensures {
        let pair=fu::entry_pair(lib,programs,entry,owner);
        &&& fu::respectful(pi::context_eq(eq),pair)
        &&& pi::commutes(pi::context_eq(eq),pair.forward,cut(key)) && pi::commutes(pi::context_eq(eq),pair.inverse,cut(key))
    },
{
    let node=replay::dependent(programs(owner)(entry.iterator));let stage=dep::stage(lib,node);let pair=fu::entry_pair(lib,programs,entry,owner);
    replay::actual_receipt_projects(lib,node,entry.input,owner);
    assert(pi::generators(stage).contains(pair.forward));assert(pi::generators(stage).contains(pair.inverse));
    installed_stage_cross(eq,lib,node,current,owner,actor,key,pair.forward);
    installed_stage_cross(eq,lib,node,current,owner,actor,key,pair.inverse);
}

/// Fresh historical inputs retain declarations across the fixed-registry
/// window. This strengthens the provisions-only metadata used by deletion.
pub proof fn fresh_interfaces<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        own::separated(source.first().state,owner),own::fragment(programs,source,labels,source.first().history.len(),owner),
    ensures forall|i:int| source.first().history.len()<=i<source.last().history.len() && g::owner(#[trigger] source.last().history[i].landed.receipt)==owner
        ==> r::interface_same(source.last().history[i].input.control.fibers[owner],source.last().state.control.fibers[owner]),
    decreases labels.len(),
{
    own::fresh_historical(eq,lib,programs,source,labels,owner);
    if labels.len()>0 {
        let prefix=source.drop_last();let previous=labels.drop_last();let a=prefix.last();let z=source.last();let label=labels.last();
        assert(g::execution(lib,programs,prefix,previous));assert(own::fragment(programs,prefix,previous,source.first().history.len(),owner));
        fresh_interfaces(eq,lib,programs,prefix,previous,owner);own::fresh_historical(eq,lib,programs,prefix,previous,owner);
        ol::frame(eq,lib,programs,a,z,label.0,label.1);own::interface_frame(eq,lib,programs,a,z,label.0,label.1,owner);
        assert forall|i:int| source.first().history.len()<=i<z.history.len() && g::owner(#[trigger] z.history[i].landed.receipt)==owner
            implies r::interface_same(z.history[i].input.control.fibers[owner],z.state.control.fibers[owner]) by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);}else{assert(i==a.history.len());assert(z.history[i].input==a.state);}
        }
    }
}

pub proof fn crosses_batch<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,current:s::State<U>,owner:usize,actor:usize,key:Port)
    requires og::primitive_theory(eq,lib),inv::well_formed(current),s::registered(current,owner),s::registered(current,actor),owner!=actor,
        current.control.fibers[owner].phase!=Phase::Inactive,!r::relied(current.control,actor),g::undo(receipt::<U>(actor,key),current).is_some(),
        offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int| offset<=i<entries.len() ==> own::historical(lib,programs,#[trigger] entries[i],owner,current.control.fibers[owner].provisions),
        forall|i:int| offset<=i<entries.len() && g::owner(#[trigger] entries[i].landed.receipt)==owner
            ==> r::interface_same(entries[i].input.control.fibers[owner],current.control.fibers[owner]),
    ensures pi::respects(pi::context_eq(eq),cut(key)),pi::commutes(pi::context_eq(eq),cut(key),batch::redo(fu::events(actions))),
        pi::commutes(pi::context_eq(eq),cut(key),batch::undo(fu::events(actions))),
{
    replay::context_equivalence(eq,lib);cut_contract(eq,actor,key);old::forward_origins(actions);fu::journal_origins(actions);
    let records=fu::catalog(actions);let es=fu::events(actions);
    assert forall|i:int| 0<=i<batch::forwards(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] batch::forwards(es)[i])
        && pi::commutes(pi::context_eq(eq),batch::forwards(es)[i],cut(key)) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].forward==batch::forwards(es)[i];
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));entry_cross(eq,lib,programs,entry,current,owner,actor,key);
    }
    assert forall|i:int| 0<=i<sj::journal(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] sj::journal(es)[i])
        && pi::commutes(pi::context_eq(eq),sj::journal(es)[i],cut(key)) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));entry_cross(eq,lib,programs,entry,current,owner,actor,key);
    }
    sj::word_commutes(pi::context_eq(eq),batch::forwards(es),cut(key));sj::word_commutes(pi::context_eq(eq),sj::journal(es),cut(key));
}

/// The existing actual-window induction supplies batch and historical facts.
/// The final strict cut domain and real target invocation are derived here.
pub proof fn target_old_provision<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,source:s::State<U>,target:s::State<U>,owner:usize,actor:usize,key:Port)
    requires og::primitive_theory(eq,lib),inv::well_formed(source),inv::well_formed(target),s::registered(source,owner),s::registered(source,actor),s::registered(target,actor),owner!=actor,
        source.control.fibers[owner].phase!=Phase::Inactive,!r::relied(source.control,actor),g::undo(receipt::<U>(actor,key),source).is_some(),
        source.control.fibers[actor]==target.control.fibers[actor],offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int| offset<=i<entries.len() ==> own::historical(lib,programs,#[trigger] entries[i],owner,source.control.fibers[owner].provisions),
        forall|i:int| offset<=i<entries.len() && g::owner(#[trigger] entries[i].landed.receipt)==owner
            ==> r::interface_same(entries[i].input.control.fibers[owner],source.control.fibers[owner]),
        batch::batch(pi::context_eq(eq),batch::redo(fu::events(actions)),batch::undo(fu::events(actions)),p::project(source,ISet::full())),
        pi::context_eq(eq)(batch::undo(fu::events(actions))(p::project(source,ISet::full())).unwrap(),p::project(target,ISet::full())),
    ensures {
        let a=g::undo(receipt::<U>(actor,key),source).unwrap();let b=g::undo(receipt::<U>(actor,key),target).unwrap();let es=fu::events(actions);
        &&& g::undo(receipt::<U>(actor,key),target).is_some() && inv::well_formed(a) && inv::well_formed(b)
        &&& a.control==source.control && b.control==target.control
        &&& batch::batch(pi::context_eq(eq),batch::redo(es),batch::undo(es),p::project(a,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(es)(p::project(a,ISet::full())).unwrap(),p::project(b,ISet::full()))
        &&& forall|n:usize| s::registered(source,n) && n!=actor ==> a.tables[n]==source.tables[n]
        &&& forall|n:usize| s::registered(target,n) && n!=actor ==> b.tables[n]==target.tables[n]
        &&& a.tables[actor]==source.tables[actor].remove(key) && b.tables[actor]==target.tables[actor].remove(key)
    },
{
    replay::context_equivalence(eq,lib);let es=fu::events(actions);let before=p::project(source,ISet::full());
    crosses_batch(eq,lib,programs,entries,actions,offset,source,owner,actor,key);
    fu::table_inverse_projects(receipt::<U>(actor,key),source);cut_contract(eq,actor,key);
    batch::foreign_cross(pi::context_eq(eq),batch::redo(es),batch::undo(es),cut(key),before);
    one_inverse(eq,source,target,actor,key,batch::undo(es)(before).unwrap());
}

/// A genuine old singleton Provision Unload after an owner-only window. The
/// deleted prefix, authentic retained token and final target Unload are all
/// derived. No target execution, restoration or batch invariant is assumed.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_singleton_unload<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,owner:usize,actor:usize,key:Port,token:nat)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        own::separated(source.first().state,owner),own::fragment(programs,source,labels,source.first().history.len(),owner),old::owner_window(source,labels,owner),
        source.first().state.control.fibers[owner].phase==Phase::Inactive,source.first().state.tables[owner].is_empty(),
        source.last().state.control.fibers[owner].phase!=Phase::Inactive,actor!=owner,g::step(lib,programs,source.last(),z,actor,r::Rule::Unload),
        source.last().state.accumulators[actor]==seq![token],token<source.first().history.len(),
        source.last().history[token as int].landed.receipt==receipt::<U>(actor,key),
    ensures {
        let target=deletion::delete(lib,programs,source,labels,owner);let out=g::unload(target.last(),actor);
        let es=fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner));
        &&& g::step(lib,programs,target.last(),out,actor,r::Rule::Unload) && g::well_formed(lib,programs,out)
        &&& g::execution(lib,programs,target.push(out),sh::labels_without(labels,owner).push((actor,r::Rule::Unload)))
        &&& transport::related(eq,z,out,source.first().history.len(),owner)
        &&& batch::batch(pi::context_eq(eq),batch::redo(es),batch::undo(es),p::project(z.state,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(es)(p::project(z.state,ISet::full())).unwrap(),p::project(out.state,ISet::full()))
        &&& !z.state.tables[actor].dom().contains(key) && !out.state.tables[actor].dom().contains(key)
        &&& target.last().history[token as int]==source.last().history[token as int]
    },
{
    own::actual_source(eq,lib,programs,source,labels,owner);own::fresh_historical(eq,lib,programs,source,labels,owner);
    fresh_interfaces(eq,lib,programs,source,labels,owner);deletion::delete_execution(eq,lib,programs,source,labels,owner);
    old::only_owner_actions(lib,programs,source,labels,owner);replay::context_equivalence(eq,lib);
    let a=source.last();let offset=source.first().history.len();let actions=fu::trace_actions(lib,programs,source,labels,offset,owner);
    let es=fu::events(actions);let initial=p::project(source.first().state,ISet::full());
    old::batch_source(pi::context_eq(eq),actions,initial);batch::recovery(pi::context_eq(eq),es,initial);
    let target=deletion::delete(lib,programs,source,labels,owner);let b=target.last();let tokens=a.state.accumulators[actor];
    assert(b.history[token as int]==a.history[token as int]);old::old_indices(a.history,offset,owner,tokens);assert(b.state.accumulators[actor]==tokens);
    reveal_with_fuel(g::restore,2);assert(g::undo(receipt::<U>(actor,key),a.state).is_some());
    target_old_provision(eq,lib,programs,a.history,actions,offset,a.state,b.state,owner,actor,key);
    domains_frame(a.state,b.state,actor,key);
    assert(g::restore(b.history,tokens,b.state,actor).is_some());
    let sa=g::restore(a.history,tokens,a.state,actor).unwrap();let ta=g::restore(b.history,tokens,b.state,actor).unwrap();
    p::unique_owner(sa);p::unique_owner(ta);
    p::lifecycle_edit(sa,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
    p::lifecycle_edit(ta,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
    transport::no_users(a,b,owner,actor);let out=g::unload(b,actor);assert(g::step(lib,programs,b,out,actor,r::Rule::Unload));
    ol::configuration_preservation(eq,lib,programs,b,out,actor,r::Rule::Unload);ol::frame(eq,lib,programs,a,z,actor,r::Rule::Unload);ol::frame(eq,lib,programs,b,out,actor,r::Rule::Unload);
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n]
    } by {assert(s::registered(a.state,n));assert(s::registered(b.state,n));}
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
        assert(s::registered(a.state,n));if n==actor {history::rename_laws(a.history,offset,owner,Seq::empty(),0);}
    }
    let kept=sh::labels_without(labels,owner);
    assert forall|i:int| 0<=i<kept.push((actor,r::Rule::Unload)).len() implies
        g::step(lib,programs,target.push(out)[i],target.push(out)[i+1],kept.push((actor,r::Rule::Unload))[i].0,kept.push((actor,r::Rule::Unload))[i].1) by {
        if i<kept.len() {assert(target.push(out)[i]==target[i]);assert(target.push(out)[i+1]==target[i+1]);}else{assert(i==kept.len());assert(target.push(out)[i]==target.last());}
    }
}

pub open spec fn example_programs()->g::Programs<Port,int,int,(),()> {
    |actor:usize| |_:()|g::Node::Dependent {node:d::Node::Provision {key:ex::key(actor),value:if actor==0 {10}else{99},next:None}}
}
#[verifier::opaque]
pub open spec fn example_setup(reads:bool)->Seq<g::Configuration<int,()>> {
    let a0=g::empty::<int,()>();let a1=t::insert(a0,0,None,ISet::empty(),ex::provided(0),());
    let a2=t::insert(a1,1,None,if reads{ex::provided(0)}else{ISet::empty()},ex::provided(1),());
    let a3=g::edit(a2,0,Phase::Loading,ISet::empty(),Some(()),Seq::empty());let a4=g::land(ex::library(),example_programs(),a3,0,Phase::Active);
    seq![a0,a1,a2,a3,a4]
}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Finish)]
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn example_bootstrap(reads:bool)
    ensures g::execution(ex::library(),example_programs(),example_setup(reads),setup_labels()),
        example_setup(reads).first()==g::empty::<int,()>(),g::well_formed(ex::library(),example_programs(),example_setup(reads).last()),
        example_setup(reads).last().history.len()==1,example_setup(reads).last().history[0].landed.receipt==receipt::<int>(0,ex::key(0)),
        example_setup(reads).last().state.tables[0usize]==IMap::empty().insert(ex::key(0),10),
        example_setup(reads).last().state.tables[1usize].is_empty(),
{
    reveal(example_setup);sh::example_interface();let lib=ex::library();let states=example_setup(reads);let programs=example_programs();
    let dependencies=if reads{ex::provided(0)}else{ISet::empty()};
    syntax::constructor_member(lib,programs,0,ISet::<Port>::empty().union(ex::provided(0)),ex::provided(0),());
    syntax::constructor_member(lib,programs,1,dependencies.union(ex::provided(1)),ex::provided(1),());
    g::empty_well_formed(lib,programs);t::insertion_step(lib,programs,states[0],0,None,ISet::empty(),ex::provided(0),());
    ol::configuration_preservation(ex::equality(),lib,programs,states[0],states[1],0,r::Rule::Insert);
    t::insertion_step(lib,programs,states[1],1,None,dependencies,ex::provided(1),());
    ol::configuration_preservation(ex::equality(),lib,programs,states[1],states[2],1,r::Rule::Insert);
    assert(g::step(lib,programs,states[2],states[3],0,r::Rule::Begin));ol::configuration_preservation(ex::equality(),lib,programs,states[2],states[3],0,r::Rule::Begin);
    assert(g::step(lib,programs,states[3],states[4],0,r::Rule::Finish));ol::configuration_preservation(ex::equality(),lib,programs,states[3],states[4],0,r::Rule::Finish);
    assert(g::execution(lib,programs,states,setup_labels())) by {
        assert forall|i:int|0<=i<setup_labels().len() implies g::step(lib,programs,states[i],states[i+1],setup_labels()[i].0,setup_labels()[i].1) by {
            if i==0{}else if i==1{}else if i==2{}else{assert(i==3);}
        }
    }
}
#[verifier::opaque]
pub open spec fn example_window()->Seq<g::Configuration<int,()>> {
    let a0=example_setup(false).last();let a1=g::edit(a0,1,Phase::Loading,ISet::empty(),Some(()),Seq::empty());
    let a2=g::land(ex::library(),example_programs(),a1,1,Phase::Active);let a3=sh::retire(a2,0);
    let a4=g::edit(a3,0,Phase::Unloading,ISet::empty(),None,a3.state.accumulators[0usize]);seq![a0,a1,a2,a3,a4]
}
pub open spec fn window_labels()->Seq<(usize,r::Rule)> {
    seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Finish),(0usize,r::Rule::Retire),(0usize,r::Rule::Leave)]
}
#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn nonempty_actual_example()
    ensures {
        let source=example_window();let labels=window_labels();let z=g::unload(source.last(),0);
        let target=deletion::delete(ex::library(),example_programs(),source,labels,1);let out=g::unload(target.last(),0);
        &&& g::execution(ex::library(),example_programs(),example_setup(false),setup_labels()) && example_setup(false).first()==g::empty::<int,()>()
        &&& example_setup(false).last()==source.first() && g::execution(ex::library(),example_programs(),source.push(z),labels.push((0usize,r::Rule::Unload)))
        &&& g::execution(ex::library(),example_programs(),target.push(out),sh::labels_without(labels,1).push((0usize,r::Rule::Unload)))
        &&& source.last().history.len()==2 && target.last().history.len()==1
        &&& source.last().state.tables[0usize]==IMap::empty().insert(ex::key(0),10)
        &&& source.last().state.tables[1usize]==IMap::empty().insert(ex::key(1),99)
        &&& z.state.tables[0usize].is_empty() && out.state.tables[0usize].is_empty()
        &&& z.state.tables[1usize]==IMap::empty().insert(ex::key(1),99) && out.state.tables[1usize].is_empty()
    },
{
    reveal(example_setup);reveal(example_window);example_bootstrap(false);sh::example_interface();let lib=ex::library();let programs=example_programs();
    let states=example_window();let labels=window_labels();
    assert(g::step(lib,programs,states[0],states[1],1,r::Rule::Begin));assert(g::step(lib,programs,states[1],states[2],1,r::Rule::Finish));
    ch::concrete_child_retirement(states[2].state,0);assert(g::step(lib,programs,states[2],states[3],0,r::Rule::Retire));assert(g::step(lib,programs,states[3],states[4],0,r::Rule::Leave));
    assert(g::execution(lib,programs,states,labels)) by {
        assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,states[i],states[i+1],labels[i].0,labels[i].1) by {
            if i==0{}else if i==1{}else if i==2{}else{assert(i==3);}
        }
    }
    assert(own::separated(states[0].state,1)) by {
        assert forall|n:usize|s::registered(states[0].state,n) && n!=1 implies dep::declarations(states[0].state,n).disjoint(states[0].state.control.fibers[1usize].provisions) by {assert(n==0);}
    }
    assert(own::fragment(programs,states,labels,1,1));assert(old::owner_window(states,labels,1));
    reveal_with_fuel(g::restore,2);let z=g::unload(states.last(),0);assert(g::step(lib,programs,states.last(),z,0,r::Rule::Unload));
    actual_singleton_unload(ex::equality(),lib,programs,states,labels,z,1,0,ex::key(0),0);
    let target=deletion::delete(lib,programs,states,labels,1);let out=g::unload(target.last(),0);
    assert(target.last().history.len()==1) by {reveal_with_fuel(history::index,3);}
    assert(z.state.tables[0usize].is_empty());
    assert(s::registered(z.state,0));
    assert(out.state.tables[0usize].dom()==z.state.tables[0usize].dom());
    assert(out.state.tables[0usize].is_empty()) by {assert(out.state.tables[0usize] =~= IMap::empty());}
    assert(out.state.tables[1usize].is_empty());
    assert(z.state.tables[1usize]==IMap::empty().insert(ex::key(1),99));
    assert(states.last().state.tables[0usize]==IMap::empty().insert(ex::key(0),10));
    assert(states.last().state.tables[1usize]==IMap::empty().insert(ex::key(1),99));
    assert forall|i:int|0<=i<labels.push((0usize,r::Rule::Unload)).len() implies
        g::step(lib,programs,states.push(z)[i],states.push(z)[i+1],labels.push((0usize,r::Rule::Unload))[i].0,labels.push((0usize,r::Rule::Unload))[i].1) by {
        if i<labels.len(){assert(states.push(z)[i]==states[i]);assert(states.push(z)[i+1]==states[i+1]);}else{assert(i==labels.len());assert(states.push(z)[i]==states.last());}
    }
}

/// An actually inserted Inactive owner may declare the retiring provider's
/// key. The Unload guard allows removal; it does not imply separation until
/// the owner is installed. This is a reachable guard counterexample.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn inactive_guard_counterexample()
    ensures {
        let a=example_setup(true).last();let b=sh::retire(a,0);let c=g::edit(b,0,Phase::Unloading,ISet::empty(),None,b.state.accumulators[0usize]);let z=g::unload(c,0);
        &&& g::execution(ex::library(),example_programs(),example_setup(true),setup_labels()) && example_setup(true).first()==g::empty::<int,()>()
        &&& g::step(ex::library(),example_programs(),a,b,0,r::Rule::Retire)
        &&& g::step(ex::library(),example_programs(),b,c,0,r::Rule::Leave)
        &&& g::step(ex::library(),example_programs(),c,z,0,r::Rule::Unload)
        &&& inv::well_formed(c.state) && c.state.control.fibers[1usize].phase==Phase::Inactive && !r::relied(c.state.control,0)
        &&& !dep::declarations(c.state,1).disjoint(c.state.control.fibers[0usize].provisions)
        &&& z.state.tables[0usize].is_empty()
    },
{
    reveal(example_setup);example_bootstrap(true);sh::example_interface();let lib=ex::library();let programs=example_programs();
    let a=example_setup(true).last();let b=sh::retire(a,0);let c=g::edit(b,0,Phase::Unloading,ISet::empty(),None,b.state.accumulators[0usize]);
    ch::concrete_child_retirement(a.state,0);assert(g::step(lib,programs,a,b,0,r::Rule::Retire));ol::configuration_preservation(ex::equality(),lib,programs,a,b,0,r::Rule::Retire);
    assert(g::step(lib,programs,b,c,0,r::Rule::Leave));ol::configuration_preservation(ex::equality(),lib,programs,b,c,0,r::Rule::Leave);
    assert(dep::declarations(c.state,1).contains(ex::key(0)));assert(c.state.control.fibers[0usize].provisions.contains(ex::key(0)));
    reveal_with_fuel(g::restore,2);assert(g::step(lib,programs,c,g::unload(c,0),0,r::Rule::Unload));
}
}
