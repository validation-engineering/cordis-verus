//! Construction of surviving lifecycle prefixes for shared dependency keys.
//!
//! The owner stays registered with no provisions. Its lifecycle calls are
//! omitted while external retirement is retained. Foreign landings use their
//! own actual input, returned inverse and fresh target-history index.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, dependent_lift as dep, global,
    grammar_lift as lift, mediated as m, mixed_grammar as g, mixed_syntax as syntax,
    mixed_transposition as t, observational_grammar as og, observational_lift as ol,
    partial_independence as pi, preservation as inv, projection as p, recovery_examples as ex,
    refinement as r, semantics as s, shared_replay as replay, strict_journal as sj, Binding, Phase,
    Port,
};
use vstd::prelude::*;

verus! {

/// Journals and historical receipts are deliberately not compared literally.
/// Each target history is authenticated by its own constructed execution.
pub open spec fn controls<U,I>(source:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize)->bool {
    &&& s::registered(source.state,owner) && source.state.control.fibers[owner].provisions.is_empty()
    &&& target.state.control.fibers.dom()==source.state.control.fibers.dom()
    &&& r::interface_same(source.state.control.fibers[owner],target.state.control.fibers[owner])
    &&& source.state.control.fibers[owner].retired==target.state.control.fibers[owner].retired
    &&& target.state.control.fibers[owner].phase==Phase::Inactive && target.state.control.fibers[owner].committed.is_empty()
    &&& target.roots==source.roots && target.current[owner].is_none()
    &&& forall|n:usize| s::registered(source.state,n) ==> {
        &&& source.state.tables[n].dom()==target.state.tables[n].dom()
        &&& (n!=owner ==> source.state.control.fibers[n]==target.state.control.fibers[n] && source.current[n]==target.current[n])
    }
}
pub proof fn publication<U,I>(source:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize,actor:usize,view:ISet<Binding>)
    requires inv::well_formed(source.state),inv::well_formed(target.state),controls(source,target,owner),s::registered(source.state,actor),actor!=owner,
    ensures s::target(source.state,actor,view)==s::target(target.state,actor,view),s::coherent(source.state,actor)==s::coherent(target.state,actor),
{
    assert forall|key:Port,n:usize| s::publishes(source.state,key,n)==s::publishes(target.state,key,n) by {
        if n==owner {assert(source.state.tables[n].is_empty());assert(target.state.tables[n].is_empty());}
        else if s::registered(source.state,n) {assert(source.state.control.fibers[n]==target.state.control.fibers[n]);}
    }
}
pub proof fn operation_domains<A,X,U,B,I>(lib:g::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),replay::operational(node),dep::run(lib,node,a,actor).is_some(),
    ensures {
        let z=dep::run(lib,node,a,actor).unwrap().state;
        &&& z.control==a.control && z.effects==a.effects && z.iterators==a.iterators && z.accumulators==a.accumulators
        &&& forall|n:usize| s::registered(a,n) ==> z.tables[n].dom()==a.tables[n].dom()
    },
{
    lift::run_preservation(dep::stage(lib,node),a,actor);
    match node {
        crate::dependent_grammar::Node::Operation {operation,argument,..}=>{
            let key=(lib.key)(operation);let provider=lift::resolve(a,actor,key).unwrap();
            let value=(lib.apply)(operation,argument)(a.tables[provider][key]).unwrap().value;
            assert(a.tables[provider].insert(key,value).dom() =~= a.tables[provider].dom());
        },_=>{},
    }
}
pub open spec fn keep(actor:usize,rule:r::Rule,owner:usize)->bool {actor!=owner || rule==r::Rule::Retire}
pub open spec fn retire<U,I>(a:g::Configuration<U,I>,actor:usize)->g::Configuration<U,I> {
    g::Configuration {state:s::with_control(a.state,global::retire_fiber(a.state.control,actor)),roots:a.roots,current:a.current,history:a.history}
}
pub open spec fn advance<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:g::Configuration<U,I>,next:g::Configuration<U,I>,
    target:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)->g::Configuration<U,I> {
    if !keep(actor,rule,owner) {target}
    else if g::landing(source,next,rule) {g::land(lib,programs,target,actor,next.state.control.fibers[actor].phase)}
    else if rule==r::Rule::Retire {retire(target,actor)}
    else if rule==r::Rule::Begin {g::edit(target,actor,Phase::Loading,next.state.control.fibers[actor].committed,Some(target.roots[actor]),Seq::empty())}
    else {g::edit(target,actor,Phase::Unloading,target.state.control.fibers[actor].committed,None,target.state.accumulators[actor])}
}

pub proof fn initial_controls<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,owner:usize)
    requires g::well_formed(lib,programs,a),s::registered(a.state,owner),a.state.control.fibers[owner].provisions.is_empty(),
        a.state.control.fibers[owner].phase==Phase::Inactive,
    ensures controls(a,a,owner),
{
    assert(a.state.iterators[owner]==dep::marker(a.current[owner]));
    assert(a.current[owner].is_none());
}

/// Fixed-registry operational stages preserve table domains even when they
/// change observable shared values. Control-only source steps do so as well.
pub proof fn source_domains<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),replay::fragment_step(programs,a,z,actor,rule),
    ensures a.state.control.fibers.dom()==z.state.control.fibers.dom(),a.roots==z.roots,
        forall|n:usize| s::registered(a.state,n) ==> a.state.tables[n].dom()==z.state.tables[n].dom(),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);
    if g::landing(a,z,rule) {
        let node=replay::dependent(programs(actor)(a.current[actor].unwrap()));
        operation_domains(lib,node,a.state,actor);
        assert(programs(actor)(a.current[actor].unwrap())==g::Node::Dependent {node});
    }
    assert forall|n:usize| a.state.control.fibers.dom().contains(n)==z.state.control.fibers.dom().contains(n) by {
        if n==actor {match rule {r::Rule::Retire=>{},_=>{},}}
        else if !g::landing(a,z,rule) {assert(r::registered(a.state.control,n)==r::registered(z.state.control,n));}
    }
    assert(a.state.control.fibers.dom() =~= z.state.control.fibers.dom());
}

/// The target landing is interpreted again against its own actual input. Its
/// receipt is authenticated by that invocation; no literal inverse equality is
/// assumed when hidden representation changes along observational equivalence.
pub proof fn foreign_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,target:g::Configuration<U,I>,z:g::Configuration<U,I>,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        replay::fragment(programs,source,labels),g::well_formed(lib,programs,source.last()),g::well_formed(lib,programs,target),controls(source.last(),target,owner),actor!=owner,
        g::step(lib,programs,source.last(),z,actor,rule),g::landing(source.last(),z,rule),replay::fragment_step(programs,source.last(),z,actor,rule),
        pi::context_eq(eq)(sj::foreign(replay::events(lib,programs,source,labels,owner),p::project(source.first().state,ISet::full())).unwrap(),p::project(target.state,ISet::full())),
    ensures {
        let a=source.last();let out=advance(lib,programs,a,z,target,actor,rule,owner);
        let es=replay::events(lib,programs,source,labels,owner);let initial=p::project(source.first().state,ISet::full());
        &&& g::step(lib,programs,target,out,actor,rule) && g::well_formed(lib,programs,out) && controls(z,out,owner)
        &&& pi::context_eq(eq)(sj::foreign(es.push(replay::event(lib,programs,a,z,actor,rule,owner)),initial).unwrap(),p::project(out.state,ISet::full()))
    },
{
    let a=source.last();let id=a.current[actor].unwrap();let node=replay::dependent(programs(actor)(id));
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::run_members(eq,lib,programs,a.state,actor,id);
    assert(programs(actor)(id)==g::Node::Dependent {node});
    assert(target.state.control.fibers[actor]==a.state.control.fibers[actor]);
    replay::next_foreign_call(eq,lib,programs,source,labels,owner,node,target.state,actor);
    publication(a,target,owner,actor,a.state.control.fibers[actor].committed);
    let out=advance(lib,programs,a,z,target,actor,rule,owner);
    assert(g::step(lib,programs,target,out,actor,rule));
    ol::configuration_preservation(eq,lib,programs,target,out,actor,rule);
    source_domains(eq,lib,programs,a,z,actor,rule);
    source_domains(eq,lib,programs,target,out,actor,rule);
    operation_domains(lib,node,a.state,actor);operation_domains(lib,node,target.state,actor);
    assert forall|n:usize| s::registered(z.state,n) implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& (n!=owner ==> z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n])
    } by {if n!=actor && n!=owner {assert(a.current[n]==target.current[n]);}}
    let landed=dep::run(lib,node,target.state,actor).unwrap().state;
    lift::run_preservation(dep::stage(lib,node),target.state,actor);p::unique_owner(landed);
    p::lifecycle_edit(landed,actor,z.state.control.fibers[actor].phase,target.state.control.fibers[actor].committed,
        dep::marker(out.current[actor]),target.state.accumulators[actor].push(target.history.len()),ISet::full());
}

/// Control-only guards depend on actual publication and committed views. They
/// do not read the historical token numbers or hidden value representatives.
pub proof fn control_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),controls(a,target,owner),
        g::step(lib,programs,a,z,actor,rule),replay::fragment_step(programs,a,z,actor,rule),!g::landing(a,z,rule),
    ensures {
        let out=advance(lib,programs,a,z,target,actor,rule,owner);
        &&& controls(z,out,owner) && g::well_formed(lib,programs,out)
        &&& (keep(actor,rule,owner) ==> g::step(lib,programs,target,out,actor,rule))
        &&& p::project(out.state,ISet::full())==p::project(target.state,ISet::full())
    },
{
    let out=advance(lib,programs,a,z,target,actor,rule,owner);
    source_domains(eq,lib,programs,a,z,actor,rule);
    ol::frame(eq,lib,programs,a,z,actor,rule);
    if actor!=owner {publication(a,target,owner,actor,z.state.control.fibers[actor].committed);}
    if keep(actor,rule,owner) {
        if rule==r::Rule::Retire {
            assert(r::frame(target.state.control,out.state.control,actor));
            assert(s::child_retire(target.state,out.state,actor));
        }
        assert(g::step(lib,programs,target,out,actor,rule));
        ol::configuration_preservation(eq,lib,programs,target,out,actor,rule);
        p::unique_owner(target.state);p::unique_owner(out.state);
        assert(p::bindings_equal(target.state,out.state));p::projection_equal(target.state,out.state,ISet::full());
    }
    assert forall|n:usize| s::registered(z.state,n) implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& (n!=owner ==> z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n])
    } by {if n!=actor {assert(a.state.control.fibers[n]==z.state.control.fibers[n]);}}
}

pub proof fn own_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),controls(a,target,owner),
        g::step(lib,programs,a,z,owner,rule),replay::fragment_step(programs,a,z,owner,rule),g::landing(a,z,rule),
    ensures controls(z,target,owner),
{
    source_domains(eq,lib,programs,a,z,owner,rule);ol::frame(eq,lib,programs,a,z,owner,rule);
    let node=replay::dependent(programs(owner)(a.current[owner].unwrap()));operation_domains(lib,node,a.state,owner);
    assert forall|n:usize| s::registered(z.state,n) implies {
        &&& z.state.tables[n].dom()==target.state.tables[n].dom()
        &&& (n!=owner ==> z.state.control.fibers[n]==target.state.control.fibers[n] && z.current[n]==target.current[n])
    } by {if n!=owner {assert(a.state.control.fibers[n]==z.state.control.fibers[n]);}}
}

/// One source transition either constructs a real target transition or is a
/// deleted owner transition. The invariant uses strict foreign replay, whose
/// definedness was proved from the actual source's local operation witnesses.
pub proof fn step_replay<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,target:g::Configuration<U,I>,z:g::Configuration<U,I>,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        replay::fragment(programs,source,labels),g::well_formed(lib,programs,source.last()),g::well_formed(lib,programs,target),controls(source.last(),target,owner),
        g::step(lib,programs,source.last(),z,actor,rule),replay::fragment_step(programs,source.last(),z,actor,rule),
        pi::context_eq(eq)(sj::foreign(replay::events(lib,programs,source,labels,owner),p::project(source.first().state,ISet::full())).unwrap(),p::project(target.state,ISet::full())),
    ensures {
        let a=source.last();let out=advance(lib,programs,a,z,target,actor,rule,owner);
        let es=replay::events(lib,programs,source,labels,owner);let initial=p::project(source.first().state,ISet::full());
        &&& controls(z,out,owner) && g::well_formed(lib,programs,out)
        &&& (keep(actor,rule,owner) ==> g::step(lib,programs,target,out,actor,rule))
        &&& pi::context_eq(eq)(sj::foreign(es.push(replay::event(lib,programs,a,z,actor,rule,owner)),initial).unwrap(),p::project(out.state,ISet::full()))
    },
{
    let a=source.last();let es=replay::events(lib,programs,source,labels,owner);let initial=p::project(source.first().state,ISet::full());
    let e=replay::event(lib,programs,a,z,actor,rule,owner);
    assert(es.push(e).drop_last() =~= es);
    replay::strict_fragment_recovery(eq,lib,programs,source,labels,owner);
    if g::landing(a,z,rule) {
        if actor==owner {own_landing(eq,lib,programs,a,z,target,owner,rule);assert(e.own);}
        else {foreign_landing(eq,lib,programs,source,labels,target,z,owner,actor,rule);}
    } else {control_step(eq,lib,programs,a,z,target,owner,actor,rule);}
}

#[verifier::opaque]
pub open spec fn labels_without(labels:Seq<(usize,r::Rule)>,owner:usize)->Seq<(usize,r::Rule)>
    decreases labels.len(),
{
    if labels.len()==0 {Seq::empty()} else {
        let before=labels_without(labels.drop_last(),owner);let label=labels.last();
        if keep(label.0,label.1,owner) {before.push(label)} else {before}
    }
}
#[verifier::opaque]
pub open spec fn delete<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)->Seq<g::Configuration<U,I>>
    decreases labels.len(),
{
    if labels.len()==0 {seq![source.first()]} else {
        let before=delete(lib,programs,source.drop_last(),labels.drop_last(),owner);let label=labels.last();
        if keep(label.0,label.1,owner) {before.push(advance(lib,programs,source[source.len()-2],source.last(),before.last(),label.0,label.1,owner))}
        else {before}
    }
}

/// Constructed surviving prefixes retain the complete initial authentic
/// history, including earlier episodes. Only new owner lifecycle steps are
/// removed, and all retained landings append their own newly returned receipt.
#[verifier::rlimit(30)]
pub proof fn delete_execution<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        replay::fragment(programs,source,labels),s::registered(source.first().state,owner),source.first().state.control.fibers[owner].provisions.is_empty(),
        source.first().state.control.fibers[owner].phase==Phase::Inactive,
    ensures {
        let target=delete(lib,programs,source,labels,owner);let kept=labels_without(labels,owner);
        &&& g::execution(lib,programs,target,kept) && target.first()==source.first()
        &&& controls(source.last(),target.last(),owner) && g::well_formed(lib,programs,source.last())
        &&& forall|i:int| 0<=i<target.len() ==> g::well_formed(lib,programs,target[i])
        &&& sj::foreign(replay::events(lib,programs,source,labels,owner),p::project(source.first().state,ISet::full())).is_some()
        &&& pi::context_eq(eq)(sj::foreign(replay::events(lib,programs,source,labels,owner),p::project(source.first().state,ISet::full())).unwrap(),p::project(target.last().state,ISet::full()))
    },
    decreases labels.len(),
{
    reveal(delete);reveal(labels_without);
    let target=delete(lib,programs,source,labels,owner);let kept=labels_without(labels,owner);
    if labels.len()==0 {
        assert(source.len()==1);assert(source.first()==source.last());initial_controls(lib,programs,source.first(),owner);
        replay::context_equivalence(eq,lib);
        assert(replay::events(lib,programs,source,labels,owner).len()==0);
        assert(pi::context_eq(eq)(p::project(source.first().state,ISet::full()),p::project(source.first().state,ISet::full())));
    } else {
        let prefix=source.drop_last();let previous=labels.drop_last();let label=labels.last();
        assert(g::execution(lib,programs,prefix,previous));assert(replay::fragment(programs,prefix,previous));
        delete_execution(eq,lib,programs,prefix,previous,owner);
        let before=delete(lib,programs,prefix,previous,owner);let earlier=labels_without(previous,owner);
        assert(prefix.last()==source[source.len()-2]);
        step_replay(eq,lib,programs,prefix,previous,before.last(),source.last(),owner,label.0,label.1);
        ol::configuration_preservation(eq,lib,programs,prefix.last(),source.last(),label.0,label.1);
        let es=replay::events(lib,programs,prefix,previous,owner);
        let e=replay::event(lib,programs,prefix.last(),source.last(),label.0,label.1,owner);
        assert(replay::events(lib,programs,source,labels,owner) =~= es.push(e));
        replay::strict_fragment_recovery(eq,lib,programs,source,labels,owner);
        if keep(label.0,label.1,owner) {
            let out=advance(lib,programs,prefix.last(),source.last(),before.last(),label.0,label.1,owner);
            assert(target==before.push(out));assert(kept==earlier.push(label));
            assert forall|i:int| 0<=i<target.len() implies g::well_formed(lib,programs,target[i]) by {
                if i<before.len() {assert(target[i]==before[i]);} else {assert(i==before.len());assert(target[i]==out);}
            }
            assert(g::execution(lib,programs,target,kept)) by {
                assert forall|i:int| 0<=i<kept.len() implies g::step(lib,programs,target[i],target[i+1],kept[i].0,kept[i].1) by {
                    if i<earlier.len() {assert(target[i]==before[i]);assert(target[i+1]==before[i+1]);}
                    else {assert(i==earlier.len());assert(target[i]==before.last());}
                }
            }
        }
    }
}

pub open spec fn prefix_valid<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,i:int)->bool {
    let prefix=source.take(i+1);let steps=labels.take(i);let target=delete(lib,programs,prefix,steps,owner);
    g::execution(lib,programs,target,labels_without(steps,owner)) && target.first()==source.first() && controls(source[i],target.last(),owner)
}
pub proof fn every_prefix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        replay::fragment(programs,source,labels),s::registered(source.first().state,owner),source.first().state.control.fibers[owner].provisions.is_empty(),
        source.first().state.control.fibers[owner].phase==Phase::Inactive,
    ensures forall|i:int| 0<=i<source.len() ==> #[trigger] prefix_valid(lib,programs,source,labels,owner,i),
{
    assert forall|i:int| 0<=i<source.len() implies #[trigger] prefix_valid(lib,programs,source,labels,owner,i) by {
        let prefix=source.take(i+1);let steps=labels.take(i);
        assert(g::execution(lib,programs,prefix,steps));assert(replay::fragment(programs,prefix,steps));
        assert(prefix.first()==source.first());assert(prefix.last()==source[i]);
        delete_execution(eq,lib,programs,prefix,steps,owner);
    }
}

/// Only actual table Unit/Operation receipts occur in the current fragment.
/// The captured provider must still be the episode-committed resolution.
pub open spec fn pinned<U>(receipt:g::Receipt<U>,a:s::State<U>,actor:usize)->bool {
    match receipt {
        g::Receipt::Table {receipt}=>receipt.actor==actor && match receipt.inverse {
            lift::Inverse::Unit=>true,
            lift::Inverse::Operation {provider,key,..}=>lift::resolve(a,actor,key)==Some(provider),
            _=>false,
        },_=>false,
    }
}
pub open spec fn flat<U>(receipt:g::Receipt<U>)->m::PartialMap<IMap<Port,U>> {
    match receipt {g::Receipt::Table {receipt}=>lift::projected_inverse(receipt),_=>replay::identity()}
}
pub open spec fn receipt_word<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>)->Seq<m::PartialMap<IMap<Port,U>>>
    decreases tokens.len(),
{
    if tokens.len()==0 {Seq::empty()}
    else {seq![flat(history[tokens.last() as int].landed.receipt)]+receipt_word(history,tokens.drop_last())}
}
pub open spec fn pinned_tokens<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)->bool {
    forall|i:int| 0<=i<tokens.len() ==> tokens[i]<history.len() && pinned(#[trigger] history[tokens[i] as int].landed.receipt,a,actor)
}
pub proof fn receipt_word_extensional<U,I>(left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,tokens:Seq<nat>)
    requires forall|i:int| 0<=i<tokens.len() ==> left[tokens[i] as int].landed.receipt==right[tokens[i] as int].landed.receipt,
    ensures receipt_word(left,tokens)==receipt_word(right,tokens),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        assert(left[tokens.last() as int].landed.receipt==right[tokens.last() as int].landed.receipt);
        receipt_word_extensional(left,right,tokens.drop_last());
    }
}
pub proof fn resolution_frame<U>(a:s::State<U>,z:s::State<U>,actor:usize)
    requires s::registered(a,actor),s::registered(z,actor),r::interface_same(a.control.fibers[actor],z.control.fibers[actor]),
        a.control.fibers[actor].committed==z.control.fibers[actor].committed,
    ensures forall|key:Port| #[trigger] lift::resolve(a,actor,key)==lift::resolve(z,actor,key),
{ }

pub proof fn inverse_definedness<U>(receipt:g::Receipt<U>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),s::registered(a,actor),pinned(receipt,a,actor),flat(receipt)(p::project(a,ISet::full())).is_some(),
    ensures g::undo(receipt,a).is_some(),inv::well_formed(g::undo(receipt,a).unwrap()),g::undo(receipt,a).unwrap().control==a.control,
        forall|n:usize| s::registered(a,n) ==> g::undo(receipt,a).unwrap().tables[n].dom()==a.tables[n].dom(),
        p::project(g::undo(receipt,a).unwrap(),ISet::full())==flat(receipt)(p::project(a,ISet::full())).unwrap(),
{
    match receipt {
        g::Receipt::Table {receipt}=>{
            match receipt.inverse {
                lift::Inverse::Operation {provider,key,undo}=>{
                    lift::resolution_sound(a,actor,key);p::unique_owner(a);
                    assert(p::project(a,ISet::full()).dom().contains(key));
                    let actual=choose|n:usize|p::owns(a,key,n);
                    assert(a.control.fibers[actual].provisions.contains(key));assert(actual==provider);
                    p::lookup(a,ISet::full(),key,provider);
                    assert(a.tables[provider].insert(key,undo(a.tables[provider][key]).unwrap()).dom() =~= a.tables[provider].dom());
                },_=>{},
            }
            assert(lift::undo(receipt,a).is_some());lift::undo_preservation(receipt,a);lift::inverse_projects(receipt,a);
        },_=>{},
    }
}

/// A strict projected word's derived domain suffices for the actual full-state
/// LIFO interpreter once actual receipts retain their committed providers.
pub proof fn restore_definedness<U,I>(history:Seq<g::Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),s::registered(a,actor),pinned_tokens(history,tokens,a,actor),
        pi::run(receipt_word(history,tokens),p::project(a,ISet::full())).is_some(),
    ensures g::restore(history,tokens,a,actor).is_some(),inv::well_formed(g::restore(history,tokens,a,actor).unwrap()),
        g::restore(history,tokens,a,actor).unwrap().control==a.control,
        forall|n:usize| s::registered(a,n) ==> g::restore(history,tokens,a,actor).unwrap().tables[n].dom()==a.tables[n].dom(),
        p::project(g::restore(history,tokens,a,actor).unwrap(),ISet::full())==pi::run(receipt_word(history,tokens),p::project(a,ISet::full())).unwrap(),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;
        assert(pinned(receipt,a,actor));
        sj::run_prepend(flat(receipt),receipt_word(history,tokens.drop_last()),p::project(a,ISet::full()));
        inverse_definedness(receipt,a,actor);let next=g::undo(receipt,a).unwrap();
        assert(pinned_tokens(history,tokens.drop_last(),next,actor));
        restore_definedness(history,tokens.drop_last(),next,actor);
        assert forall|n:usize| s::registered(a,n) implies g::restore(history,tokens,a,actor).unwrap().tables[n].dom()==a.tables[n].dom() by {
            assert(s::registered(next,n));
            assert(g::restore(history,tokens.drop_last(),next,actor).unwrap().tables[n].dom()==next.tables[n].dom());
        }
    }
}

/// The journal-to-event correspondence is derived stepwise using source
/// history indices. Existing authentic history is neither erased nor renamed.
pub proof fn journal_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,es:Seq<sj::Event<IMap<Port,U>>>,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),s::registered(a.state,owner),
        g::step(lib,programs,a,z,actor,rule),replay::fragment_step(programs,a,z,actor,rule),
        receipt_word(a.history,a.state.accumulators[owner])==sj::journal(es),pinned_tokens(a.history,a.state.accumulators[owner],a.state,owner),
    ensures s::registered(z.state,owner),pinned_tokens(z.history,z.state.accumulators[owner],z.state,owner),
        receipt_word(z.history,z.state.accumulators[owner])==sj::journal(es.push(replay::event(lib,programs,a,z,actor,rule,owner))),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);source_domains(eq,lib,programs,a,z,actor,rule);
    let old=a.state.accumulators[owner];let new=z.state.accumulators[owner];let e=replay::event(lib,programs,a,z,actor,rule,owner);
    assert(es.push(e).drop_last() =~= es);
    if actor==owner && rule==r::Rule::Begin {
        assert(old.len()==0);assert(sj::journal(es).len()==0);assert(new.len()==0);
    } else {
        assert(a.state.control.fibers[owner].committed==z.state.control.fibers[owner].committed);
        resolution_frame(a.state,z.state,owner);
        assert forall|i:int| 0<=i<old.len() implies a.history[old[i] as int].landed.receipt==z.history[old[i] as int].landed.receipt by {
            assert(old[i]<a.history.len());
        }
        receipt_word_extensional(a.history,z.history,old);
        assert forall|i:int| 0<=i<old.len() implies old[i]<z.history.len() && pinned(#[trigger] z.history[old[i] as int].landed.receipt,z.state,owner) by {
            assert(pinned(a.history[old[i] as int].landed.receipt,a.state,owner));
            match a.history[old[i] as int].landed.receipt {
                g::Receipt::Table {receipt}=>{match receipt.inverse {lift::Inverse::Operation {key,..}=>{assert(lift::resolve(a.state,owner,key)==lift::resolve(z.state,owner,key));},_=>{}}},_=>{},
            }
        }
        if g::landing(a,z,rule) && actor==owner {
            let node=replay::dependent(programs(actor)(a.current[actor].unwrap()));let call=g::entry(lib,programs,a,actor);
            operation_domains(lib,node,a.state,actor);
            assert(new==old.push(a.history.len()));assert(new.drop_last() =~= old);
            assert(z.history[new.last() as int]==call);
            assert(pinned(call.landed.receipt,z.state,owner)) by {
                match node {crate::dependent_grammar::Node::Operation {operation,..}=>{
                    let key=(lib.key)(operation);assert(lift::resolve(a.state,owner,key)==lift::resolve(z.state,owner,key));
                },_=>{},}
            }
            assert(flat(call.landed.receipt)==e.inverse);
            assert forall|i:int| 0<=i<new.len() implies new[i]<z.history.len() && pinned(#[trigger] z.history[new[i] as int].landed.receipt,z.state,owner) by {
                if i<old.len() {assert(new[i]==old[i]);} else {assert(i==old.len());}
            }
        } else {assert(new==old);assert(!e.own);}
    }
}

pub proof fn actual_journal<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        replay::fragment(programs,source,labels),s::registered(source.first().state,owner),source.first().state.control.fibers[owner].phase==Phase::Inactive,
    ensures {
        let last=source.last();
        &&& g::well_formed(lib,programs,last) && s::registered(last.state,owner)
        &&& pinned_tokens(last.history,last.state.accumulators[owner],last.state,owner)
        &&& receipt_word(last.history,last.state.accumulators[owner])==sj::journal(replay::events(lib,programs,source,labels,owner))
    },
    decreases labels.len(),
{
    if labels.len()==0 {assert(source.first()==source.last());assert(source.first().state.accumulators[owner].len()==0);}
    else {
        let prefix=source.drop_last();let previous=labels.drop_last();let label=labels.last();
        assert(g::execution(lib,programs,prefix,previous));assert(replay::fragment(programs,prefix,previous));
        actual_journal(eq,lib,programs,prefix,previous,owner);
        let es=replay::events(lib,programs,prefix,previous,owner);let e=replay::event(lib,programs,prefix.last(),source.last(),label.0,label.1,owner);
        journal_step(eq,lib,programs,prefix.last(),source.last(),es,owner,label.0,label.1);
        ol::configuration_preservation(eq,lib,programs,prefix.last(),source.last(),label.0,label.1);
        assert(replay::events(lib,programs,source,labels,owner) =~= es.push(e));
    }
}

/// The final own Unload is constructed and proved enabled, rather than
/// requiring an already-successful restoration or legal erased trace.
pub proof fn terminal_deletion<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),
        replay::fragment(programs,source,labels),s::registered(source.first().state,owner),source.first().state.control.fibers[owner].provisions.is_empty(),
        source.first().state.control.fibers[owner].phase==Phase::Inactive,source.last().state.control.fibers[owner].phase==Phase::Unloading,
    ensures {
        let last=source.last();let terminal=g::unload(last,owner);let target=delete(lib,programs,source,labels,owner);
        &&& g::restore(last.history,last.state.accumulators[owner],last.state,owner).is_some()
        &&& g::step(lib,programs,last,terminal,owner,r::Rule::Unload) && g::well_formed(lib,programs,terminal)
        &&& g::execution(lib,programs,source.push(terminal),labels.push((owner,r::Rule::Unload)))
        &&& g::execution(lib,programs,target,labels_without(labels,owner)) && target.first()==source.first()
        &&& controls(terminal,target.last(),owner) && terminal.state.control==target.last().state.control
        &&& pi::context_eq(eq)(p::project(terminal.state,ISet::full()),p::project(target.last().state,ISet::full()))
    },
{
    delete_execution(eq,lib,programs,source,labels,owner);actual_journal(eq,lib,programs,source,labels,owner);
    replay::strict_fragment_recovery(eq,lib,programs,source,labels,owner);replay::context_equivalence(eq,lib);
    let last=source.last();let target=delete(lib,programs,source,labels,owner);let out=target.last();
    restore_definedness(last.history,last.state.accumulators[owner],last.state,owner);
    assert(!r::relied(last.state.control,owner)) by {
        if r::relied(last.state.control,owner) {
            let (n,b)=choose|n:usize,b:Binding| s::registered(last.state,n) && n!=owner && last.state.control.fibers[n].phase!=Phase::Inactive
                && last.state.control.fibers[n].committed.contains(b) && b.provider==owner;
            let key=Port {key:b.key,realm:b.realm};assert(last.state.control.fibers[owner].provisions.contains(key));
        }
    }
    let terminal=g::unload(last,owner);assert(g::step(lib,programs,last,terminal,owner,r::Rule::Unload));
    ol::configuration_preservation(eq,lib,programs,last,terminal,owner,r::Rule::Unload);
    let restored=g::restore(last.history,last.state.accumulators[owner],last.state,owner).unwrap();
    p::unique_owner(restored);p::lifecycle_edit(restored,owner,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
    assert(controls(last,out,owner));
    assert forall|n:usize| terminal.state.control.fibers.dom().contains(n) implies #[trigger] terminal.state.control.fibers[n]==out.state.control.fibers[n] by {
        assert(s::registered(last.state,n));
        if n==owner {
            assert(r::interface_same(last.state.control.fibers[owner],out.state.control.fibers[owner]));
            assert(terminal.state.control.fibers[n].committed =~= out.state.control.fibers[n].committed);
        } else {assert(last.state.control.fibers[n]==out.state.control.fibers[n]);}
    }
    assert(terminal.state.control.fibers.dom() =~= last.state.control.fibers.dom());
    assert(terminal.state.control.fibers.dom()==out.state.control.fibers.dom());
    assert(terminal.state.control.fibers =~= out.state.control.fibers);
    assert(terminal.state.control==out.state.control);
    assert forall|n:usize| s::registered(terminal.state,n) implies {
        &&& terminal.state.tables[n].dom()==out.state.tables[n].dom()
        &&& (n!=owner ==> terminal.state.control.fibers[n]==out.state.control.fibers[n] && terminal.current[n]==out.current[n])
    } by {
        assert(s::registered(last.state,n));
        assert(terminal.state.tables[n].dom()==last.state.tables[n].dom());
    }
    assert(g::execution(lib,programs,source.push(terminal),labels.push((owner,r::Rule::Unload)))) by {
        assert forall|i:int| 0<=i<labels.push((owner,r::Rule::Unload)).len() implies g::step(lib,programs,source.push(terminal)[i],source.push(terminal)[i+1],labels.push((owner,r::Rule::Unload))[i].0,labels.push((owner,r::Rule::Unload))[i].1) by {
            if i<labels.len() {assert(source.push(terminal)[i+1]==source[i+1]);} else {assert(i==labels.len());}
        }
    }
}

pub open spec fn example_shift(amount:int)->m::PartialMap<int> {|v:int|Some(v+amount)}
pub proof fn example_generator(amount:int,f:m::PartialMap<int>)
    requires pi::value_generators(ex::translation(amount)).contains(f),
    ensures f==example_shift(amount) || f==example_shift(-amount),
{
    if f==pi::value_forward(ex::translation(amount)) {assert(f =~= example_shift(amount));}
    else {
        let v=choose|v:int| #[trigger] ex::translation(amount)(v).is_some() && ex::translation(amount)(v).unwrap().undo==f;
        assert(f =~= example_shift(-amount));
    }
}
/// The interface has a nonempty, total family of actual addition operations.
/// Constant outcomes are stable; captured subtraction closures are independent
/// of the hidden input representative and are genuinely returned by each call.
pub proof fn example_interface()
    ensures og::primitive_theory(ex::equality(),ex::library()),replay::interface(ex::equality(),ex::library()),
{
    ex::primitive_theory();og::exact_theory(ex::equality(),ex::library());
    assert forall|a:Port,b:Port,x:int,y:int| #![trigger (ex::library().apply)(a,x),(ex::library().apply)(b,y)]
        ex::library().allowed.contains(a) && ex::library().allowed.contains(b) && (ex::library().arguments)(a,x) && (ex::library().arguments)(b,y)
        && (ex::library().key)(a)==(ex::library().key)(b)
        implies pi::value_independent(|u:int,v:int|ex::equality()((ex::library().key)(a),u,v),(ex::library().apply)(a,x),(ex::library().apply)(b,y)) by {
        let eq=|u:int,v:int|ex::equality()(a,u,v);
        assert forall|f:m::PartialMap<int>,h:m::PartialMap<int>| pi::value_generators(ex::translation(x)).contains(f) && pi::value_generators(ex::translation(y)).contains(h)
            implies #[trigger] pi::commutes(eq,f,h) by {
            example_generator(x,f);example_generator(y,h);
            assert forall|v:int| #[trigger] pi::optional_equal(eq,pi::compose(f,h)(v),pi::compose(h,f)(v)) by {}
        }
        assert forall|h:m::PartialMap<int>| pi::value_generators(ex::translation(y)).contains(h) implies #[trigger] pi::value_stable(eq,ex::translation(x),h) by {
            assert forall|v:int| #[trigger] h(v).is_some() implies {
                &&& ex::translation(x)(v).is_some()==ex::translation(x)(h(v).unwrap()).is_some()
                &&& ex::translation(x)(v).is_some() ==> ex::translation(x)(v).unwrap().outcome==ex::translation(x)(h(v).unwrap()).unwrap().outcome
                    && m::partial_related(eq,ex::translation(x)(v).unwrap().undo,ex::translation(x)(h(v).unwrap()).unwrap().undo)
            } by {}
        }
        assert forall|f:m::PartialMap<int>| pi::value_generators(ex::translation(x)).contains(f) implies #[trigger] pi::value_stable(eq,ex::translation(y),f) by {
            assert forall|v:int| #[trigger] f(v).is_some() implies {
                &&& ex::translation(y)(v).is_some()==ex::translation(y)(f(v).unwrap()).is_some()
                &&& ex::translation(y)(v).is_some() ==> ex::translation(y)(v).unwrap().outcome==ex::translation(y)(f(v).unwrap()).unwrap().outcome
                    && m::partial_related(eq,ex::translation(y)(v).unwrap().undo,ex::translation(y)(f(v).unwrap()).unwrap().undo)
            } by {}
        }
    }
}
pub open spec fn example_programs()->g::Programs<Port,int,int,(),bool> {
    |actor:usize| |shift:bool|if !shift {
        g::Node::Dependent {node:d::Node::Provision {key:ex::key(0),value:10,next:None}}
    } else {g::Node::Dependent {node:d::Node::Operation {operation:ex::key(0),argument:if actor==1 {5}else{7},select:|_:()|None}}}
}
pub open spec fn example_view()->ISet<Binding> {ISet::empty().insert(Binding {key:0,realm:0,provider:0})}
pub proof fn example_target(a:s::State<int>,actor:usize)
    requires s::registered(a,actor),!a.control.fibers[actor].retired,a.control.fibers[actor].dependencies==ex::provided(0),
        s::publishes(a,ex::key(0),0),
    ensures s::target(a,actor,example_view()),
{
    assert forall|key:Port| a.control.fibers[actor].dependencies.contains(key) implies exists|b:Binding| example_view().contains(b) && b.key==key.key && b.realm==key.realm by {
        assert(key==ex::key(0));let b=Binding {key:0,realm:0,provider:0};assert(example_view().contains(b));
    }
}
#[verifier::opaque]
pub open spec fn example_trace()->Seq<g::Configuration<int,bool>> {
    let a0=g::empty::<int,bool>();let a1=t::insert(a0,0,None,ISet::empty(),ex::provided(0),false);
    let a2=t::insert(a1,1,None,ex::provided(0),ISet::empty(),true);
    let a3=t::insert(a2,2,None,ex::provided(0),ISet::empty(),true);
    let a4=g::edit(a3,0,Phase::Loading,ISet::empty(),Some(false),Seq::empty());
    let initial=g::land(ex::library(),example_programs(),a4,0,Phase::Active);
    let a5=g::edit(initial,1,Phase::Loading,example_view(),Some(true),Seq::empty());
    let a6=g::land(ex::library(),example_programs(),a5,1,Phase::Active);
    let a7=g::edit(a6,2,Phase::Loading,example_view(),Some(true),Seq::empty());
    let a8=g::land(ex::library(),example_programs(),a7,2,Phase::Active);
    let a9=retire(a8,1);
    let a10=g::edit(a9,1,Phase::Unloading,example_view(),None,a9.state.accumulators[1usize]);
    seq![initial,a5,a6,a7,a8,a9,a10]
}
pub open spec fn example_labels()->Seq<(usize,r::Rule)> {
    seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Finish),(2usize,r::Rule::Begin),(2usize,r::Rule::Finish),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave)]
}
#[verifier::rlimit(30)]
pub proof fn example_execution()
    ensures g::execution(ex::library(),example_programs(),example_trace(),example_labels()),
        g::well_formed(ex::library(),example_programs(),example_trace().first()),
        replay::fragment(example_programs(),example_trace(),example_labels()),
        s::registered(example_trace().first().state,1),example_trace().first().state.control.fibers[1usize].phase==Phase::Inactive,
        example_trace().first().state.control.fibers[1usize].provisions.is_empty(),example_trace().last().state.control.fibers[1usize].phase==Phase::Unloading,
        example_trace().first().history.len()==1,example_trace().last().history.len()==3,
        example_trace().last().state.tables[0usize][ex::key(0)]==22,
        example_trace().last().state.accumulators[1usize]==seq![1nat],
        example_trace().last().state.accumulators[2usize]==seq![2nat],
        p::owns(example_trace().first().state,ex::key(0),0),p::owns(example_trace().last().state,ex::key(0),0),
{
    reveal(example_trace);example_interface();let lib=ex::library();let programs=example_programs();
    syntax::constructor_member(lib,programs,0,ex::provided(0),ex::provided(0),false);
    syntax::constructor_member(lib,programs,1,ex::provided(0),ISet::empty(),true);
    syntax::constructor_member(lib,programs,2,ex::provided(0),ISet::empty(),true);
    assert(ISet::<Port>::empty().union(ex::provided(0)) =~= ex::provided(0));
    assert(ex::provided(0).union(ISet::empty()) =~= ex::provided(0));
    let a0=g::empty::<int,bool>();let a1=t::insert(a0,0,None,ISet::empty(),ex::provided(0),false);
    let a2=t::insert(a1,1,None,ex::provided(0),ISet::empty(),true);let a3=t::insert(a2,2,None,ex::provided(0),ISet::empty(),true);
    g::empty_well_formed(lib,programs);t::insertion_step(lib,programs,a0,0,None,ISet::empty(),ex::provided(0),false);
    ol::configuration_preservation(ex::equality(),lib,programs,a0,a1,0,r::Rule::Insert);
    t::insertion_step(lib,programs,a1,1,None,ex::provided(0),ISet::empty(),true);
    ol::configuration_preservation(ex::equality(),lib,programs,a1,a2,1,r::Rule::Insert);
    t::insertion_step(lib,programs,a2,2,None,ex::provided(0),ISet::empty(),true);
    ol::configuration_preservation(ex::equality(),lib,programs,a2,a3,2,r::Rule::Insert);
    let a4=g::edit(a3,0,Phase::Loading,ISet::empty(),Some(false),Seq::empty());
    assert(g::step(lib,programs,a3,a4,0,r::Rule::Begin));ol::configuration_preservation(ex::equality(),lib,programs,a3,a4,0,r::Rule::Begin);
    let states=example_trace();assert(g::step(lib,programs,a4,states[0],0,r::Rule::Finish));
    ol::configuration_preservation(ex::equality(),lib,programs,a4,states[0],0,r::Rule::Finish);
    example_target(states[0].state,1);
    assert(g::step(lib,programs,states[0],states[1],1,r::Rule::Begin));
    example_target(states[1].state,1);
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    assert(states[1].state.control.fibers[1usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[1].state.control.fibers[1usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[1].state,1,ex::key(0))==Some(0usize));
    assert(g::run(lib,programs(1)(true),states[1].state,1).is_some());
    assert(g::step(lib,programs,states[1],states[2],1,r::Rule::Finish));
    example_target(states[2].state,2);
    assert(g::step(lib,programs,states[2],states[3],2,r::Rule::Begin));
    example_target(states[3].state,2);
    assert(states[3].state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[3].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[3].state,2,ex::key(0))==Some(0usize));
    assert(g::run(lib,programs(2)(true),states[3].state,2).is_some());
    assert(g::step(lib,programs,states[3],states[4],2,r::Rule::Finish));
    ch::concrete_child_retirement(states[4].state,1);assert(g::step(lib,programs,states[4],states[5],1,r::Rule::Retire));
    assert(g::step(lib,programs,states[5],states[6],1,r::Rule::Leave));
    assert forall|i:int| 0<=i<example_labels().len() implies g::step(lib,programs,states[i],states[i+1],example_labels()[i].0,example_labels()[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else {assert(i==5);}
    }
    assert forall|i:int| 0<=i<example_labels().len() implies replay::fragment_step(programs,states[i],states[i+1],example_labels()[i].0,example_labels()[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else {assert(i==5);}
    }
}

// Compute the concrete forward construction separately from the general
// deletion theorem and from the owner's inverse application.
proof fn example_target_values()
    ensures {
        let source=example_trace();let target=delete(ex::library(),example_programs(),source,example_labels(),1);
        &&& target.first().history.len()==1 && target.last().history.len()==2
        &&& target.last().history[0]==source.first().history[0]
        &&& target.last().state.accumulators[2usize]==seq![1nat]
        &&& source.last().state.accumulators[2usize]==seq![2nat]
        &&& p::owns(target.last().state,ex::key(0),0)
        &&& target.last().state.tables[0usize][ex::key(0)]==17
        &&& target.last().state.control.fibers[1usize].retired && target.last().state.control.fibers[1usize].phase==Phase::Inactive
    },
{
    hide(g::step);hide(replay::fragment);
    example_execution();
    reveal(example_trace);reveal_with_fuel(delete,7);reveal_with_fuel(labels_without,7);
    let source=example_trace();let target=delete(ex::library(),example_programs(),source,example_labels(),1);
    let binding=Binding {key:0,realm:0,provider:0};
    assert(lift::names_key(binding,ex::key(0)));
    assert(target[1].state.control.fibers[2usize].committed.contains(binding));
    assert(exists|b:Binding| target[1].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(target[1].state,2,ex::key(0))==Some(0usize));
    assert(g::run(ex::library(),example_programs()(2)(true),target[1].state,2).is_some());
    assert(target.last().state.accumulators[2usize] =~= seq![1nat]);assert(source.last().state.accumulators[2usize] =~= seq![2nat]);
    assert(target.first().history.len()==1 && target.last().history.len()==2);
    assert(target.last().history[0]==source.first().history[0]);
    assert(p::owns(target.last().state,ex::key(0),0));
    assert(target.last().state.tables[0usize][ex::key(0)]==17);
    assert(target.last().state.control.fibers[1usize].retired && target.last().state.control.fibers[1usize].phase==Phase::Inactive);
}
/// Both actors write the same committed provider cell. The initial Provision
/// remains authentic history entry zero; the foreign call is re-executed on 10
/// instead of 15, mints target token one and yields 17 at the closed endpoint.
#[verifier::rlimit(30)]
pub proof fn actual_shared_terminal()
    ensures {
        let source=example_trace();let target=delete(ex::library(),example_programs(),source,example_labels(),1);let final_source=g::unload(source.last(),1);
        &&& g::execution(ex::library(),example_programs(),target,labels_without(example_labels(),1))
        &&& g::step(ex::library(),example_programs(),source.last(),final_source,1,r::Rule::Unload)
        &&& target.first().history.len()==1 && target.last().history.len()==2
        &&& target.last().history[0]==source.first().history[0]
        &&& target.last().state.accumulators[2usize]==seq![1nat]
        &&& source.last().state.accumulators[2usize]==seq![2nat]
        &&& final_source.state.tables[0usize][ex::key(0)]==17 && target.last().state.tables[0usize][ex::key(0)]==17
        &&& target.last().state.control.fibers[1usize].retired && target.last().state.control.fibers[1usize].phase==Phase::Inactive
    },
{
    hide(g::step);hide(og::primitive_theory);
    hide(delete);hide(labels_without);hide(g::unload);
    example_execution();example_interface();
    delete_execution(ex::equality(),ex::library(),example_programs(),example_trace(),example_labels(),1);
    terminal_deletion(ex::equality(),ex::library(),example_programs(),example_trace(),example_labels(),1);
    example_target_values();
    // Recover the concrete terminal value from the proved projected equality.
    let source=example_trace();let target=delete(ex::library(),example_programs(),source,example_labels(),1);
    let terminal=g::unload(source.last(),1);let key=ex::key(0);
    p::unique_owner(terminal.state);p::unique_owner(target.last().state);
    assert(p::owns(terminal.state,key,0));
    p::lookup(terminal.state,ISet::full(),key,0);
    p::lookup(target.last().state,ISet::full(),key,0);
}

} // verus!
