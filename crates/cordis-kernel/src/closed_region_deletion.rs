//! Source-driven deletion of a dependency-closed region of episodes.
//! Dormant roots retain their registrations; born names are erased. Consumers
//! of erased publications belong to the same region. Surviving receipts retain
//! their original partial inverses, with compressed history indices.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, dependent_lift as dep, grammar_lift as lift,
    mixed_grammar as g, mixed_syntax as syntax, preservation as inv, projection as p,
    refinement as r, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;
verus! {
pub struct Region { pub episodes:ISet<usize>, pub born:ISet<usize> }
impl Region {
    pub open spec fn wf(self)->bool { self.born.subset_of(self.episodes) }
    pub open spec fn keep(self,actor:usize,rule:r::Rule)->bool {
        !self.born.contains(actor) && (!self.episodes.contains(actor)
            || rule==r::Rule::Insert || rule==r::Rule::Retire || rule==r::Rule::Remove)
    }
}
pub open spec fn retain<T>(map:IMap<usize,T>,region:Region)->IMap<usize,T> {
    IMap::new(|n:usize|map.dom().contains(n) && !region.born.contains(n),|n:usize|map[n])
}
pub open spec fn fiber(f:r::Fiber,n:usize,region:Region)->r::Fiber {
    if region.episodes.contains(n) {r::Fiber {phase:Phase::Inactive,committed:ISet::empty(),..f}} else {f}
}
pub open spec fn tokens(xs:Seq<nat>,rho:spec_fn(nat)->nat)->Seq<nat> {xs.map(|_:int,t:nat|rho(t))}
pub open spec fn state<U>(a:s::State<U>,region:Region,rho:spec_fn(nat)->nat)->s::State<U> {
    s::State {
        control:r::State {fibers:IMap::new(|n:usize|s::registered(a,n) && !region.born.contains(n),|n:usize|fiber(a.control.fibers[n],n,region))},
        tables:IMap::new(|n:usize|s::registered(a,n) && !region.born.contains(n),|n:usize|if region.episodes.contains(n) {IMap::empty()} else {a.tables[n]}),
        effects:retain(a.effects,region),
        iterators:IMap::new(|n:usize|s::registered(a,n) && !region.born.contains(n),|n:usize|if region.episodes.contains(n) {None} else {a.iterators[n]}),
        accumulators:IMap::new(|n:usize|s::registered(a,n) && !region.born.contains(n),|n:usize|if region.episodes.contains(n) {Seq::empty()} else {tokens(a.accumulators[n],rho)}),
    }
}
/// Source-only closure: no surviving admission reads a removed publication,
/// and no retained registration names an erased parent.
pub open spec fn closed<U>(a:s::State<U>,region:Region)->bool {
    &&& region.wf()
    &&& forall|n:usize|s::registered(a,n) && !region.born.contains(n) && a.control.fibers[n].parent.is_some()
        ==> !region.born.contains(a.control.fibers[n].parent.unwrap())
    &&& forall|n:usize,m:usize|s::registered(a,n) && s::registered(a,m) && !region.episodes.contains(n) && region.episodes.contains(m)
        ==> a.control.fibers[n].dependencies.disjoint(a.control.fibers[m].provisions)
}
/// A receipt's actual captured footprint, not the current provider target.
pub open spec fn local<U>(receipt:g::Receipt<U>,region:Region)->bool {
    let own=region.episodes.contains(g::owner(receipt));
    match receipt {
        g::Receipt::Table {receipt}=>match receipt.inverse {
            lift::Inverse::Operation {provider,..}=>region.episodes.contains(provider)==own,
            _=>true,
        },
        g::Receipt::Child {child,..}=>region.born.contains(child)==own,
    }
}
pub open spec fn local_history<U,I>(h:Seq<g::Entry<U,I>>,region:Region)->bool {
    forall|i:int|0<=i<h.len() ==> local(h[i].landed.receipt,region)
}
pub open spec fn index<U,I>(h:Seq<g::Entry<U,I>>,region:Region,t:nat)->nat
    decreases t,
{if t==0 {0} else {index(h,region,(t-1) as nat)+if region.episodes.contains(g::owner(h[t as int-1].landed.receipt)) {0nat} else {1nat}}}
pub open spec fn prefix<T>(a:Seq<T>,b:Seq<T>)->bool {a.len()<=b.len() && forall|i:int|0<=i<a.len() ==> a[i]==b[i]}
pub proof fn index_prefix<U,I>(a:Seq<g::Entry<U,I>>,b:Seq<g::Entry<U,I>>,region:Region,t:nat)
    requires prefix(a,b),t<=a.len(), ensures index(a,region,t)==index(b,region,t), decreases t,
{if t>0 {index_prefix(a,b,region,(t-1) as nat);}}
pub open spec fn entry<U,I>(e:g::Entry<U,I>,region:Region,rho:spec_fn(nat)->nat)->g::Entry<U,I> {
    g::Entry {input:state(e.input,region,rho),iterator:e.iterator,landed:g::Landed {state:state(e.landed.state,region,rho),..e.landed}}
}
pub open spec fn history<U,I>(h:Seq<g::Entry<U,I>>,region:Region,rho:spec_fn(nat)->nat)->Seq<g::Entry<U,I>>
    decreases h.len(),
{if h.len()==0 {Seq::empty()} else {
    let before=history(h.drop_last(),region,rho);
    if region.episodes.contains(g::owner(h.last().landed.receipt)) {before} else {before.push(entry(h.last(),region,rho))}
}}
pub proof fn history_push<U,I>(h:Seq<g::Entry<U,I>>,e:g::Entry<U,I>,region:Region,rho:spec_fn(nat)->nat)
    ensures history(h.push(e),region,rho)==if region.episodes.contains(g::owner(e.landed.receipt)) {history(h,region,rho)} else {history(h,region,rho).push(entry(e,region,rho))},
{assert(h.push(e).drop_last() =~= h);}
pub proof fn history_indices<U,I>(h:Seq<g::Entry<U,I>>,region:Region,rho:spec_fn(nat)->nat)
    ensures history(h,region,rho).len()==index(h,region,h.len()),
        forall|i:int|0<=i<h.len() && !region.episodes.contains(g::owner(h[i].landed.receipt)) ==>
            index(h,region,i as nat)<history(h,region,rho).len()
            && history(h,region,rho)[index(h,region,i as nat) as int]==entry(h[i],region,rho),
    decreases h.len(),
{
    if h.len()>0 {
        let before=h.drop_last();history_indices(before,region,rho);
        assert(prefix(before,h));index_prefix(before,h,region,before.len());
        assert forall|i:int|0<=i<h.len() && !region.episodes.contains(g::owner(h[i].landed.receipt)) implies
            index(h,region,i as nat)<history(h,region,rho).len()
            && history(h,region,rho)[index(h,region,i as nat) as int]==entry(h[i],region,rho) by {
            if i<before.len() {index_prefix(before,h,region,i as nat);} else {assert(i==before.len());}
        }
    }
}
pub open spec fn configuration<U,I>(a:g::Configuration<U,I>,region:Region,rho:spec_fn(nat)->nat)->g::Configuration<U,I> {
    g::Configuration {state:state(a.state,region,rho),roots:retain(a.roots,region),
        current:IMap::new(|n:usize|a.current.dom().contains(n) && !region.born.contains(n),|n:usize|if region.episodes.contains(n) {None} else {a.current[n]}),
        history:history(a.history,region,rho)}
}
pub proof fn update<U>(a:s::State<U>,region:Region,rho:spec_fn(nat)->nat,owner:usize,key:Port,value:Option<U>)
    requires s::registered(a,owner),
    ensures region.episodes.contains(owner) ==> state(p::update_slot(a,owner,key,value),region,rho)==state(a,region,rho),
        !region.episodes.contains(owner) && region.wf() ==> state(p::update_slot(a,owner,key,value),region,rho)==p::update_slot(state(a,region,rho),owner,key,value),
{
    if region.episodes.contains(owner) || region.wf() {
        let left=state(p::update_slot(a,owner,key,value),region,rho);
        let right=if region.episodes.contains(owner) {state(a,region,rho)} else {p::update_slot(state(a,region,rho),owner,key,value)};
        assert(left.control.fibers =~= right.control.fibers);assert(left.tables =~= right.tables);assert(left.effects =~= right.effects);
        assert(left.iterators =~= right.iterators);assert(left.accumulators =~= right.accumulators);
    }
}
pub proof fn edit<U>(a:s::State<U>,region:Region,rho:spec_fn(nat)->nat,actor:usize,phase:Phase,view:ISet<Binding>,next:Option<nat>,stack:Seq<nat>)
    requires region.wf(),s::registered(a,actor),
    ensures region.episodes.contains(actor) ==> state(s::edit(a,actor,phase,view,next,stack),region,rho)==state(a,region,rho),
        !region.episodes.contains(actor) ==> state(s::edit(a,actor,phase,view,next,stack),region,rho)==s::edit(state(a,region,rho),actor,phase,view,next,tokens(stack,rho)),
{
    let left=state(s::edit(a,actor,phase,view,next,stack),region,rho);
    let right=if region.episodes.contains(actor) {state(a,region,rho)} else {s::edit(state(a,region,rho),actor,phase,view,next,tokens(stack,rho))};
    assert(left.control.fibers =~= right.control.fibers);assert(left.tables =~= right.tables);assert(left.effects =~= right.effects);assert(left.iterators =~= right.iterators);assert(left.accumulators =~= right.accumulators);
}
pub proof fn targets<U>(a:s::State<U>,region:Region,rho:spec_fn(nat)->nat,actor:usize,view:ISet<Binding>)
    requires inv::well_formed(a),closed(a,region),s::registered(a,actor),!region.episodes.contains(actor),
    ensures s::target(a,actor,view)==s::target(state(a,region,rho),actor,view),
        s::coherent(a,actor)==s::coherent(state(a,region,rho),actor),
{
    assert forall|key:Port,n:usize|a.control.fibers[actor].dependencies.contains(key) implies
        s::publishes(a,key,n)==s::publishes(state(a,region,rho),key,n) by {
        if s::registered(a,n) && region.episodes.contains(n) {
            assert(a.control.fibers[actor].dependencies.disjoint(a.control.fibers[n].provisions));
        }
    }
}
/// Actual partial inverses transport, or stutter inside the removed region.
/// No success in the constructed execution is a premise.
pub proof fn undo<U>(a:s::State<U>,receipt:g::Receipt<U>,region:Region,rho:spec_fn(nat)->nat)
    requires region.wf(),local(receipt,region),g::undo(receipt,a).is_some(),
    ensures region.episodes.contains(g::owner(receipt)) ==> state(g::undo(receipt,a).unwrap(),region,rho)==state(a,region,rho),
        !region.episodes.contains(g::owner(receipt)) ==> g::undo(receipt,state(a,region,rho)).is_some()
            && g::undo(receipt,state(a,region,rho)).unwrap()==state(g::undo(receipt,a).unwrap(),region,rho),
{
    match receipt {
        g::Receipt::Table {receipt}=>match receipt.inverse {
            lift::Inverse::Operation {provider,key,undo}=>{
                if !region.episodes.contains(receipt.actor) {assert(lift::resolve(a,receipt.actor,key)==lift::resolve(state(a,region,rho),receipt.actor,key));}
                update(a,region,rho,provider,key,Some(undo(a.tables[provider][key]).unwrap()));
            },
            lift::Inverse::Provision {key}=>{update(a,region,rho,receipt.actor,key,None);},
            _=>{},
        },
        g::Receipt::Child {child,..}=>{
            if region.born.contains(child) {assert(state(g::undo(receipt,a).unwrap(),region,rho).control.fibers =~= state(a,region,rho).control.fibers);}
            else {assert(state(g::undo(receipt,a).unwrap(),region,rho).control.fibers =~= g::undo(receipt,state(a,region,rho)).unwrap().control.fibers);}
            let left=state(g::undo(receipt,a).unwrap(),region,rho);
            let right=if region.episodes.contains(g::owner(receipt)) {state(a,region,rho)} else {g::undo(receipt,state(a,region,rho)).unwrap()};
            assert(left.tables =~= right.tables);assert(left.effects =~= right.effects);assert(left.iterators =~= right.iterators);assert(left.accumulators =~= right.accumulators);
        },
    }
}
pub proof fn restore<U,I>(h:Seq<g::Entry<U,I>>,stack:Seq<nat>,a:s::State<U>,actor:usize,region:Region,rho:spec_fn(nat)->nat)
    requires region.wf(),local_history(h,region),g::restore(h,stack,a,actor).is_some(),
        forall|t:nat|t<h.len() ==> rho(t)==index(h,region,t),
    ensures region.episodes.contains(actor) ==> state(g::restore(h,stack,a,actor).unwrap(),region,rho)==state(a,region,rho),
        !region.episodes.contains(actor) ==> g::restore(history(h,region,rho),tokens(stack,rho),state(a,region,rho),actor).is_some()
            && g::restore(history(h,region,rho),tokens(stack,rho),state(a,region,rho),actor).unwrap()==state(g::restore(h,stack,a,actor).unwrap(),region,rho),
    decreases stack.len(),
{
    if stack.len()>0 {
        let t=stack.last();let receipt=h[t as int].landed.receipt;
        undo(a,receipt,region,rho);restore(h,stack.drop_last(),g::undo(receipt,a).unwrap(),actor,region,rho);
        if !region.episodes.contains(actor) {
            history_indices(h,region,rho);assert(tokens(stack,rho).last()==rho(t));
            assert(tokens(stack,rho).drop_last() =~= tokens(stack.drop_last(),rho));
        }
    }
}
/// The original call's captured provider and Child identity discharge these
/// laws. The callback sees the same value, so it returns the same inverse and
/// continuation, including value-dependent continuations.
pub proof fn run<A,X,U,B,I>(lib:g::Library<A,X,U,B>,node:g::Node<A,X,U,B,I>,a:s::State<U>,actor:usize,region:Region,rho:spec_fn(nat)->nat)
    requires region.wf(),g::run(lib,node,a,actor).is_some(),local(g::run(lib,node,a,actor).unwrap().receipt,region),
        !region.episodes.contains(actor) && matches!(node,g::Node::Child {..}) ==> !region.born.contains(actor),
    ensures g::owner(g::run(lib,node,a,actor).unwrap().receipt)==actor,s::registered(g::run(lib,node,a,actor).unwrap().state,actor),
        region.episodes.contains(actor) ==> state(g::run(lib,node,a,actor).unwrap().state,region,rho)==state(a,region,rho),
        !region.episodes.contains(actor) ==> g::run(lib,node,state(a,region,rho),actor).is_some()
            && g::run(lib,node,state(a,region,rho),actor).unwrap()==(g::Landed {state:state(g::run(lib,node,a,actor).unwrap().state,region,rho),..g::run(lib,node,a,actor).unwrap()}),
{
    let old=g::run(lib,node,a,actor).unwrap();let left=state(old.state,region,rho);let start=state(a,region,rho);
    match node {
        g::Node::Dependent {node}=>match node {
            d::Node::Operation {operation,argument,..}=>{
                let key=(lib.key)(operation);let provider=lift::resolve(a,actor,key).unwrap();
                if !region.episodes.contains(actor) {assert(lift::resolve(a,actor,key)==lift::resolve(start,actor,key));}
                update(a,region,rho,provider,key,Some((lib.apply)(operation,argument)(a.tables[provider][key]).unwrap().value));
            },
            d::Node::Provision {key,value,..}=>{update(a,region,rho,actor,key,Some(value));},
            _=>{},
        },
        g::Node::Child {child,dependencies,provisions,root,next}=>{
            let right=if region.episodes.contains(actor) {start} else {g::create(start,actor,child,dependencies,provisions)};
            if !region.episodes.contains(actor) {
                assert(r::frame(start.control,right.control,child));
                assert(r::step(start.control,right.control,child,r::Rule::Insert));
            }
            assert(left.control.fibers =~= right.control.fibers);assert(left.tables =~= right.tables);
            assert(left.effects =~= right.effects);assert(left.iterators =~= right.iterators);
            assert(tokens(Seq::<nat>::empty(),rho) =~= Seq::<nat>::empty());assert(left.accumulators =~= right.accumulators);
        },
    }
}
}

#[path = "closed_region_example.rs"]
pub mod example;
#[path = "closed_region_execution.rs"]
pub mod execution;
#[path = "closed_region_trace.rs"]
pub mod trace;

#[path = "closed_region_fresh.rs"]
pub mod fresh;
#[path = "closed_region_fresh_trace.rs"]
pub mod fresh_trace;
