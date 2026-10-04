//! A guard-aware local correction of orchestration/child transposition.
//!
//! An external insertion may move before a child landing only when its parent
//! was already present. Freshness, provision exclusion and root membership are
//! checked as local insertion premises. The two real histories need not be equal:
//! each stores the actual input of its own landing, while receipts correspond.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, global, mixed_grammar as g, mixed_syntax as syntax,
    preservation as inv, refinement as r, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn insert<U,I>(a:g::Configuration<U,I>,id:usize,parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>,root:I)->g::Configuration<U,I> {
    g::Configuration {
        state:s::extend_child(a.state,global::insert_fiber(a.state.control,id,parent,dependencies,provisions),id,0),
        roots:a.roots.insert(id,root),current:a.current.insert(id,None),history:a.history,
    }
}
/// These are the actual O-Insert guards and a syntactic component obligation.
/// No assertion about the whole successor or reverse execution is included.
pub open spec fn insertion_ready<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,id:usize,
    parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>,root:I)->bool {
    &&& !s::registered(a.state,id)
    &&& match parent {None=>true,Some(p)=>s::registered(a.state,p)}
    &&& forall|n:usize,k:Port| s::registered(a.state,n) && a.state.control.fibers[n].provisions.contains(k) ==> !provisions.contains(k)
    &&& syntax::member(lib,programs,id,dependencies.union(provisions),provisions,root)
}
pub proof fn insertion_step<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,id:usize,
    parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>,root:I)
    requires insertion_ready(lib,programs,a,id,parent,dependencies,provisions,root),
    ensures g::step(lib,programs,a,insert(a,id,parent,dependencies,provisions,root),id,r::Rule::Insert),
{
    let z=insert(a,id,parent,dependencies,provisions,root);
    assert(r::frame(a.state.control,z.state.control,id));
    assert(inv::insert_map(a.state,z.state,id));
}

/// An Inactive empty insertion leaves actual publication and the old actor's
/// target unchanged, including the absence of a target before landing Divert.
pub proof fn insertion_target<U,I>(a:g::Configuration<U,I>,id:usize,parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>,root:I,actor:usize,view:ISet<Binding>)
    requires !s::registered(a.state,id),s::registered(a.state,actor),
    ensures s::target(a.state,actor,view)==s::target(insert(a,id,parent,dependencies,provisions,root).state,actor,view),
        s::coherent(a.state,actor)==s::coherent(insert(a,id,parent,dependencies,provisions,root).state,actor),
{
    let z=insert(a,id,parent,dependencies,provisions,root);assert(actor!=id);
    assert forall|key:Port,n:usize| s::publishes(a.state,key,n)==s::publishes(z.state,key,n) by {if n==id {assert(!s::publishes(z.state,key,n));}}
}
pub open spec fn landing_phase(rule:r::Rule)->Phase {
    if rule==r::Rule::Iter {Phase::Loading} else if rule==r::Rule::Finish {Phase::Active} else {Phase::Unloading}
}
pub open spec fn same_receipts<U,I>(left:g::Configuration<U,I>,right:g::Configuration<U,I>)->bool {
    left.history.len()==right.history.len() && forall|i:int| 0<=i<left.history.len() ==> {
        &&& left.history[i].iterator==right.history[i].iterator
        &&& left.history[i].landed.receipt==right.history[i].landed.receipt
        &&& left.history[i].landed.next==right.history[i].landed.next
        &&& left.history[i].landed.spawn==right.history[i].landed.spawn
    }
}

/// Corresponding authentic receipts execute the same strict inverse program
/// on every common input. Different recorded forward inputs are not replayed.
pub proof fn corresponding_restore<U,I>(left:g::Configuration<U,I>,right:g::Configuration<U,I>,tokens:Seq<nat>,input:s::State<U>,actor:usize)
    requires same_receipts(left,right),
    ensures g::restore(left.history,tokens,input,actor)==g::restore(right.history,tokens,input,actor),
        forall|token:nat| #[trigger] g::kind(left.history)(token)==g::kind(right.history)(token),
    decreases tokens.len(),
{
    if tokens.len()>0 && tokens.last()<left.history.len() {
        let receipt=left.history[tokens.last() as int].landed.receipt;
        assert(receipt==right.history[tokens.last() as int].landed.receipt);
        if g::owner(receipt)==actor && g::undo(receipt,input).is_some() {
            corresponding_restore(left,right,tokens.drop_last(),g::undo(receipt,input).unwrap(),actor);
        }
    }
}

/// Two concrete mixed steps commute when the insertion does not read the name
/// born by the landing. The original landing and local insertion guards are
/// inputs; reverse-step applicability and the common endpoint are conclusions.
pub proof fn child_insert_diamond<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize,rule:r::Rule,
    child:usize,child_dependencies:ISet<Port>,child_provisions:ISet<Port>,child_root:I,next:Option<I>,
    id:usize,parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>,root:I)
    requires d::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        programs(actor)(a.current[actor].unwrap())==(g::Node::Child {child,dependencies:child_dependencies,provisions:child_provisions,root:child_root,next}),
        insertion_ready(lib,programs,b,id,parent,dependencies,provisions,root),parent!=Some(child),
    ensures {
        let forward=insert(b,id,parent,dependencies,provisions,root);
        let middle=insert(a,id,parent,dependencies,provisions,root);
        let reverse=g::land(lib,programs,middle,actor,landing_phase(rule));
        &&& id!=actor && id!=child && !s::registered(a.state,id) && !s::registered(a.state,child)
        &&& insertion_ready(lib,programs,a,id,parent,dependencies,provisions,root)
        &&& g::step(lib,programs,b,forward,id,r::Rule::Insert)
        &&& g::step(lib,programs,a,middle,id,r::Rule::Insert)
        &&& g::step(lib,programs,middle,reverse,actor,rule)
        &&& g::well_formed(lib,programs,forward) && g::well_formed(lib,programs,middle) && g::well_formed(lib,programs,reverse)
        &&& forward.state==reverse.state && forward.roots==reverse.roots && forward.current==reverse.current
        &&& same_receipts(forward,reverse)
        &&& forward.history.len()==a.history.len()+1
        &&& forall|i:int| 0<=i<a.history.len() ==> forward.history[i]==a.history[i] && reverse.history[i]==a.history[i]
        &&& forward.history.last().input==a.state && reverse.history.last().input==middle.state
        &&& forward.history.last().landed.receipt==(g::Receipt::Child {actor,child})
        &&& reverse.history.last().landed.receipt==(g::Receipt::Child {actor,child})
    },
{
    g::frame(eq,lib,programs,a,b,actor,rule);g::configuration_preservation(eq,lib,programs,a,b,actor,rule);
    let forward=insert(b,id,parent,dependencies,provisions,root);
    let middle=insert(a,id,parent,dependencies,provisions,root);
    let reverse=g::land(lib,programs,middle,actor,landing_phase(rule));
    assert(b==g::land(lib,programs,a,actor,landing_phase(rule)));
    assert(g::run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor).is_some());
    assert(!s::registered(a.state,child));assert(s::registered(b.state,child));assert(actor!=child);
    assert(id!=child);assert(id!=actor);assert(!s::registered(a.state,id));
    assert forall|n:usize,k:Port| s::registered(a.state,n) && a.state.control.fibers[n].provisions.contains(k) implies !provisions.contains(k) by {
        assert(s::registered(b.state,n));assert(b.state.control.fibers[n].provisions.contains(k));
    }
    if let Some(p)=parent {assert(p!=child);assert(s::registered(a.state,p));}
    assert(insertion_ready(lib,programs,a,id,parent,dependencies,provisions,root));
    insertion_step(lib,programs,b,id,parent,dependencies,provisions,root);
    insertion_step(lib,programs,a,id,parent,dependencies,provisions,root);
    insertion_target(a,id,parent,dependencies,provisions,root,actor,a.state.control.fibers[actor].committed);
    let context=g::create(middle.state,actor,child,child_dependencies,child_provisions);
    assert(r::frame(middle.state.control,context.control,child));
    assert forall|n:usize,k:Port| s::registered(middle.state,n) && middle.state.control.fibers[n].provisions.contains(k)
        implies !child_provisions.contains(k) by {
        if n==id {if child_provisions.contains(k) {assert(b.state.control.fibers[child].provisions.contains(k));assert(!provisions.contains(k));}}
        else {assert(s::registered(a.state,n));}
    }
    assert(r::step(middle.state.control,context.control,child,r::Rule::Insert));
    assert(g::run(lib,programs(actor)(middle.current[actor].unwrap()),middle.state,actor).is_some());
    assert(g::step(lib,programs,middle,reverse,actor,rule));
    assert(forward.state.control.fibers =~= reverse.state.control.fibers);
    assert(forward.state.tables =~= reverse.state.tables);
    assert(forward.state.effects =~= reverse.state.effects);
    assert(forward.state.iterators =~= reverse.state.iterators);
    assert(forward.state.accumulators =~= reverse.state.accumulators);
    assert(forward.roots =~= reverse.roots);assert(forward.current =~= reverse.current);
    assert(same_receipts(forward,reverse)) by {
        assert forall|i:int| 0<=i<forward.history.len() implies {
            &&& forward.history[i].iterator==reverse.history[i].iterator
            &&& forward.history[i].landed.receipt==reverse.history[i].landed.receipt
            &&& forward.history[i].landed.next==reverse.history[i].landed.next
            &&& forward.history[i].landed.spawn==reverse.history[i].landed.spawn
        } by {if i<a.history.len() {assert(forward.history[i]==a.history[i]);assert(reverse.history[i]==a.history[i]);} else {assert(i==a.history.len());}}
    }
    g::configuration_preservation(eq,lib,programs,b,forward,id,r::Rule::Insert);
    g::configuration_preservation(eq,lib,programs,a,middle,id,r::Rule::Insert);
    g::configuration_preservation(eq,lib,programs,middle,reverse,actor,rule);
}

/// The missing parent guard is a real obstruction, independent of metadata,
/// type-family choices and how the candidate reverse successor is constructed.
pub proof fn born_parent_blocks_insert<U,I>(a:g::Configuration<U,I>,child:usize,id:usize,candidate:g::Configuration<U,I>)
    requires !s::registered(a.state,child),candidate.state.control.fibers[id].parent==Some(child),
    ensures !r::step(a.state.control,candidate.state.control,id,r::Rule::Insert),
{ }

/// The same construction can be recovered directly from two already observed
/// steps. The second step supplies its own fresh name, declarations and root.
pub proof fn observed_pair<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,
    child:usize,child_dependencies:ISet<Port>,child_provisions:ISet<Port>,child_root:I,next:Option<I>,id:usize)
    requires d::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        programs(actor)(a.current[actor].unwrap())==(g::Node::Child {child,dependencies:child_dependencies,provisions:child_provisions,root:child_root,next}),
        g::step(lib,programs,b,z,id,r::Rule::Insert),z.state.control.fibers[id].parent!=Some(child),
    ensures {
        let f=z.state.control.fibers[id];let middle=insert(a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
        let reverse=g::land(lib,programs,middle,actor,landing_phase(rule));
        &&& g::step(lib,programs,a,middle,id,r::Rule::Insert) && g::step(lib,programs,middle,reverse,actor,rule)
        &&& z.state==reverse.state && z.roots==reverse.roots && z.current==reverse.current && same_receipts(z,reverse)
        &&& g::well_formed(lib,programs,middle) && g::well_formed(lib,programs,reverse)
        &&& z.history.last().input==a.state && reverse.history.last().input==middle.state
    },
{
    let f=z.state.control.fibers[id];let external=insert(b,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
    assert(r::step(b.state.control,z.state.control,id,r::Rule::Insert));
    assert(f.committed =~= ISet::<Binding>::empty());
    assert(f==external.state.control.fibers[id]);
    assert(z.state.control.fibers.dom() =~= external.state.control.fibers.dom()) by {
        assert forall|n:usize| z.state.control.fibers.dom().contains(n)==external.state.control.fibers.dom().contains(n) by {
            if n!=id {assert(r::frame(b.state.control,z.state.control,id));assert(s::registered(b.state,n)==s::registered(z.state,n));}
        }
    }
    assert(z.state.control.fibers =~= external.state.control.fibers) by {
        assert forall|n:usize| z.state.control.fibers.dom().contains(n) implies z.state.control.fibers[n]==external.state.control.fibers[n] by {
            if n!=id {assert(r::frame(b.state.control,z.state.control,id));assert(s::registered(b.state,n));assert(z.state.control.fibers[n]==b.state.control.fibers[n]);}
        }
    }
    assert(z==external);
    assert(insertion_ready(lib,programs,b,id,f.parent,f.dependencies,f.provisions,z.roots[id]));
    child_insert_diamond(eq,lib,programs,a,b,actor,rule,child,child_dependencies,child_provisions,child_root,next,
        id,f.parent,f.dependencies,f.provisions,z.roots[id]);
}

/// A real nonempty prefix exercises the diamond with disjoint nonempty child
/// and external provisions. Histories differ because their actual inputs do.
pub proof fn concrete_diamond()
    ensures {
        let a=crate::mixed_examples::trace()[2];let b=crate::mixed_examples::trace()[3];
        let lib=crate::mixed_examples::library();let programs=crate::mixed_examples::programs();
        let provided=crate::mixed_examples::provided(2);
        let forward=insert(b,2,Some(0),ISet::empty(),provided,false);
        let middle=insert(a,2,Some(0),ISet::empty(),provided,false);
        let reverse=g::land(lib,programs,middle,0,Phase::Loading);
        &&& g::step(lib,programs,a,b,0,r::Rule::Iter) && g::step(lib,programs,b,forward,2,r::Rule::Insert)
        &&& g::step(lib,programs,a,middle,2,r::Rule::Insert) && g::step(lib,programs,middle,reverse,0,r::Rule::Iter)
        &&& forward.state==reverse.state && forward.roots==reverse.roots && forward.current==reverse.current
        &&& same_receipts(forward,reverse) && forward.history!=reverse.history
        &&& forward.history.last().landed.receipt==(g::Receipt::Child {actor:0usize,child:1usize})
        &&& g::well_formed(lib,programs,forward) && g::well_formed(lib,programs,reverse)
    },
{
    crate::mixed_examples::actual_execution();crate::mixed_examples::primitive_theory();
    let lib=crate::mixed_examples::library();let programs=crate::mixed_examples::programs();
    g::from_empty_safe(crate::mixed_examples::equality(),lib,programs,crate::mixed_examples::trace(),crate::mixed_examples::labels());
    reveal(crate::mixed_examples::trace);
    let a=crate::mixed_examples::trace()[2];let b=crate::mixed_examples::trace()[3];let provided=crate::mixed_examples::provided(2);
    syntax::constructor_member(lib,programs,2,provided,provided,false);
    assert(ISet::<Port>::empty().union(provided) =~= provided);
    assert(insertion_ready(lib,programs,b,2,Some(0),ISet::empty(),provided,false));
    child_insert_diamond(crate::mixed_examples::equality(),lib,programs,a,b,0,r::Rule::Iter,
        1,ISet::empty(),crate::mixed_examples::provided(1),false,Some(true),2,Some(0),ISet::empty(),provided,false);
    let forward=insert(b,2,Some(0),ISet::empty(),provided,false);
    let middle=insert(a,2,Some(0),ISet::empty(),provided,false);
    let reverse=g::land(lib,programs,middle,0,Phase::Loading);
    assert(!s::registered(forward.history.last().input,2));assert(s::registered(reverse.history.last().input,2));
}

/// A legal insertion after a child landing need not be legal before it: the
/// parent may be precisely the name that the landing has just created.
pub proof fn concrete_parent_rejection()
    ensures {
        let a=crate::mixed_examples::trace()[2];let b=crate::mixed_examples::trace()[3];
        let lib=crate::mixed_examples::library();let programs=crate::mixed_examples::programs();
        let provided=crate::mixed_examples::provided(2);
        let after=insert(b,2,Some(1),ISet::empty(),provided,false);
        let premature=insert(a,2,Some(1),ISet::empty(),provided,false);
        &&& g::step(lib,programs,a,b,0,r::Rule::Iter) && g::step(lib,programs,b,after,2,r::Rule::Insert)
        &&& !g::step(lib,programs,a,premature,2,r::Rule::Insert)
        &&& !r::step(a.state.control,premature.state.control,2,r::Rule::Insert)
        &&& !insertion_ready(lib,programs,a,2,Some(1),ISet::empty(),provided,false)
        &&& !insertion_ready(lib,programs,b,2,Some(0),ISet::empty(),crate::mixed_examples::provided(1),false)
    },
{
    crate::mixed_examples::actual_execution();reveal(crate::mixed_examples::trace);
    let a=crate::mixed_examples::trace()[2];let b=crate::mixed_examples::trace()[3];
    let lib=crate::mixed_examples::library();let programs=crate::mixed_examples::programs();let provided=crate::mixed_examples::provided(2);
    syntax::constructor_member(lib,programs,2,provided,provided,false);
    assert(ISet::<Port>::empty().union(provided) =~= provided);
    assert(insertion_ready(lib,programs,b,2,Some(1),ISet::empty(),provided,false));
    insertion_step(lib,programs,b,2,Some(1),ISet::empty(),provided,false);
    born_parent_blocks_insert(a,1,2,insert(a,2,Some(1),ISet::empty(),provided,false));
    assert(b.state.control.fibers[1usize].provisions.contains(crate::mixed_examples::key(1)));
}

} // verus!
