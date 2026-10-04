//! Definition 48 over a supplied context carrier, coeffect projection and total
//! iterator interpretation. This is a conditional definition, not construction
//! of the recursive Gamma of Definition 28. In particular, strict partial
//! interpreters do not acquire a total full-context witness through this API.
#[cfg(verus_keep_ghost)]
use crate::{iterator_independence as reach, iterators as it, observation as o, quotient as q};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(K)]
pub struct Component<K,I> {
    pub dependencies:ISet<K>,
    pub provisions:ISet<K>,
    pub root:I,
}

pub open spec fn observed<G,K,V>(eq:spec_fn(K,V,V)->bool,
    coeffects:spec_fn(G)->IMap<K,V>,keys:ISet<K>,a:G,b:G)->bool {
    o::context_equal(eq,keys,coeffects(a),coeffects(b))
}

pub proof fn singleton_observation<K,V>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,key:K,a:V,b:V)
    requires keys.contains(key),
    ensures o::context_equal(eq,keys,IMap::empty().insert(key,a),IMap::empty().insert(key,b))==eq(key,a,b),
{
    let left=IMap::empty().insert(key,a);let right=IMap::empty().insert(key,b);
    if o::context_equal(eq,keys,left,right) {assert(eq(key,left[key],right[key]));}
    if eq(key,a,b) {
        assert forall|k:K| keys.contains(k) && left.dom().contains(k)
            implies #[trigger] eq(k,left[k],right[k]) by {assert(k==key);}
    }
}

/// The type in Equation 42: least witnessed iterator membership, with respect
/// and actual inverse recovery quantified over the entire supplied carrier G.
pub open spec fn component_core<G,K,V,I>(eq:spec_fn(K,V,V)->bool,
    coeffects:spec_fn(G)->IMap<K,V>,family:q::IteratorFamily<G,I>,c:Component<K,I>)->bool {
    it::paper_witnessed(|a:G,b:G|observed(eq,coeffects,c.dependencies.union(c.provisions),a,b),family,c.root)
}

/// An operational installation interpretation makes the explanatory provision
/// bound explicit. It records keys actually installed by a stage, including an
/// installation hidden by later changes within that stage. It must be supplied
/// by the primitive interpretation; an empty event set is not inferred from an
/// unchanged final domain.
pub open spec fn installation_bound<G,K,I>(family:q::IteratorFamily<G,I>,
    installs:spec_fn(I,G)->ISet<K>,c:Component<K,I>)->bool {
    forall|id:I,input:G| reach::reach(family,c.root).contains(id)
        ==> (#[trigger] installs(id,input)).subset_of(c.provisions)
}

/// A useful observable consequence, weaker than an installation-event bound.
pub open spec fn introduced_bindings_bound<G,K,V,I>(coeffects:spec_fn(G)->IMap<K,V>,
    family:q::IteratorFamily<G,I>,c:Component<K,I>)->bool {
    forall|id:I,input:G,key:K| reach::reach(family,c.root).contains(id)
        && #[trigger] coeffects(family(id,input).state).dom().contains(key)
        && !coeffects(input).dom().contains(key) ==> c.provisions.contains(key)
}

/// Full component predicate, conditional on an accurate installation-event
/// interpretation. No disjointness of d and p, or eventual provision of every
/// declared key, is silently added to Definition 48.
pub open spec fn component<G,K,V,I>(eq:spec_fn(K,V,V)->bool,
    coeffects:spec_fn(G)->IMap<K,V>,family:q::IteratorFamily<G,I>,
    installs:spec_fn(I,G)->ISet<K>,c:Component<K,I>)->bool {
    component_core(eq,coeffects,family,c) && installation_bound(family,installs,c)
}

pub proof fn component_stage_witness<G,K,V,I>(eq:spec_fn(K,V,V)->bool,
    coeffects:spec_fn(G)->IMap<K,V>,family:q::IteratorFamily<G,I>,
    installs:spec_fn(I,G)->ISet<K>,c:Component<K,I>,input:G)
    requires component(eq,coeffects,family,installs,c),
    ensures observed(eq,coeffects,c.dependencies.union(c.provisions),
        (family(c.root,input).undo)(family(c.root,input).state),input),
        q::iterator_related(|a:G,b:G|observed(eq,coeffects,c.dependencies.union(c.provisions),a,b),family,c.root,c.root),
        family(c.root,input).next.is_some() ==> it::paper_witnessed(
            |a:G,b:G|observed(eq,coeffects,c.dependencies.union(c.provisions),a,b),family,family(c.root,input).next.unwrap()),
{
    let base=|a:G,b:G|observed(eq,coeffects,c.dependencies.union(c.provisions),a,b);
    it::paper_witnessed_unfolding(base,family,c.root);
    assert(base((family(c.root,input).undo)(family(c.root,input).state),input));
}

/// Installing-event provenance, rather than net-domain equality, justifies the
/// public observable bound. This premise is local to actual stage evaluations.
pub proof fn installations_imply_binding_bound<G,K,V,I>(coeffects:spec_fn(G)->IMap<K,V>,
    family:q::IteratorFamily<G,I>,installs:spec_fn(I,G)->ISet<K>,c:Component<K,I>)
    requires installation_bound(family,installs,c),
        forall|id:I,input:G,key:K| reach::reach(family,c.root).contains(id)
            && #[trigger] coeffects(family(id,input).state).dom().contains(key)
            && !coeffects(input).dom().contains(key) ==> installs(id,input).contains(key),
    ensures introduced_bindings_bound(coeffects,family,c),
{ }

/// The original leastness property is retained; a coinductively closed,
/// nonterminating family does not become a component through this theorem.
pub proof fn component_induction<G,K,V,I>(eq:spec_fn(K,V,V)->bool,
    coeffects:spec_fn(G)->IMap<K,V>,family:q::IteratorFamily<G,I>,
    installs:spec_fn(I,G)->ISet<K>,c:Component<K,I>,members:ISet<I>)
    requires component(eq,coeffects,family,installs,c),
        it::witnessed_constructor_closed(|a:G,b:G|observed(eq,coeffects,c.dependencies.union(c.provisions),a,b),family,members),
    ensures members.contains(c.root),
{
    it::paper_witnessed_least(|a:G,b:G|observed(eq,coeffects,c.dependencies.union(c.provisions),a,b),family,c.root,members);
}

pub open spec fn unit<G,I>()->q::IteratorFamily<G,I> {
    |_:I,a:G|q::Iteration {state:a,undo:|b:G|b,next:None}
}

pub proof fn unit_related<G,I>(eq:spec_fn(G,G)->bool,left:I,right:I)
    ensures q::iterator_related(eq,unit(),left,right),
{
    let relation=|_:I,_:I|true;
    assert(q::bisimulation(eq,unit(),relation));
    assert(relation(left,right));
}

pub proof fn unit_witnessed<G,I>(eq:spec_fn(G,G)->bool,id:I)
    requires forall|a:G| #[trigger] eq(a,a),
    ensures it::paper_witnessed(eq,unit(),id),
{
    let names=ISet::<I>::full();
    assert forall|i:I| names.contains(i) implies {
        &&& q::iterator_related(eq,unit(),i,i)
        &&& forall|a:G| #[trigger] eq((unit::<G,I>()(i,a).undo)(unit::<G,I>()(i,a).state),a)
        &&& forall|a:G| #[trigger] unit::<G,I>()(i,a).next.is_some() ==> names.contains(unit::<G,I>()(i,a).next.unwrap())
    } by {unit_related(eq,i,i);}
    assert(it::witnessed_closed(eq,unit(),names));
    assert(names.contains(id));
    it::inductive_constructor(unit::<G,I>(),id);
}

/// A nonempty, value-changing total example: every G=int carries key false,
/// either boolean iterator identity increments its value and returns the
/// actual subtraction inverse. The interface is nonempty; no key is installed.
pub open spec fn counter_coeffects(a:int)->IMap<bool,int> {IMap::empty().insert(false,a)}
pub open spec fn counter_family()->q::IteratorFamily<int,bool> {
    |_:bool,a:int|q::Iteration {state:a+1,undo:|b:int|b-1,next:None}
}
pub open spec fn counter_component()->Component<bool,bool> {
    Component {dependencies:ISet::empty().insert(false),provisions:ISet::empty(),root:false}
}
pub proof fn counter_is_component()
    ensures component(|_:bool,a:int,b:int|a==b,|a:int|counter_coeffects(a),counter_family(),
        |_:bool,_:int|ISet::empty(),counter_component()),
        counter_coeffects(4).dom().contains(false),counter_family()(false,4).state==5,
        (counter_family()(false,4).undo)(5)==4,
{
    let coeffects=|a:int|counter_coeffects(a);
    let c=counter_component();let family=counter_family();
    let eq=|a:int,b:int|observed(|_:bool,u:int,v:int|u==v,coeffects,c.dependencies.union(c.provisions),a,b);
    assert forall|a:int,b:int| #[trigger] eq(a,b)==(a==b) by {
        singleton_observation(|_:bool,u:int,v:int|u==v,c.dependencies.union(c.provisions),false,a,b);
    }
    let relation=|_:bool,_:bool|true;
    assert(q::bisimulation(eq,family,relation));
    let names=ISet::<bool>::full();
    assert forall|i:bool| names.contains(i) implies {
        &&& q::iterator_related(eq,family,i,i)
        &&& forall|a:int| #[trigger] eq((family(i,a).undo)(family(i,a).state),a)
        &&& forall|a:int| #[trigger] family(i,a).next.is_some() ==> names.contains(family(i,a).next.unwrap())
    } by {assert(relation(i,i));}
    assert(it::witnessed_closed(eq,family,names));
    assert(names.contains(false));it::inductive_constructor(family,false);
}

} // verus!
