//! Partial equivalence of controlled strict function fields.
//!
//! A legal-input relation need not be reflexive outside its domain. These
//! generic map and coinductive iterator laws use symmetry and transitivity
//! only, then apply to the actual configuration relation and real restores.
//! This does not identify arbitrary controls under table-only observation.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, iterators as it, mediated as m, mixed_grammar as g,
    mixed_observational_runs as rows, observation as o, quotient as q, semantics as s,
    strict_partial_quotient as controlled, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn per<S>(eq:spec_fn(S,S)->bool)->bool {
    &&& forall|x:S,y:S| #[trigger] eq(x,y) ==> eq(y,x)
    &&& forall|x:S,y:S,z:S| #[trigger] eq(x,y) && #[trigger] eq(y,z) ==> eq(x,z)
}

/// Reflexivity follows for related endpoints, never for arbitrary inputs.
pub proof fn per_members<S>(eq:spec_fn(S,S)->bool,x:S,y:S)
    requires per(eq),eq(x,y),
    ensures eq(y,x),eq(x,x),eq(y,y),
{ }

pub proof fn map_per<S>(eq:spec_fn(S,S)->bool,f:spec_fn(S)->S,g:spec_fn(S)->S,h:spec_fn(S)->S)
    requires per(eq),
    ensures o::related_maps(eq,f,g) ==> o::related_maps(eq,g,f),
        o::related_maps(eq,f,g) && o::related_maps(eq,g,h) ==> o::related_maps(eq,f,h),
        o::related_maps(eq,f,g) ==> o::related_maps(eq,f,f) && o::related_maps(eq,g,g),
{
    if o::related_maps(eq,f,g) {
        assert forall|a:S,b:S|eq(a,b) implies #[trigger] eq(g(a),f(b)) by {
            assert(eq(b,a));assert(eq(f(b),g(a)));
        }
        assert forall|a:S,b:S|eq(a,b) implies #[trigger] eq(f(a),f(b)) by {
            per_members(eq,a,b);assert(eq(f(a),g(b)));assert(eq(g(b),f(b)));
        }
        assert forall|a:S,b:S|eq(a,b) implies #[trigger] eq(g(a),g(b)) by {
            per_members(eq,a,b);assert(eq(g(a),f(b)));assert(eq(f(b),g(b)));
        }
        if o::related_maps(eq,g,h) {
            assert forall|a:S,b:S|eq(a,b) implies #[trigger] eq(f(a),h(b)) by {
                per_members(eq,a,b);assert(eq(f(a),g(b)));assert(eq(g(b),h(b)));
            }
        }
    }
}

/// Partial maps preserve both success/failure and their successful outputs.
/// The middle input is reflexive because it belongs to an actual related pair.
pub proof fn partial_map_per<S>(eq:spec_fn(S,S)->bool,f:m::PartialMap<S>,g:m::PartialMap<S>,h:m::PartialMap<S>)
    requires per(eq),
    ensures m::partial_related(eq,f,g) ==> m::partial_related(eq,g,f),
        m::partial_related(eq,f,g) && m::partial_related(eq,g,h) ==> m::partial_related(eq,f,h),
        m::partial_related(eq,f,g) ==> m::partial_related(eq,f,f) && m::partial_related(eq,g,g),
{
    if m::partial_related(eq,f,g) {
        assert forall|a:S,b:S| #![trigger g(a),f(b)] eq(a,b) implies {
            &&& g(a).is_some()==f(b).is_some()
            &&& (g(a).is_some() ==> eq(g(a).unwrap(),f(b).unwrap()))
        } by {assert(eq(b,a));if f(b).is_some(){assert(eq(f(b).unwrap(),g(a).unwrap()));}}
        assert forall|a:S,b:S| #![trigger f(a),f(b)] eq(a,b) implies {
            &&& f(a).is_some()==f(b).is_some()
            &&& (f(a).is_some() ==> eq(f(a).unwrap(),f(b).unwrap()))
        } by {
            per_members(eq,a,b);assert(f(a).is_some()==g(b).is_some());assert(g(b).is_some()==f(b).is_some());
            if f(a).is_some(){assert(eq(f(a).unwrap(),g(b).unwrap()));assert(eq(g(b).unwrap(),f(b).unwrap()));}
        }
        assert forall|a:S,b:S| #![trigger g(a),g(b)] eq(a,b) implies {
            &&& g(a).is_some()==g(b).is_some()
            &&& (g(a).is_some() ==> eq(g(a).unwrap(),g(b).unwrap()))
        } by {
            per_members(eq,a,b);assert(g(a).is_some()==f(b).is_some());assert(f(b).is_some()==g(b).is_some());
            if g(a).is_some(){assert(eq(g(a).unwrap(),f(b).unwrap()));assert(eq(f(b).unwrap(),g(b).unwrap()));}
        }
        if m::partial_related(eq,g,h) {
            assert forall|a:S,b:S| #![trigger f(a),h(b)] eq(a,b) implies {
                &&& f(a).is_some()==h(b).is_some()
                &&& (f(a).is_some() ==> eq(f(a).unwrap(),h(b).unwrap()))
            } by {
                per_members(eq,a,b);assert(f(a).is_some()==g(b).is_some());assert(g(b).is_some()==h(b).is_some());
                if f(a).is_some(){assert(eq(f(a).unwrap(),g(b).unwrap()));assert(eq(g(b).unwrap(),h(b).unwrap()));}
            }
        }
    }
}

pub proof fn optional_per<S>(eq:spec_fn(S,S)->bool)
    requires per(eq),
    ensures per(|a:Option<S>,b:Option<S>|it::optional_eq(eq,a,b)),
{
    let lifted=|a:Option<S>,b:Option<S>|it::optional_eq(eq,a,b);
    assert forall|a:Option<S>,b:Option<S>| #[trigger] lifted(a,b) implies lifted(b,a) by {
        match (a,b) {(Some(x),Some(y))=>{assert(eq(x,y));},_=>{},}
    }
    assert forall|a:Option<S>,b:Option<S>,c:Option<S>| #[trigger] lifted(a,b) && #[trigger] lifted(b,c) implies lifted(a,c) by {
        match (a,b,c) {(Some(x),Some(y),Some(z))=>{assert(eq(x,y));assert(eq(y,z));},_=>{},}
    }
}

pub proof fn reversed_bisimulation<S,I>(eq:spec_fn(S,S)->bool,family:q::IteratorFamily<S,I>,relation:spec_fn(I,I)->bool)
    requires per(eq),q::bisimulation(eq,family,relation),
    ensures q::bisimulation(eq,family,|i:I,j:I|relation(j,i)),
{
    assert forall|i:I,j:I,a:S,b:S| #![trigger family(i,a),family(j,b)] relation(j,i) && eq(a,b) implies {
        let x=family(i,a);let y=family(j,b);
        &&& eq(x.state,y.state) && o::related_maps(eq,x.undo,y.undo)
        &&& q::continuation(|k:I,l:I|relation(l,k),x.next,y.next)
    } by {
        assert(eq(b,a));assert(eq(family(j,b).state,family(i,a).state));
        assert(o::related_maps(eq,family(j,b).undo,family(i,a).undo));
        map_per(eq,family(j,b).undo,family(i,a).undo,family(i,a).undo);
        match (family(i,a).next,family(j,b).next) {(Some(k),Some(l))=>{assert(relation(l,k));},_=>{},}
    }
}

pub proof fn composed_bisimulation<S,I>(eq:spec_fn(S,S)->bool,family:q::IteratorFamily<S,I>,left:spec_fn(I,I)->bool,right:spec_fn(I,I)->bool)
    requires per(eq),q::bisimulation(eq,family,left),q::bisimulation(eq,family,right),
    ensures q::bisimulation(eq,family,|i:I,k:I|exists|j:I| #[trigger] left(i,j) && right(j,k)),
{
    let composition=|i:I,k:I|exists|j:I| #[trigger] left(i,j) && right(j,k);
    assert forall|i:I,k:I,a:S,c:S| #![trigger family(i,a),family(k,c)] composition(i,k) && eq(a,c) implies {
        let x=family(i,a);let z=family(k,c);
        &&& eq(x.state,z.state) && o::related_maps(eq,x.undo,z.undo) && q::continuation(composition,x.next,z.next)
    } by {
        let j=choose|j:I| #[trigger] left(i,j) && right(j,k);
        let x=family(i,a);let y=family(j,c);let z=family(k,c);
        per_members(eq,a,c);assert(eq(x.state,y.state));assert(eq(y.state,z.state));
        map_per(eq,x.undo,y.undo,z.undo);
        match (x.next,y.next,z.next) {
            (Some(xn),Some(yn),Some(zn))=>{assert(left(xn,yn) && right(yn,zn));assert(composition(xn,zn));},_=>{},
        }
    }
}

/// The genuine greatest relation is a PER on code indices. The proof constructs
/// reverse and composed postfixed relations; no bounded unfolding is used.
pub proof fn iterator_per<S,I>(eq:spec_fn(S,S)->bool,family:q::IteratorFamily<S,I>)
    requires per(eq),
    ensures per(|i:I,j:I|q::iterator_related(eq,family,i,j)),
{
    let greatest=|i:I,j:I|q::iterator_related(eq,family,i,j);
    q::greatest_bisimulation(eq,family);reversed_bisimulation(eq,family,greatest);
    assert forall|i:I,j:I| #[trigger] greatest(i,j) implies greatest(j,i) by {
        assert((|x:I,y:I|greatest(y,x))(j,i));
    }
    composed_bisimulation(eq,family,greatest,greatest);
    let composition=|i:I,k:I|exists|j:I| #[trigger] greatest(i,j) && greatest(j,k);
    assert forall|i:I,j:I,k:I| #[trigger] greatest(i,j) && #[trigger] greatest(j,k) implies greatest(i,k) by {assert(composition(i,k));}
}

pub proof fn legal_input_per<U>(eq:spec_fn(Port,U,U)->bool,actor:usize)
    requires forall|key:Port| #[trigger] m::key_equivalence(eq,key),
    ensures per(controlled::input_relation(eq,actor)),
{
    let input=controlled::input_relation(eq,actor);
    assert forall|a:s::State<U>,b:s::State<U>| #[trigger] input(a,b) implies input(b,a) by {controlled::legal_input_per(eq,actor,a,b,a);}
    assert forall|a:s::State<U>,b:s::State<U>,c:s::State<U>| #[trigger] input(a,b) && #[trigger] input(b,c) implies input(a,c) by {controlled::legal_input_per(eq,actor,a,b,c);}
}

pub proof fn actual_iterator_per<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,actor:usize)
    requires forall|key:Port| #[trigger] m::key_equivalence(eq,key),
    ensures per(|i:I,j:I|controlled::iterator_related(eq,lib,programs,actor,i,j)),
        per(|i:Option<I>,j:Option<I>|controlled::continuations(eq,lib,programs,actor,i,j)),
{
    legal_input_per(eq,actor);let input=controlled::input_relation(eq,actor);optional_per(input);
    let lifted=|a:Option<s::State<U>>,b:Option<s::State<U>>|it::optional_eq(input,a,b);
    iterator_per(lifted,it::encode_partial(controlled::family(lib,programs,actor)));
    let names=|i:I,j:I|controlled::iterator_related(eq,lib,programs,actor,i,j);
    let greatest=|i:I,j:I|q::iterator_related(lifted,it::encode_partial(controlled::family(lib,programs,actor)),i,j);
    assert(names =~= greatest);
    optional_per(names);
    assert((|i:Option<I>,j:Option<I>|controlled::continuations(eq,lib,programs,actor,i,j)) =~= (|i:Option<I>,j:Option<I>|it::optional_eq(names,i,j)));
}

pub proof fn tables_per<U>(eq:spec_fn(Port,U,U)->bool,a:s::State<U>,b:s::State<U>,z:s::State<U>)
    requires forall|key:Port| #[trigger] m::key_equivalence(eq,key),rows::tables_related(eq,a,b),
    ensures rows::tables_related(eq,b,a),rows::tables_related(eq,a,a),rows::tables_related(eq,b,b),
        rows::tables_related(eq,b,z) ==> rows::tables_related(eq,a,z),
{
    rows::tables_reflexive(eq,a);rows::tables_reflexive(eq,b);
    assert forall|n:usize|s::registered(b,n) implies {
        &&& b.tables[n].dom()==a.tables[n].dom()
        &&& forall|key:Port|b.tables[n].dom().contains(key) ==> eq(key,b.tables[n][key],a.tables[n][key])
    } by {
        assert(s::registered(a,n));assert(a.tables[n].dom()==b.tables[n].dom());
        assert forall|key:Port|b.tables[n].dom().contains(key) implies eq(key,b.tables[n][key],a.tables[n][key]) by {
            assert(m::key_equivalence(eq,key));let local=|u:U,v:U|eq(key,u,v);assert(c::equivalence(local));assert(local(a.tables[n][key],b.tables[n][key]));
        }
    }
    if rows::tables_related(eq,b,z) {
        assert forall|n:usize|s::registered(a,n) implies {
            &&& a.tables[n].dom()==z.tables[n].dom()
            &&& forall|key:Port|a.tables[n].dom().contains(key) ==> eq(key,a.tables[n][key],z.tables[n][key])
        } by {
            assert(s::registered(b,n));assert(b.tables[n].dom()==z.tables[n].dom());
            assert forall|key:Port|a.tables[n].dom().contains(key) implies eq(key,a.tables[n][key],z.tables[n][key]) by {
                assert(m::key_equivalence(eq,key));let local=|u:U,v:U|eq(key,u,v);assert(c::equivalence(local));
                assert(local(a.tables[n][key],b.tables[n][key]));assert(local(b.tables[n][key],z.tables[n][key]));
            }
        }
    }
}

/// Actual configuration fields form a PER even when code identities, histories
/// and accumulator lengths differ. There is no assumed reflexivity of arbitrary
/// callbacks, no new execution model and no typing/legality conclusion here.
#[verifier::spinoff_prover]
pub proof fn configuration_per<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>)
    requires forall|key:Port| #[trigger] m::key_equivalence(eq,key),controlled::related(eq,lib,programs,a,b),
    ensures controlled::related(eq,lib,programs,b,a),controlled::related(eq,lib,programs,a,a),controlled::related(eq,lib,programs,b,b),
        controlled::related(eq,lib,programs,b,z) ==> controlled::related(eq,lib,programs,a,z),
{
    tables_per(eq,a.state,b.state,z.state);
    assert forall|actor:usize|s::registered(a.state,actor) implies {
        &&& controlled::iterator_related(eq,lib,programs,actor,b.roots[actor],a.roots[actor])
        &&& controlled::iterator_related(eq,lib,programs,actor,a.roots[actor],a.roots[actor])
        &&& controlled::iterator_related(eq,lib,programs,actor,b.roots[actor],b.roots[actor])
        &&& controlled::continuations(eq,lib,programs,actor,b.current[actor],a.current[actor])
        &&& controlled::continuations(eq,lib,programs,actor,a.current[actor],a.current[actor])
        &&& controlled::continuations(eq,lib,programs,actor,b.current[actor],b.current[actor])
        &&& m::partial_related(controlled::input_relation(eq,actor),controlled::accumulator(b,actor),controlled::accumulator(a,actor))
        &&& m::partial_related(controlled::input_relation(eq,actor),controlled::accumulator(a,actor),controlled::accumulator(a,actor))
        &&& m::partial_related(controlled::input_relation(eq,actor),controlled::accumulator(b,actor),controlled::accumulator(b,actor))
        &&& (controlled::related(eq,lib,programs,b,z) ==> {
            &&& controlled::iterator_related(eq,lib,programs,actor,a.roots[actor],z.roots[actor])
            &&& controlled::continuations(eq,lib,programs,actor,a.current[actor],z.current[actor])
            &&& m::partial_related(controlled::input_relation(eq,actor),controlled::accumulator(a,actor),controlled::accumulator(z,actor))
        })
    } by {
        actual_iterator_per(eq,lib,programs,actor);legal_input_per(eq,actor);
        let names=|i:I,j:I|controlled::iterator_related(eq,lib,programs,actor,i,j);
        let next=|i:Option<I>,j:Option<I>|controlled::continuations(eq,lib,programs,actor,i,j);
        assert(names(a.roots[actor],b.roots[actor]));per_members(names,a.roots[actor],b.roots[actor]);
        assert(next(a.current[actor],b.current[actor]));per_members(next,a.current[actor],b.current[actor]);
        assert(m::partial_related(controlled::input_relation(eq,actor),controlled::accumulator(a,actor),controlled::accumulator(b,actor)));
        if controlled::related(eq,lib,programs,b,z) {
            assert(s::registered(b.state,actor));assert(names(b.roots[actor],z.roots[actor]));assert(next(b.current[actor],z.current[actor]));
            assert(m::partial_related(controlled::input_relation(eq,actor),controlled::accumulator(b,actor),controlled::accumulator(z,actor)));
        }
        partial_map_per(controlled::input_relation(eq,actor),controlled::accumulator(a,actor),controlled::accumulator(b,actor),controlled::accumulator(z,actor));
    }
    assert forall|actor:usize|s::registered(b.state,actor) implies {
        &&& controlled::iterator_related(eq,lib,programs,actor,b.roots[actor],a.roots[actor])
        &&& controlled::continuations(eq,lib,programs,actor,b.current[actor],a.current[actor])
        &&& m::partial_related(controlled::input_relation(eq,actor),controlled::accumulator(b,actor),controlled::accumulator(a,actor))
    } by {assert(s::registered(a.state,actor));}
    assert forall|actor:usize|s::registered(b.state,actor) implies {
        &&& controlled::iterator_related(eq,lib,programs,actor,b.roots[actor],b.roots[actor])
        &&& controlled::continuations(eq,lib,programs,actor,b.current[actor],b.current[actor])
        &&& m::partial_related(controlled::input_relation(eq,actor),controlled::accumulator(b,actor),controlled::accumulator(b,actor))
    } by {assert(s::registered(a.state,actor));}
}


pub proof fn partial_maps_relation_per<S>(eq:spec_fn(S,S)->bool)
    requires per(eq),
    ensures per(|f:m::PartialMap<S>,g:m::PartialMap<S>|m::partial_related(eq,f,g)),
{
    let relation=|f:m::PartialMap<S>,g:m::PartialMap<S>|m::partial_related(eq,f,g);
    assert forall|f:m::PartialMap<S>,g:m::PartialMap<S>| #[trigger] relation(f,g) implies relation(g,f) by {partial_map_per(eq,f,g,f);}
    assert forall|f:m::PartialMap<S>,g:m::PartialMap<S>,h:m::PartialMap<S>| #[trigger] relation(f,g) && #[trigger] relation(g,h) implies relation(f,h) by {partial_map_per(eq,f,g,h);}
}

pub proof fn configuration_relation_per<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>)
    requires forall|key:Port| #[trigger] m::key_equivalence(eq,key),
    ensures per(|a:g::Configuration<U,I>,b:g::Configuration<U,I>|controlled::related(eq,lib,programs,a,b)),
{
    let relation=|a:g::Configuration<U,I>,b:g::Configuration<U,I>|controlled::related(eq,lib,programs,a,b);
    assert forall|a:g::Configuration<U,I>,b:g::Configuration<U,I>| #[trigger] relation(a,b) implies relation(b,a) by {configuration_per(eq,lib,programs,a,b,a);}
    assert forall|a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>| #[trigger] relation(a,b) && #[trigger] relation(b,z) implies relation(a,z) by {configuration_per(eq,lib,programs,a,b,z);}
}
}
