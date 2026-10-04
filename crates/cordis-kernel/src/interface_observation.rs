//! Lift a component-local function relation to all-key observations.
//!
//! Each forward and actual returned inverse must frame keys outside the
//! interface. Relation inclusion alone is insufficient. Carrier and iterator
//! index are arbitrary; table observations do not include registry/control.
#[cfg(verus_keep_ghost)]
use crate::{
    functional_quotient as fq, iterators as it, mediated as med, observation as o, projection as p,
    quotient as q, semantics as s, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn observed<S,K,V>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,project:spec_fn(S)->IMap<K,V>)->spec_fn(S,S)->bool {
    |a:S,b:S|o::context_equal(eq,keys,project(a),project(b))
}
pub open spec fn outside<S,K,V>(keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,a:S,z:S)->bool {
    forall|k:K| !keys.contains(k) ==> {
        &&& project(a).dom().contains(k)==project(z).dom().contains(k)
        &&& (project(a).dom().contains(k) ==> project(a)[k]==project(z)[k])
    }
}
pub open spec fn map_frame<S,K,V>(keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,f:spec_fn(S)->S)->bool {
    forall|a:S| #[trigger] outside(keys,project,a,f(a))
}
pub open spec fn partial_frame<S,K,V>(keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,f:med::PartialMap<S>)->bool {
    forall|a:S| f(a).is_some() ==> #[trigger] outside(keys,project,a,f(a).unwrap())
}

pub proof fn apply_frame<S,K,V>(keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,f:spec_fn(S)->S,a:S)
    requires map_frame(keys,project,f),
    ensures outside(keys,project,a,f(a)),
{ }

pub proof fn restrict<S,K,V>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,a:S,b:S)
    requires observed(eq,ISet::full(),project)(a,b),
    ensures observed(eq,keys,project)(a,b),
{
    assert forall|k:K| keys.contains(k) implies project(a).dom().contains(k)==project(b).dom().contains(k) by {assert(ISet::<K>::full().contains(k));}
    assert forall|k:K| keys.contains(k) && project(a).dom().contains(k) implies eq(k,project(a)[k],project(b)[k]) by {assert(ISet::<K>::full().contains(k));}
}

/// Domain agreement and values are joined key by key. Outside values inherit
/// their original relation, without assuming value-relation reflexivity.
pub proof fn join<S,K,V>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,a:S,b:S,x:S,y:S)
    requires observed(eq,ISet::full(),project)(a,b),observed(eq,keys,project)(x,y),
        outside(keys,project,a,x),outside(keys,project,b,y),
    ensures observed(eq,ISet::full(),project)(x,y),
{
    assert forall|k:K| ISet::<K>::full().contains(k) implies project(x).dom().contains(k)==project(y).dom().contains(k) by {
        if keys.contains(k) {} else {assert(project(a).dom().contains(k)==project(b).dom().contains(k));}
    }
    assert forall|k:K| ISet::<K>::full().contains(k) && project(x).dom().contains(k) implies eq(k,project(x)[k],project(y)[k]) by {
        if keys.contains(k) {} else {assert(project(a).dom().contains(k));assert(eq(k,project(a)[k],project(b)[k]));}
    }
}

pub proof fn maps<S,K,V>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,f:spec_fn(S)->S,g:spec_fn(S)->S)
    requires o::related_maps(observed(eq,keys,project),f,g),map_frame(keys,project,f),map_frame(keys,project,g),
    ensures o::related_maps(observed(eq,ISet::full(),project),f,g),
{
    let local=observed(eq,keys,project);let global=observed(eq,ISet::full(),project);
    assert forall|a:S,b:S| global(a,b) implies #[trigger] global(f(a),g(b)) by {
        restrict(eq,keys,project,a,b);assert(local(f(a),g(b)));join(eq,keys,project,a,b,f(a),g(b));
    }
}

/// Success domains come from the local partial-function relation. Frames are
/// needed only on successful outputs; paired target success is a conclusion.
pub proof fn partial_maps<S,K,V>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,f:med::PartialMap<S>,g:med::PartialMap<S>)
    requires med::partial_related(observed(eq,keys,project),f,g),partial_frame(keys,project,f),partial_frame(keys,project,g),
    ensures med::partial_related(observed(eq,ISet::full(),project),f,g),
{
    let local=observed(eq,keys,project);let global=observed(eq,ISet::full(),project);
    assert forall|a:S,b:S| #![trigger f(a),g(b)] global(a,b) implies {
        &&& f(a).is_some()==g(b).is_some()
        &&& (f(a).is_some() ==> global(f(a).unwrap(),g(b).unwrap()))
    } by {
        restrict(eq,keys,project,a,b);assert(f(a).is_some()==g(b).is_some());
        if f(a).is_some() {assert(local(f(a).unwrap(),g(b).unwrap()));join(eq,keys,project,a,b,f(a).unwrap(),g(b).unwrap());}
    }
}

/// A continuation-closed family of forward and actual-returned-inverse frames.
/// There is no finite rank or countability assumption on the index space.
pub open spec fn framed<S,K,V,I>(keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,family:q::IteratorFamily<S,I>,names:ISet<I>)->bool {
    forall|i:I,a:S| #![trigger family(i,a)] names.contains(i) ==> {
        let y=family(i,a);
        &&& outside(keys,project,a,y.state)
        &&& map_frame(keys,project,y.undo)
        &&& (y.next.is_some() ==> names.contains(y.next.unwrap()))
    }
}

pub proof fn iterators<S,K,V,I>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,family:q::IteratorFamily<S,I>,names:ISet<I>,left:I,right:I)
    requires framed(keys,project,family,names),names.contains(left),names.contains(right),
        q::iterator_related(observed(eq,keys,project),family,left,right),
    ensures q::iterator_related(observed(eq,ISet::full(),project),family,left,right),
{
    let local=observed(eq,keys,project);let global=observed(eq,ISet::full(),project);
    let relation=|i:I,j:I| names.contains(i) && names.contains(j) && q::iterator_related(local,family,i,j);
    assert(q::bisimulation(global,family,relation)) by {
        assert forall|i:I,j:I,a:S,b:S| #![trigger family(i,a),family(j,b)] relation(i,j) && global(a,b) implies {
            let x=family(i,a);let y=family(j,b);
            &&& global(x.state,y.state) && o::related_maps(global,x.undo,y.undo)
            &&& q::continuation(relation,x.next,y.next)
        } by {
            restrict(eq,keys,project,a,b);q::iterator_unfolding(local,family,i,j);
            let x=family(i,a);let y=family(j,b);
            assert(local(x.state,y.state));assert(outside(keys,project,a,x.state));assert(outside(keys,project,b,y.state));
            join(eq,keys,project,a,b,x.state,y.state);
            maps(eq,keys,project,x.undo,y.undo);
            match (x.next,y.next) {(Some(u),Some(v))=>{assert(q::iterator_related(local,family,u,v));assert(relation(u,v));},_=>{}}
        }
    }
    assert(relation(left,right));
}

pub open spec fn partial_framed<S,K,V,I>(keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,family:it::PartialFamily<S,I>,names:ISet<I>)->bool {
    forall|i:I,a:S| #![trigger family(i,a)] names.contains(i) && family(i,a).is_some() ==> {
        let y=family(i,a).unwrap();
        &&& outside(keys,project,a,y.state)
        &&& partial_frame(keys,project,y.undo)
        &&& (y.next.is_some() ==> names.contains(y.next.unwrap()))
    }
}

/// Lift the complete strict partial iterator relation, including failure and
/// the returned inverse's domain. Failure is not completed to an identity.
pub proof fn partial_iterators<S,K,V,I>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,family:it::PartialFamily<S,I>,names:ISet<I>,left:I,right:I)
    requires partial_framed(keys,project,family,names),names.contains(left),names.contains(right),
        q::iterator_related(|a:Option<S>,b:Option<S>|it::optional_eq(observed(eq,keys,project),a,b),it::encode_partial(family),left,right),
    ensures q::iterator_related(|a:Option<S>,b:Option<S>|it::optional_eq(observed(eq,ISet::full(),project),a,b),it::encode_partial(family),left,right),
{
    let local=observed(eq,keys,project);let global=observed(eq,ISet::full(),project);
    let ls=|a:Option<S>,b:Option<S>|it::optional_eq(local,a,b);let gs=|a:Option<S>,b:Option<S>|it::optional_eq(global,a,b);
    let encoded=it::encode_partial(family);
    let relation=|i:I,j:I| names.contains(i) && names.contains(j) && q::iterator_related(ls,encoded,i,j);
    assert(q::bisimulation(gs,encoded,relation)) by {
        assert forall|i:I,j:I,a:Option<S>,b:Option<S>| #![trigger encoded(i,a),encoded(j,b)] relation(i,j) && gs(a,b) implies {
            let x=encoded(i,a);let y=encoded(j,b);
            &&& gs(x.state,y.state) && o::related_maps(gs,x.undo,y.undo)
            &&& q::continuation(relation,x.next,y.next)
        } by {
            q::iterator_unfolding(ls,encoded,i,j);
            match (a,b) {
                (Some(u),Some(v))=>{
                    restrict(eq,keys,project,u,v);assert(ls(a,b));
                    assert(ls(encoded(i,a).state,encoded(j,b).state));
                    assert(family(i,u).is_some()==family(j,v).is_some());
                    if family(i,u).is_some() {
                        let x=family(i,u).unwrap();let y=family(j,v).unwrap();
                        assert(local(x.state,y.state));
                        join(eq,keys,project,u,v,x.state,y.state);
                        assert(med::partial_related(local,x.undo,y.undo)) by {
                            assert forall|c:S,d:S| #![trigger (x.undo)(c),(y.undo)(d)] local(c,d) implies {
                                &&& (x.undo)(c).is_some()==(y.undo)(d).is_some()
                                &&& ((x.undo)(c).is_some() ==> local((x.undo)(c).unwrap(),(y.undo)(d).unwrap()))
                            } by {assert(ls((encoded(i,a).undo)(Some(c)),(encoded(j,b).undo)(Some(d))));}
                        }
                        partial_maps(eq,keys,project,x.undo,y.undo);it::partial_inverse_encoding(global,x.undo,y.undo);
                        match (x.next,y.next) {(Some(k),Some(l))=>{assert(q::iterator_related(ls,encoded,k,l));assert(relation(k,l));},_=>{}}
                    }
                },
                _=>{},
            }
        }
    }
    assert(relation(left,right));
}

pub proof fn outside_transitive<S,K,V>(keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,a:S,b:S,c:S)
    requires outside(keys,project,a,b),outside(keys,project,b,c),
    ensures outside(keys,project,a,c),
{ }

/// Local immediate recovery becomes all-key recovery because neither the
/// stage nor the actual inverse changes a key outside the interface.
pub proof fn recovery<S,K,V>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,input:S,output:S,restored:S)
    requires forall|k:K,v:V| #[trigger] eq(k,v,v),observed(eq,keys,project)(restored,input),
        outside(keys,project,input,output),outside(keys,project,output,restored),
    ensures observed(eq,ISet::full(),project)(restored,input),
{
    outside_transitive(keys,project,input,output,restored);
    assert(observed(eq,ISet::full(),project)(input,input)) by {
        assert forall|k:K| ISet::<K>::full().contains(k) && project(input).dom().contains(k) implies eq(k,project(input)[k],project(input)[k]) by { }
    }
    join(eq,keys,project,input,input,restored,input);
}

/// The entire witnessed family lifts, not just one successful call. This
/// preserves greatest-continuation respect and all actual inverse witnesses.
pub proof fn witnesses<S,K,V,I>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,family:q::IteratorFamily<S,I>,names:ISet<I>,root:I)
    requires forall|k:K,v:V| #[trigger] eq(k,v,v),framed(keys,project,family,names),names.contains(root),
        it::witnessed(observed(eq,keys,project),family,root),
    ensures it::witnessed(observed(eq,ISet::full(),project),family,root),
{
    let local=observed(eq,keys,project);let global=observed(eq,ISet::full(),project);
    let original=choose|ids:ISet<I>| ids.contains(root) && it::witnessed_closed(local,family,ids);
    let all=original.intersect(names);
    assert(it::witnessed_closed(global,family,all)) by {
        assert forall|i:I| all.contains(i) implies {
            &&& q::iterator_related(global,family,i,i)
            &&& forall|a:S| #[trigger] global((family(i,a).undo)(family(i,a).state),a)
            &&& forall|a:S| #[trigger] family(i,a).next.is_some() ==> all.contains(family(i,a).next.unwrap())
        } by {
            iterators(eq,keys,project,family,names,i,i);
            assert forall|a:S| #[trigger] global((family(i,a).undo)(family(i,a).state),a) by {
                let y=family(i,a);assert(local((y.undo)(y.state),a));
                recovery(eq,keys,project,a,y.state,(y.undo)(y.state));
            }
        }
    }
    assert(all.contains(root));
}

pub proof fn partial_witnesses<S,K,V,I>(eq:spec_fn(K,V,V)->bool,keys:ISet<K>,project:spec_fn(S)->IMap<K,V>,family:it::PartialFamily<S,I>,names:ISet<I>,root:I)
    requires forall|k:K,v:V| #[trigger] eq(k,v,v),partial_framed(keys,project,family,names),names.contains(root),
        it::partial_witnessed(observed(eq,keys,project),family,root),
    ensures it::partial_witnessed(observed(eq,ISet::full(),project),family,root),
{
    let local=observed(eq,keys,project);let global=observed(eq,ISet::full(),project);
    let original=choose|ids:ISet<I>| ids.contains(root) && it::partial_witness_closed(local,family,ids);
    let all=original.intersect(names);
    assert(it::partial_witness_closed(global,family,all)) by {
        assert forall|i:I| all.contains(i) implies {
            &&& q::iterator_related(|a:Option<S>,b:Option<S>|it::optional_eq(global,a,b),it::encode_partial(family),i,i)
            &&& forall|a:S| #[trigger] family(i,a).is_some() ==> {
                let y=family(i,a).unwrap();
                &&& (y.undo)(y.state).is_some() && global((y.undo)(y.state).unwrap(),a)
                &&& (y.next.is_some() ==> all.contains(y.next.unwrap()))
            }
        } by {
            partial_iterators(eq,keys,project,family,names,i,i);
            assert forall|a:S| #[trigger] family(i,a).is_some() implies {
                let y=family(i,a).unwrap();
                &&& (y.undo)(y.state).is_some() && global((y.undo)(y.state).unwrap(),a)
                &&& (y.next.is_some() ==> all.contains(y.next.unwrap()))
            } by {
                let y=family(i,a).unwrap();assert((y.undo)(y.state).is_some());assert(local((y.undo)(y.state).unwrap(),a));
                recovery(eq,keys,project,a,y.state,(y.undo)(y.state).unwrap());
            }
        }
    }
    assert(all.contains(root));
}

/// Directly supplies the all-key iterator field used by the existing nine-rule
/// functional quotient. It does not add a control-frame contract for Child.
pub proof fn model_iterators<V>(eq:spec_fn(Port,V,V)->bool,keys:ISet<Port>,model:s::Model<V>,actor:usize,names:ISet<nat>,left:nat,right:nat)
    requires framed(keys,|a:s::State<V>|p::project(a,ISet::full()),fq::family(model,actor),names),names.contains(left),names.contains(right),
        q::iterator_related(observed(eq,keys,|a:s::State<V>|p::project(a,ISet::full())),fq::family(model,actor),left,right),
    ensures fq::iterator_related(eq,model,actor,left,right),
{
    let project=|a:s::State<V>|p::project(a,ISet::full());
    iterators(eq,keys,project,fq::family(model,actor),names,left,right);
    assert(observed(eq,ISet::full(),project) =~= (|a:s::State<V>,b:s::State<V>|fq::observed(eq,a,b)));
}

pub proof fn model_restore_frame<V>(keys:ISet<Port>,model:s::Model<V>,tokens:Seq<nat>)
    requires forall|i:int| 0<=i<tokens.len() ==> map_frame(keys,|a:s::State<V>|p::project(a,ISet::full()),|a:s::State<V>|(model.undo)(#[trigger] tokens[i],a)),
    ensures map_frame(keys,|a:s::State<V>|p::project(a,ISet::full()),fq::accumulator(model,tokens)),
    decreases tokens.len(),
{
    let project=|a:s::State<V>|p::project(a,ISet::full());
    if tokens.len()>0 {
        model_restore_frame(keys,model,tokens.drop_last());
        assert forall|a:s::State<V>| #[trigger] outside(keys,project,a,fq::accumulator(model,tokens)(a)) by {
            let middle=(model.undo)(tokens.last(),a);let output=s::restore(model,tokens.drop_last(),middle);
            assert(map_frame(keys,project,|x:s::State<V>|(model.undo)(tokens.last(),x)));
            apply_frame(keys,project,|x:s::State<V>|(model.undo)(tokens.last(),x),a);
            apply_frame(keys,project,fq::accumulator(model,tokens.drop_last()),middle);
            outside_transitive(keys,project,a,middle,output);
        }
    }
}

/// Unequal token lists and unequal lengths remain permitted. Only their local
/// denotations and each token's actual outside-interface frame are needed.
pub proof fn model_accumulators<V>(eq:spec_fn(Port,V,V)->bool,keys:ISet<Port>,model:s::Model<V>,left:Seq<nat>,right:Seq<nat>)
    requires o::related_maps(observed(eq,keys,|a:s::State<V>|p::project(a,ISet::full())),fq::accumulator(model,left),fq::accumulator(model,right)),
        forall|i:int| 0<=i<left.len() ==> map_frame(keys,|a:s::State<V>|p::project(a,ISet::full()),|a:s::State<V>|(model.undo)(#[trigger] left[i],a)),
        forall|i:int| 0<=i<right.len() ==> map_frame(keys,|a:s::State<V>|p::project(a,ISet::full()),|a:s::State<V>|(model.undo)(#[trigger] right[i],a)),
    ensures fq::accumulators_related(eq,model,left,right),
{
    let project=|a:s::State<V>|p::project(a,ISet::full());
    model_restore_frame(keys,model,left);model_restore_frame(keys,model,right);
    maps(eq,keys,project,fq::accumulator(model,left),fq::accumulator(model,right));
    assert(observed(eq,ISet::full(),project) =~= (|a:s::State<V>,b:s::State<V>|fq::observed(eq,a,b)));
}

} // verus!
