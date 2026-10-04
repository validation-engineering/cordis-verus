//! The least partial grammar connected to greatest iterator bisimulation.
//!
//! This is a strict partial reading of Definition 42: a foreign transformation
//! must succeed before its effect on a yield can be compared. Failure is still
//! observable in commutation and local enabledness. The final counterexample
//! explains why adding a failure sink does not imply the unguarded total reading.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, iterator_independence as total, iterators as it, mediated as med, monoid as m,
    observation as o, partial_independence as p, quotient as q,
};
use vstd::prelude::*;

verus! {

pub open spec fn closed<S,I>(family:it::PartialFamily<S,I>,ids:ISet<I>)->bool {
    forall|id:I,s:S| ids.contains(id) && (#[trigger] family(id,s)).is_some()
        && family(id,s).unwrap().next.is_some() ==> ids.contains(family(id,s).unwrap().next.unwrap())
}
pub open spec fn reach<S,I>(family:it::PartialFamily<S,I>,root:I)->ISet<I> {
    ISet::new(|id:I|forall|ids:ISet<I>| #[trigger] ids.contains(root) && closed(family,ids) ==> ids.contains(id))
}
pub proof fn closed_encoding<S,I>(family:it::PartialFamily<S,I>,ids:ISet<I>)
    ensures closed(family,ids)==total::closed(it::encode_partial(family),ids),
{
    let encoded=it::encode_partial(family);
    if closed(family,ids) {
        assert forall|id:I,s:Option<S>| ids.contains(id) && (#[trigger] encoded(id,s)).next.is_some()
            implies ids.contains(encoded(id,s).next.unwrap()) by {
            assert(s.is_some()); assert(family(id,s.unwrap()).is_some());
        }
    } else if total::closed(encoded,ids) {
        assert forall|id:I,s:S| ids.contains(id) && (#[trigger] family(id,s)).is_some()
            && family(id,s).unwrap().next.is_some() implies ids.contains(family(id,s).unwrap().next.unwrap()) by {
            assert(encoded(id,Some(s)).next==family(id,s).unwrap().next);
        }
    }
}
pub proof fn reach_encoding<S,I>(family:it::PartialFamily<S,I>,root:I)
    ensures reach(family,root)==total::reach(it::encode_partial(family),root),
        reach(family,root).contains(root),closed(family,reach(family,root)),
{
    assert forall|ids:ISet<I>| #[trigger] closed(family,ids)==total::closed(it::encode_partial(family),ids) by {closed_encoding(family,ids);}
    assert(reach(family,root) =~= total::reach(it::encode_partial(family),root));
    total::reach_least_closed(it::encode_partial(family),root,ISet::full());
}
pub open spec fn forward<S,I>(family:it::PartialFamily<S,I>,id:I)->med::PartialMap<S> {
    |s:S|match family(id,s) {Some(y)=>Some(y.state),None=>None}
}
pub open spec fn generators<S,I>(family:it::PartialFamily<S,I>,root:I)->ISet<med::PartialMap<S>> {
    ISet::new(|map:med::PartialMap<S>|exists|id:I|reach(family,root).contains(id)
        && (map==forward(family,id) || exists|s:S| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==map))
}
pub open spec fn transforms<S,I>(family:it::PartialFamily<S,I>,root:I,map:med::PartialMap<S>)->bool {
    p::generated(generators(family,root),map)
}
/// Actual successful yields compare inverse domains and the greatest
/// bisimulation of the original family; opaque continuation indices need not equal.
pub open spec fn yields_related<S,I>(eq:spec_fn(S,S)->bool,family:it::PartialFamily<S,I>,a:it::PartialIteration<S,I>,b:it::PartialIteration<S,I>)->bool {
    med::partial_related(eq,a.undo,b.undo)
        && q::continuation(|i:I,j:I|q::iterator_related(|x:Option<S>,y:Option<S>|it::optional_eq(eq,x,y),it::encode_partial(family),i,j),a.next,b.next)
}
pub open spec fn stable<S,I>(eq:spec_fn(S,S)->bool,family:it::PartialFamily<S,I>,id:I,map:med::PartialMap<S>)->bool {
    forall|s:S| #[trigger] map(s).is_some() ==> {
        let a=family(id,s);let b=family(id,map(s).unwrap());
        &&& a.is_some()==b.is_some()
        &&& (a.is_some() ==> yields_related(eq,family,a.unwrap(),b.unwrap()))
    }
}
/// Both complete partial transformation monoids, including all actual inverses
/// at every reachable stage. Only clause (2)'s foreign application is guarded.
pub open spec fn independent<S,I,J>(eq:spec_fn(S,S)->bool,left:it::PartialFamily<S,I>,i:I,right:it::PartialFamily<S,J>,j:J)->bool {
    &&& forall|a:med::PartialMap<S>,b:med::PartialMap<S>|transforms(left,i,a)&&transforms(right,j,b) ==> p::commutes(eq,a,b)
    &&& forall|k:I,b:med::PartialMap<S>|reach(left,i).contains(k)&&transforms(right,j,b) ==> stable(eq,left,k,b)
    &&& forall|k:J,a:med::PartialMap<S>|reach(right,j).contains(k)&&transforms(left,i,a) ==> stable(eq,right,k,a)
}

pub proof fn grammar_reach<K,V,O>(grammar:p::Grammar<K,V,O>)
    ensures reach(it::mediated_family(grammar.program),grammar.root)==p::reach(grammar.program,grammar.root),
{
    let family=it::mediated_family(grammar.program);
    assert forall|ids:ISet<nat>| #[trigger] closed(family,ids)==p::reachable_closed(grammar.program,ids) by {
        if closed(family,ids) {
            assert forall|id:nat,s:IMap<K,V>|ids.contains(id)&&(#[trigger] med::run((grammar.program)(id),s)).is_some()
                &&med::run((grammar.program)(id),s).unwrap().next.is_some()
                implies ids.contains(med::run((grammar.program)(id),s).unwrap().next.unwrap()) by {assert(family(id,s).is_some());}
        } else if p::reachable_closed(grammar.program,ids) {
            assert forall|id:nat,s:IMap<K,V>|ids.contains(id)&&(#[trigger] family(id,s)).is_some()
                &&family(id,s).unwrap().next.is_some() implies ids.contains(family(id,s).unwrap().next.unwrap()) by {
                assert(med::run((grammar.program)(id),s).is_some());
            }
        }
    }
    assert(reach(family,grammar.root) =~= p::reach(grammar.program,grammar.root));
}
pub proof fn grammar_generators<K,V,O>(grammar:p::Grammar<K,V,O>)
    ensures generators(it::mediated_family(grammar.program),grammar.root)==p::reachable_generators(grammar),
{
    grammar_reach(grammar);let family=it::mediated_family(grammar.program);
    assert forall|id:nat| #[trigger] forward(family,id)==p::forward((grammar.program)(id)) by {
        assert(forward(family,id) =~= p::forward((grammar.program)(id)));
    }
    assert(generators(family,grammar.root) =~= p::reachable_generators(grammar)) by {
        assert forall|map:med::PartialMap<IMap<K,V>>|generators(family,grammar.root).contains(map)
            implies p::reachable_generators(grammar).contains(map) by {
            assert(exists|id:nat|reach(family,grammar.root).contains(id)
                && (map==forward(family,id) || exists|s:IMap<K,V>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==map));
            let id=choose|id:nat|reach(family,grammar.root).contains(id)
                && (map==forward(family,id) || exists|s:IMap<K,V>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==map);
            assert(forward(family,id)==p::forward((grammar.program)(id)));
            if map!=forward(family,id) {
                let s=choose|s:IMap<K,V>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==map;
                assert(med::run((grammar.program)(id),s).is_some());
            }
            assert(p::generators((grammar.program)(id)).contains(map));
        }
        assert forall|map:med::PartialMap<IMap<K,V>>|p::reachable_generators(grammar).contains(map)
            implies generators(family,grammar.root).contains(map) by {
            let id=choose|id:nat|p::reach(grammar.program,grammar.root).contains(id)&& #[trigger] p::generators((grammar.program)(id)).contains(map);
            assert(forward(family,id)==p::forward((grammar.program)(id)));
            if map!=p::forward((grammar.program)(id)) {
                let s=choose|s:IMap<K,V>| (#[trigger] med::run((grammar.program)(id),s)).is_some() && med::run((grammar.program)(id),s).unwrap().undo==map;
                assert(family(id,s).is_some());
                assert(exists|s:IMap<K,V>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==map);
            }
            assert(reach(family,grammar.root).contains(id));
            assert(map==forward(family,id) || exists|s:IMap<K,V>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==map);
            assert(exists|id:nat|reach(family,grammar.root).contains(id)
                && (map==forward(family,id) || exists|s:IMap<K,V>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==map));
        }
    }
}

pub proof fn grammar_self_respects<K,V,O>(eq:spec_fn(K,V,V)->bool,grammar:p::Grammar<K,V,O>,id:nat)
    requires p::valid(eq,grammar),p::reach(grammar.program,grammar.root).contains(id),
    ensures q::iterator_related(|a:Option<IMap<K,V>>,b:Option<IMap<K,V>>|it::optional_eq(p::context_eq(eq),a,b),
        it::encode_partial(it::mediated_family(grammar.program)),id,id),
{
    let names=p::reach(grammar.program,grammar.root);let family=it::mediated_family(grammar.program);let ctx=p::context_eq(eq);
    p::context_equivalence(eq,grammar);p::reach_least_closed(grammar.program,grammar.root,names);
    assert forall|i:nat|names.contains(i) implies it::partial_respects(ctx,family,i) by {p::reachable_member(eq,grammar,i);}
    assert forall|i:nat,s:IMap<K,V>| #![trigger family(i,s)] names.contains(i)&&family(i,s).is_some() implies {
        let y=family(i,s).unwrap();
        &&& (y.undo)(y.state).is_some()
        &&& ctx((y.undo)(y.state).unwrap(),s)
        &&& (y.next.is_some() ==> names.contains(y.next.unwrap()))
    } by {p::reachable_member(eq,grammar,i);assert(ctx(s,s));}
    it::partial_family_coinduction(ctx,family,names,id);
}

pub proof fn grammar_stable<K,V,O,P>(eq:spec_fn(K,V,V)->bool,left:p::Grammar<K,V,O>,right:p::Grammar<K,V,P>,id:nat,map:med::PartialMap<IMap<K,V>>)
    requires p::valid(eq,left),p::valid(eq,right),p::separated(left,right),p::witnessed_keys(eq,left,right),
        reach(it::mediated_family(left.program),left.root).contains(id),transforms(it::mediated_family(right.program),right.root,map),
    ensures stable(p::context_eq(eq),it::mediated_family(left.program),id,map),
{
    grammar_reach(left);grammar_generators(right);p::grammar_yields_stable(eq,left,right,id,map);
    let family=it::mediated_family(left.program);let ctx=p::context_eq(eq);
    p::reach_least_closed(left.program,left.root,ISet::full());
    assert forall|s:IMap<K,V>| #[trigger] map(s).is_some() implies {
        let a=family(id,s);let b=family(id,map(s).unwrap());
        &&& a.is_some()==b.is_some()
        &&& (a.is_some() ==> yields_related(ctx,family,a.unwrap(),b.unwrap()))
    } by {
        assert(med::run((left.program)(id),s).is_some()==med::run((left.program)(id),map(s).unwrap()).is_some());
        if family(id,s).is_some() && family(id,s).unwrap().next.is_some() {
            let next=family(id,s).unwrap().next.unwrap();
            assert(p::reach(left.program,left.root).contains(next));grammar_self_respects(eq,left,next);
        }
    }
}
/// Lemma 47's coinductive conclusion for actual partial iterators. Grammar
/// typing and local coeffect witnesses supply the hypotheses, not this relation.
pub proof fn grammar_independence<K,V,O,P>(eq:spec_fn(K,V,V)->bool,left:p::Grammar<K,V,O>,right:p::Grammar<K,V,P>)
    requires p::valid(eq,left),p::valid(eq,right),p::separated(left,right),p::witnessed_keys(eq,left,right),
    ensures independent(p::context_eq(eq),it::mediated_family(left.program),left.root,it::mediated_family(right.program),right.root),
{
    grammar_generators(left);grammar_generators(right);
    let lf=it::mediated_family(left.program);let rf=it::mediated_family(right.program);let ctx=p::context_eq(eq);
    assert forall|a:med::PartialMap<IMap<K,V>>,b:med::PartialMap<IMap<K,V>>|transforms(lf,left.root,a)&&transforms(rf,right.root,b)
        implies p::commutes(ctx,a,b) by {p::grammar_monoids_commute(eq,left,right,a,b);}
    assert forall|i:nat,b:med::PartialMap<IMap<K,V>>|reach(lf,left.root).contains(i)&&transforms(rf,right.root,b)
        implies stable(ctx,lf,i,b) by {grammar_stable(eq,left,right,i,b);}
    assert(p::separated(right,left));
    assert(p::witnessed_keys(eq,right,left)) by {
        assert forall|k:K,a:med::Operation<V,P>,b:med::Operation<V,O>|right.keys.contains(k)&&left.keys.contains(k)
            && (#[trigger] (right.allowed)(k,a))&&(#[trigger] (left.allowed)(k,b))
            implies p::value_independent(|x:V,y:V|eq(k,x,y),a,b) by {
            let e=|x:V,y:V|eq(k,x,y);
            assert(p::value_independent(e,b,a));assert(med::key_equivalence(eq,k));
            assert forall|f:med::PartialMap<V>,g:med::PartialMap<V>|p::value_generators(a).contains(f)&&p::value_generators(b).contains(g)
                implies #[trigger] p::commutes(e,f,g) by {
                assert(p::commutes(e,g,f));
                assert forall|s:V| #[trigger] p::optional_equal(e,p::compose(f,g)(s),p::compose(g,f)(s)) by {
                    p::optional_symmetric(e,p::compose(g,f)(s),p::compose(f,g)(s));
                }
            }
        }
    }
    assert forall|i:nat,a:med::PartialMap<IMap<K,V>>|reach(rf,right.root).contains(i)&&transforms(lf,left.root,a)
        implies stable(ctx,rf,i,a) by {grammar_stable(eq,right,left,i,a);}
}

/// On the domain of an actual foreign application, partial stability is the
/// same inverse/continuation comparison used by total Definition 42.
pub proof fn encoded_yields_on_domain<S,I>(eq:spec_fn(S,S)->bool,family:it::PartialFamily<S,I>,id:I,map:med::PartialMap<S>,s:S)
    requires stable(eq,family,id,map),map(s).is_some(),
    ensures total::yields_related(|a:Option<S>,b:Option<S>|it::optional_eq(eq,a,b),it::encode_partial(family),
        it::encode_partial(family)(id,Some(s)),it::encode_partial(family)(id,it::lift_partial(map,Some(s)))),
{
    if family(id,s).is_some() {it::partial_inverse_encoding(eq,family(id,s).unwrap().undo,family(id,map(s).unwrap()).unwrap().undo);}
}
/// A total foreign map removes this particular domain obstruction. No claim
/// that grammar generators or their inverses are total is hidden in this lemma.
pub proof fn total_foreign_stability<S,I>(eq:spec_fn(S,S)->bool,family:it::PartialFamily<S,I>,id:I,map:med::PartialMap<S>)
    requires c::equivalence(eq),stable(eq,family,id,map),forall|s:S| #[trigger] map(s).is_some(),
    ensures total::stable(|a:Option<S>,b:Option<S>|it::optional_eq(eq,a,b),it::encode_partial(family),id,|s:Option<S>|it::lift_partial(map,s)),
{
    let base=|a:Option<S>,b:Option<S>|it::optional_eq(eq,a,b);let encoded=it::encode_partial(family);
    assert forall|s:Option<S>| #[trigger] total::yields_related(base,encoded,encoded(id,it::lift_partial(map,s)),encoded(id,s)) by {
        if s.is_some() {
            encoded_yields_on_domain(eq,family,id,map,s.unwrap());
            o::map_partial_equivalence(base,encoded(id,s).undo,encoded(id,it::lift_partial(map,s)).undo,encoded(id,s).undo);
            match (encoded(id,s).next,encoded(id,it::lift_partial(map,s)).next) {
                (Some(i),Some(j))=>{q::iterator_partial_equivalence(base,encoded,i,j,i);},_=>{},
            }
        }
    }
}

/// The missing hypothesis cannot be discarded: a failed foreign application
/// selects the sink's terminal continuation, even if the local stage succeeds.
pub proof fn failure_sink_obstruction<S,I>(eq:spec_fn(S,S)->bool,family:it::PartialFamily<S,I>,id:I,map:med::PartialMap<S>,s:S)
    requires family(id,s).is_some(),family(id,s).unwrap().next.is_some(),map(s).is_none(),
    ensures !total::stable(|a:Option<S>,b:Option<S>|it::optional_eq(eq,a,b),it::encode_partial(family),id,|x:Option<S>|it::lift_partial(map,x)),
{
    let encoded=it::encode_partial(family);let base=|a:Option<S>,b:Option<S>|it::optional_eq(eq,a,b);
    let lifted=|x:Option<S>|it::lift_partial(map,x);
    assert(encoded(id,None).next.is_none());assert(encoded(id,Some(s)).next.is_some());
    assert(!total::yields_related(base,encoded,encoded(id,None),encoded(id,Some(s))));
    if total::stable(base,encoded,id,lifted) {total::stable_at(base,encoded,id,lifted,Some(s));}
}

/// Clause (1) does transport through strict lifting: failures agree in either
/// order, and respect upgrades same-input commutation to quotient map equality.
pub proof fn encoded_commutation<S>(eq:spec_fn(S,S)->bool,a:med::PartialMap<S>,b:med::PartialMap<S>)
    requires c::equivalence(eq),p::respects(eq,a),p::respects(eq,b),p::commutes(eq,a,b),
    ensures total::commutes(|x:Option<S>,y:Option<S>|it::optional_eq(eq,x,y),
        |s:Option<S>|it::lift_partial(a,s),|s:Option<S>|it::lift_partial(b,s)),
{
    let ab=p::compose(a,b);let ba=p::compose(b,a);p::composition_respects(eq,b,a);
    assert(med::partial_related(eq,ab,ba)) by {
        assert forall|x:S,y:S| #![trigger ab(x),ba(y)] eq(x,y) implies {
            &&& ab(x).is_some()==ba(y).is_some()
            &&& (ab(x).is_some() ==> eq(ab(x).unwrap(),ba(y).unwrap()))
        } by {
            assert(p::optional_equal(eq,ab(x),ba(x)));
            assert(ba(x).is_some()==ba(y).is_some());
            if ab(x).is_some() {assert(eq(ba(x).unwrap(),ba(y).unwrap()));}
        }
    }
    it::partial_inverse_encoding(eq,ab,ba);
    let left=|s:Option<S>|it::lift_partial(a,s);let right=|s:Option<S>|it::lift_partial(b,s);
    assert(crate::foundations::compose(left,right) =~= (|s:Option<S>|it::lift_partial(ab,s)));
    assert(crate::foundations::compose(right,left) =~= (|s:Option<S>|it::lift_partial(ba,s)));
}

/// A two-stage provision followed by unit, or a terminal provision. These are
/// genuine members of the least grammar, with no assumed operation contracts.
pub open spec fn provision(key:nat,continues:bool)->p::Grammar<nat,int,()> {
    p::Grammar {
        program:|id:nat|if id==0 {med::Node::Provision {key,value:0,next:if continues {Some(1)}else{None}}} else {med::Node::Unit},
        allowed:|key:nat,op:med::Operation<int,()>|false,
        keys:ISet::empty().insert(key),provisions:ISet::empty().insert(key),root:0,
    }
}
pub proof fn provision_valid(key:nat,continues:bool)
    ensures p::valid(|key:nat,x:int,y:int|x==y,provision(key,continues)),
{
    let grammar=provision(key,continues);
    med::constructor_member(grammar.program,grammar.allowed,grammar.keys,grammar.provisions,1);
    med::constructor_member(grammar.program,grammar.allowed,grammar.keys,grammar.provisions,0);
}

/// Disjoint keys and fully witnessed grammar constructors still do not imply
/// unguarded total Definition 42 after adding None. At {1 -> 0}, the second
/// provision fails while the first yields continuation 1; the sink yields None.
pub proof fn provisions_refute_totalization()
    ensures {
        let eq=|key:nat,x:int,y:int|x==y;let left=provision(0,true);let right=provision(1,false);
        let lf=it::mediated_family(left.program);let rf=it::mediated_family(right.program);let ctx=p::context_eq(eq);
        &&& p::valid(eq,left)&&p::valid(eq,right)&&p::separated(left,right)&&p::witnessed_keys(eq,left,right)
        &&& independent(ctx,lf,left.root,rf,right.root)
        &&& !total::independent(|a:Option<IMap<nat,int>>,b:Option<IMap<nat,int>>|it::optional_eq(ctx,a,b),
            it::encode_partial(lf),left.root,it::encode_partial(rf),right.root)
    },
{
    let eq=|key:nat,x:int,y:int|x==y;let left=provision(0,true);let right=provision(1,false);
    provision_valid(0,true);provision_valid(1,false);grammar_independence(eq,left,right);
    let lf=it::mediated_family(left.program);let rf=it::mediated_family(right.program);let ctx=p::context_eq(eq);
    let le=it::encode_partial(lf);let re=it::encode_partial(rf);
    let base=|a:Option<IMap<nat,int>>,b:Option<IMap<nat,int>>|it::optional_eq(ctx,a,b);
    let map=forward(rf,0);let lifted=|s:Option<IMap<nat,int>>|it::lift_partial(map,s);
    let input=IMap::<nat,int>::empty().insert(1,0);
    failure_sink_obstruction(ctx,lf,0,map,input);
    assert(lifted =~= total::forward(re,0));
    total::reach_least_closed(le,0,ISet::full());total::reach_least_closed(re,0,ISet::full());
    assert(total::generators(re,0).contains(lifted));m::generator_member(total::generators(re,0),lifted);
    if total::independent(base,le,0,re,0) {assert(total::stable(base,le,0,lifted));}
}

}
