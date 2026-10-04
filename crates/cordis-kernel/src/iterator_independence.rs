//! Definition 42 on arbitrary iterator families and observational quotients.
//!
//! Reachability is the least continuation-closed set. Inverses are compared as
//! maps and continuations by the greatest bisimulation, including infinite
//! continuations; no common rank or equality of opaque indices is required.
#[cfg(verus_keep_ghost)]
use crate::{calculus as c, foundations as f, monoid as m, observation as o, quotient as q};
use vstd::prelude::*;

verus! {

pub open spec fn closed<S,I>(family:q::IteratorFamily<S,I>,ids:ISet<I>)->bool {
    forall|i:I,s:S| ids.contains(i) && (#[trigger] family(i,s)).next.is_some()
        ==> ids.contains(family(i,s).next.unwrap())
}
pub open spec fn reach<S,I>(family:q::IteratorFamily<S,I>,root:I)->ISet<I> {
    ISet::new(|i:I|forall|ids:ISet<I>| #[trigger] ids.contains(root) && closed(family,ids) ==> ids.contains(i))
}
pub proof fn reach_least_closed<S,I>(family:q::IteratorFamily<S,I>,root:I,ids:ISet<I>)
    ensures reach(family,root).contains(root),closed(family,reach(family,root)),
        ids.contains(root) && closed(family,ids) ==> reach(family,root).subset_of(ids),
{
    assert forall|i:I,s:S| reach(family,root).contains(i) && (#[trigger] family(i,s)).next.is_some()
        implies reach(family,root).contains(family(i,s).next.unwrap()) by {
        let next=family(i,s).next.unwrap();
        assert forall|candidate:ISet<I>| #[trigger] candidate.contains(root) && closed(family,candidate)
            implies candidate.contains(next) by {assert(candidate.contains(i));}
    }
}

pub open spec fn forward<S,I>(family:q::IteratorFamily<S,I>,id:I)->spec_fn(S)->S { |s:S|family(id,s).state }
pub open spec fn generators<S,I>(family:q::IteratorFamily<S,I>,root:I)->ISet<spec_fn(S)->S> {
    ISet::new(|map:spec_fn(S)->S| exists|id:I| reach(family,root).contains(id)
        && (map==forward(family,id) || exists|input:S| (#[trigger] family(id,input)).undo==map))
}
pub open spec fn transforms<S,I>(family:q::IteratorFamily<S,I>,root:I,map:spec_fn(S)->S)->bool {
    m::generated(generators(family,root),map)
}
pub open spec fn commutes<S>(eq:spec_fn(S,S)->bool,a:spec_fn(S)->S,b:spec_fn(S)->S)->bool {
    o::related_maps(eq,f::compose(a,b),f::compose(b,a))
}
pub open spec fn yields_related<S,I>(eq:spec_fn(S,S)->bool,family:q::IteratorFamily<S,I>,a:q::Iteration<S,I>,b:q::Iteration<S,I>)->bool {
    o::related_maps(eq,a.undo,b.undo) && q::continuation(|i:I,j:I|q::iterator_related(eq,family,i,j),a.next,b.next)
}
pub open spec fn stable<S,I>(eq:spec_fn(S,S)->bool,family:q::IteratorFamily<S,I>,id:I,map:spec_fn(S)->S)->bool {
    forall|s:S| #[trigger] yields_related(eq,family,family(id,map(s)),family(id,s))
}
pub proof fn map_at<S>(eq:spec_fn(S,S)->bool,a:spec_fn(S)->S,b:spec_fn(S)->S,x:S,y:S)
    requires o::related_maps(eq,a,b),eq(x,y),
    ensures eq(a(x),b(y)),
{ }
pub proof fn commutes_at<S>(eq:spec_fn(S,S)->bool,a:spec_fn(S)->S,b:spec_fn(S)->S,x:S,y:S)
    requires commutes(eq,a,b),eq(x,y),
    ensures eq(a(b(x)),b(a(y))),
{ map_at(eq,f::compose(a,b),f::compose(b,a),x,y); }
pub proof fn stable_at<S,I>(eq:spec_fn(S,S)->bool,family:q::IteratorFamily<S,I>,id:I,map:spec_fn(S)->S,s:S)
    requires stable(eq,family,id,map),
    ensures yields_related(eq,family,family(id,map(s)),family(id,s)),
{ }
/// Both complete monoids are quantified, including yielded inverses of every
/// reachable iterator at every input; stability is required in both directions.
pub open spec fn independent<S,I,J>(eq:spec_fn(S,S)->bool,left:q::IteratorFamily<S,I>,i:I,right:q::IteratorFamily<S,J>,j:J)->bool {
    &&& forall|a:spec_fn(S)->S,b:spec_fn(S)->S| transforms(left,i,a) && transforms(right,j,b) ==> commutes(eq,a,b)
    &&& forall|k:I,b:spec_fn(S)->S| reach(left,i).contains(k) && transforms(right,j,b) ==> stable(eq,left,k,b)
    &&& forall|k:J,a:spec_fn(S)->S| reach(right,j).contains(k) && transforms(left,i,a) ==> stable(eq,right,k,a)
}
pub open spec fn pairwise<S,L,I>(eq:spec_fn(S,S)->bool,family:spec_fn(L)->q::IteratorFamily<S,I>,root:spec_fn(L)->I)->bool {
    forall|l:L,k:L| l!=k ==> #[trigger] independent(eq,family(l),root(l),family(k),root(k))
}

pub proof fn yields_transitive<S,I>(eq:spec_fn(S,S)->bool,family:q::IteratorFamily<S,I>,a:q::Iteration<S,I>,b:q::Iteration<S,I>,d:q::Iteration<S,I>)
    requires c::equivalence(eq),yields_related(eq,family,a,b),yields_related(eq,family,b,d),
    ensures yields_related(eq,family,a,d),
{
    o::map_partial_equivalence(eq,a.undo,b.undo,d.undo);
    match (a.next,b.next,d.next) {
        (Some(x),Some(y),Some(z))=>{q::iterator_partial_equivalence(eq,family,x,y,z);},
        _=>{},
    }
}

/// Root self-respect propagates through every possible continuation, including
/// infinite paths. This derives respect of all actual generator maps.
pub proof fn reachable_respects<S,I>(eq:spec_fn(S,S)->bool,family:q::IteratorFamily<S,I>,root:I,id:I)
    requires c::equivalence(eq),q::iterator_related(eq,family,root,root),reach(family,root).contains(id),
    ensures q::iterator_related(eq,family,id,id),
{
    let ids=ISet::new(|i:I|q::iterator_related(eq,family,i,i));
    q::greatest_bisimulation(eq,family);
    assert(closed(family,ids)) by {
        assert forall|i:I,s:S| ids.contains(i) && (#[trigger] family(i,s)).next.is_some()
            implies ids.contains(family(i,s).next.unwrap()) by {
            assert(eq(s,s));assert(q::iterator_related(eq,family,i,i));
            assert(q::continuation(|k:I,l:I|q::iterator_related(eq,family,k,l),family(i,s).next,family(i,s).next));
        }
    }
    reach_least_closed(family,root,ids);
}
pub proof fn generator_respects<S,I>(eq:spec_fn(S,S)->bool,family:q::IteratorFamily<S,I>,root:I,map:spec_fn(S)->S)
    requires c::equivalence(eq),q::iterator_related(eq,family,root,root),generators(family,root).contains(map),
    ensures o::related_maps(eq,map,map),
{
    let id=choose|id:I|reach(family,root).contains(id)
        && (map==forward(family,id) || exists|input:S| (#[trigger] family(id,input)).undo==map);
    reachable_respects(eq,family,root,id);q::iterator_unfolding(eq,family,id,id);
    if map==forward(family,id) {
        assert forall|a:S,b:S| eq(a,b) implies #[trigger] eq(map(a),map(b)) by {assert(eq(family(id,a).state,family(id,b).state));}
    } else {
        let input=choose|input:S| (#[trigger] family(id,input)).undo==map;
        assert(eq(input,input));assert(o::related_maps(eq,family(id,input).undo,family(id,input).undo));
    }
}

pub proof fn word_respects<S>(eq:spec_fn(S,S)->bool,word:Seq<spec_fn(S)->S>)
    requires forall|i:int|0<=i<word.len() ==> o::related_maps(eq,#[trigger] word[i],word[i]),
    ensures o::related_maps(eq,|s:S|c::run(word,s),|s:S|c::run(word,s)),
    decreases word.len(),
{
    if word.len()>0 {
        word_respects(eq,word.drop_last());
        assert forall|a:S,b:S| eq(a,b) implies #[trigger] eq(c::run(word,a),c::run(word,b)) by {
            map_at(eq,|s:S|c::run(word.drop_last(),s),|s:S|c::run(word.drop_last(),s),a,b);
            map_at(eq,word.last(),word.last(),c::run(word.drop_last(),a),c::run(word.drop_last(),b));
        }
    }
}
pub proof fn commute_composition<S>(eq:spec_fn(S,S)->bool,a:spec_fn(S)->S,b:spec_fn(S)->S,d:spec_fn(S)->S)
    requires c::equivalence(eq),commutes(eq,a,b),commutes(eq,a,d),o::related_maps(eq,b,b),o::related_maps(eq,d,d),
    ensures commutes(eq,a,f::compose(b,d)),
{
    assert forall|x:S,y:S| eq(x,y) implies #[trigger] eq(a(b(d(x))),b(d(a(y)))) by {
        map_at(eq,d,d,x,y);commutes_at(eq,a,b,d(x),d(y));
        assert(eq(y,y));commutes_at(eq,a,d,y,y);
        assert(eq(b(a(d(y))),b(d(a(y)))));
    }
}
pub proof fn commute_symmetric<S>(eq:spec_fn(S,S)->bool,a:spec_fn(S)->S,b:spec_fn(S)->S)
    requires c::equivalence(eq),commutes(eq,a,b),
    ensures commutes(eq,b,a),
{ o::map_partial_equivalence(eq,f::compose(a,b),f::compose(b,a),f::compose(b,a)); }
pub proof fn commute_word<S>(eq:spec_fn(S,S)->bool,a:spec_fn(S)->S,word:Seq<spec_fn(S)->S>)
    requires c::equivalence(eq),o::related_maps(eq,a,a),
        forall|i:int|0<=i<word.len() ==> commutes(eq,a,#[trigger] word[i]) && o::related_maps(eq,word[i],word[i]),
    ensures commutes(eq,a,|s:S|c::run(word,s)),
    decreases word.len(),
{
    if word.len()>0 {
        let prefix=word.drop_last();let last=word.last();
        commute_word(eq,a,prefix);word_respects(eq,prefix);
        commute_composition(eq,a,last,|s:S|c::run(prefix,s));
        assert((|s:S|c::run(word,s)) =~= f::compose(last,|s:S|c::run(prefix,s)));
    } else {assert((|s:S|c::run(word,s)) =~= (|s:S|s));}
}
pub proof fn generated_commutation<S>(eq:spec_fn(S,S)->bool,left:ISet<spec_fn(S)->S>,right:ISet<spec_fn(S)->S>,a:spec_fn(S)->S,b:spec_fn(S)->S)
    requires c::equivalence(eq),m::generated(left,a),m::generated(right,b),
        forall|f:spec_fn(S)->S| left.contains(f) || right.contains(f) ==> o::related_maps(eq,f,f),
        forall|f:spec_fn(S)->S,g:spec_fn(S)->S| left.contains(f) && right.contains(g) ==> commutes(eq,f,g),
    ensures commutes(eq,a,b),
{
    let xs=choose|word:Seq<spec_fn(S)->S>|m::represents(left,word,a);
    let ys=choose|word:Seq<spec_fn(S)->S>|m::represents(right,word,b);
    assert forall|i:int| 0<=i<xs.len() implies o::related_maps(eq,#[trigger] xs[i],xs[i]) by {}
    assert forall|j:int| 0<=j<ys.len() implies o::related_maps(eq,#[trigger] ys[j],ys[j]) by {}
    assert(a =~= (|s:S|c::run(xs,s)));
    assert(b =~= (|s:S|c::run(ys,s)));
    word_respects(eq,ys);
    assert(o::related_maps(eq,b,b));
    assert forall|i:int| 0<=i<xs.len() implies commutes(eq,b,#[trigger] xs[i]) && o::related_maps(eq,xs[i],xs[i]) by {
        assert forall|j:int| 0<=j<ys.len() implies commutes(eq,xs[i],#[trigger] ys[j]) && o::related_maps(eq,ys[j],ys[j]) by {}
        commute_word(eq,xs[i],ys);assert(commutes(eq,xs[i],b));commute_symmetric(eq,xs[i],b);
    }
    commute_word(eq,b,xs);assert(commutes(eq,b,a));commute_symmetric(eq,b,a);
}

pub proof fn stable_word<S,I>(eq:spec_fn(S,S)->bool,family:q::IteratorFamily<S,I>,id:I,word:Seq<spec_fn(S)->S>)
    requires c::equivalence(eq),q::iterator_related(eq,family,id,id),
        forall|i:int|0<=i<word.len() ==> stable(eq,family,id,#[trigger] word[i]),
    ensures stable(eq,family,id,|s:S|c::run(word,s)),
    decreases word.len(),
{
    q::iterator_unfolding(eq,family,id,id);
    if word.len()>0 {
        stable_word(eq,family,id,word.drop_last());
        assert forall|s:S| #[trigger] yields_related(eq,family,family(id,c::run(word,s)),family(id,s)) by {
            let middle=family(id,c::run(word.drop_last(),s));
            stable_at(eq,family,id,word.last(),c::run(word.drop_last(),s));
            stable_at(eq,family,id,|s:S|c::run(word.drop_last(),s),s);
            assert(yields_related(eq,family,family(id,c::run(word,s)),middle));
            yields_transitive(eq,family,family(id,c::run(word,s)),middle,family(id,s));
        }
    } else {
        assert forall|s:S| #[trigger] yields_related(eq,family,family(id,c::run(word,s)),family(id,s)) by {assert(eq(s,s));}
    }
}
pub open spec fn basis<S,I,J>(eq:spec_fn(S,S)->bool,left:q::IteratorFamily<S,I>,i:I,right:q::IteratorFamily<S,J>,j:J)->bool {
    &&& forall|a:spec_fn(S)->S,b:spec_fn(S)->S| generators(left,i).contains(a) && generators(right,j).contains(b) ==> commutes(eq,a,b)
    &&& forall|k:I,b:spec_fn(S)->S| reach(left,i).contains(k) && generators(right,j).contains(b) ==> stable(eq,left,k,b)
    &&& forall|k:J,a:spec_fn(S)->S| reach(right,j).contains(k) && generators(left,i).contains(a) ==> stable(eq,right,k,a)
}
/// Exact generator criterion, retaining quotient inverse and coinductive
/// continuation stability in both directions, not just forward commutation.
pub proof fn generator_criterion<S,I,J>(eq:spec_fn(S,S)->bool,left:q::IteratorFamily<S,I>,i:I,right:q::IteratorFamily<S,J>,j:J)
    requires c::equivalence(eq),q::iterator_related(eq,left,i,i),q::iterator_related(eq,right,j,j),
    ensures independent(eq,left,i,right,j)==basis(eq,left,i,right,j),
{
    let ls=generators(left,i);let rs=generators(right,j);
    if basis(eq,left,i,right,j) {
        assert forall|a:spec_fn(S)->S| ls.contains(a) || rs.contains(a) implies o::related_maps(eq,a,a) by {
            if ls.contains(a) {generator_respects(eq,left,i,a);} else {generator_respects(eq,right,j,a);}
        }
        assert forall|a:spec_fn(S)->S,b:spec_fn(S)->S| transforms(left,i,a) && transforms(right,j,b) implies commutes(eq,a,b) by {
            generated_commutation(eq,ls,rs,a,b);
        }
        assert forall|k:I,b:spec_fn(S)->S| reach(left,i).contains(k) && transforms(right,j,b) implies stable(eq,left,k,b) by {
            reachable_respects(eq,left,i,k);
            let word=choose|word:Seq<spec_fn(S)->S>|m::represents(rs,word,b);
            assert forall|n:int|0<=n<word.len() implies stable(eq,left,k,#[trigger] word[n]) by {}
            stable_word(eq,left,k,word);
        }
        assert forall|k:J,a:spec_fn(S)->S| reach(right,j).contains(k) && transforms(left,i,a) implies stable(eq,right,k,a) by {
            reachable_respects(eq,right,j,k);
            let word=choose|word:Seq<spec_fn(S)->S>|m::represents(ls,word,a);
            assert forall|n:int|0<=n<word.len() implies stable(eq,right,k,#[trigger] word[n]) by {}
            stable_word(eq,right,k,word);
        }
    } else if independent(eq,left,i,right,j) {
        assert forall|a:spec_fn(S)->S,b:spec_fn(S)->S| ls.contains(a) && rs.contains(b) implies commutes(eq,a,b) by {
            m::generator_member(ls,a);m::generator_member(rs,b);
        }
        assert forall|k:I,b:spec_fn(S)->S| reach(left,i).contains(k) && rs.contains(b) implies stable(eq,left,k,b) by {m::generator_member(rs,b);}
        assert forall|k:J,a:spec_fn(S)->S| reach(right,j).contains(k) && ls.contains(a) implies stable(eq,right,k,a) by {m::generator_member(ls,a);}
    }
}

pub proof fn actual_exchange<S,I,J>(eq:spec_fn(S,S)->bool,left:q::IteratorFamily<S,I>,i:I,right:q::IteratorFamily<S,J>,j:J,input:S)
    requires c::equivalence(eq),independent(eq,left,i,right,j),
    ensures eq(right(j,left(i,input).state).state,left(i,right(j,input).state).state),
        yields_related(eq,left,left(i,right(j,input).state),left(i,input)),
        yields_related(eq,right,right(j,left(i,input).state),right(j,input)),
        q::continuation(|x:I,y:I|q::iterator_related(eq,left,x,y),left(i,right(j,input).state).next,left(i,input).next),
        q::continuation(|x:J,y:J|q::iterator_related(eq,right,x,y),right(j,left(i,input).state).next,right(j,input).next),
{
    reach_least_closed(left,i,ISet::full());reach_least_closed(right,j,ISet::full());
    assert(generators(left,i).contains(forward(left,i)));assert(generators(right,j).contains(forward(right,j)));
    m::generator_member(generators(left,i),forward(left,i));m::generator_member(generators(right,j),forward(right,j));
    assert(commutes(eq,forward(left,i),forward(right,j)));assert(eq(input,input));
    assert(stable(eq,left,i,forward(right,j)));assert(stable(eq,right,j,forward(left,i)));
    commutes_at(eq,forward(left,i),forward(right,j),input,input);
    stable_at(eq,left,i,forward(right,j),input);stable_at(eq,right,j,forward(left,i),input);
}

pub proof fn independence_symmetric<S,I,J>(eq:spec_fn(S,S)->bool,left:q::IteratorFamily<S,I>,i:I,right:q::IteratorFamily<S,J>,j:J)
    requires c::equivalence(eq),independent(eq,left,i,right,j),
    ensures independent(eq,right,j,left,i),
{
    assert forall|a:spec_fn(S)->S,b:spec_fn(S)->S| transforms(right,j,a) && transforms(left,i,b) implies commutes(eq,a,b) by {
        commute_symmetric(eq,b,a);
    }
}

/// These two indices denote the same infinite behavior. A foreign transformation
/// changes the raw continuation bit but preserves the greatest bisimulation.
pub open spec fn parity_iterator(_id:bool,s:int)->q::Iteration<int,bool> {
    q::Iteration{state:s,undo:|x:int|x,next:Some(s%2==0)}
}
pub open spec fn increment_iterator(_id:(),s:int)->q::Iteration<int,()> {
    q::Iteration{state:s+1,undo:|x:int|x-1,next:None}
}
pub proof fn parity_bisimulation(a:bool,b:bool)
    ensures q::iterator_related(|x:int,y:int|x==y,|i:bool,s:int|parity_iterator(i,s),a,b),
{
    let family=|i:bool,s:int|parity_iterator(i,s);
    let relation=|_:bool,_:bool|true;
    assert(q::bisimulation(|x:int,y:int|x==y,family,relation));
    assert(relation(a,b));
}
pub proof fn quotient_continuation_example()
    ensures {
        let eq=|x:int,y:int|x==y;
        let family=|i:bool,s:int|parity_iterator(i,s);
        &&& independent(eq,family,true,|i:(),s:int|increment_iterator(i,s),())
        &&& family(true,1).next!=family(true,0).next
        &&& yields_related(eq,family,family(true,1),family(true,0))
    },
{
    let eq=|x:int,y:int|x==y;let left=|i:bool,s:int|parity_iterator(i,s);let right=|i:(),s:int|increment_iterator(i,s);
    parity_bisimulation(true,true);
    assert(q::bisimulation(eq,right,|_:(),_:()|true));
    assert(q::iterator_related(eq,right,(),()));
    assert forall|map:spec_fn(int)->int| generators(left,true).contains(map) implies f::maps_equal(map,|s:int|s) by {
        let id=choose|id:bool|reach(left,true).contains(id) && (map==forward(left,id) || exists|s:int| (#[trigger] left(id,s)).undo==map);
        if map!=forward(left,id) {let s=choose|s:int| (#[trigger] left(id,s)).undo==map;}
    }
    assert forall|map:spec_fn(int)->int| generators(right,()).contains(map) implies
        f::maps_equal(map,|s:int|s+1) || f::maps_equal(map,|s:int|s-1) by {
        let id=choose|id:()|reach(right,()).contains(id) && (map==forward(right,id) || exists|s:int| (#[trigger] right(id,s)).undo==map);
        if map!=forward(right,id) {let s=choose|s:int| (#[trigger] right(id,s)).undo==map;}
    }
    assert forall|a:spec_fn(int)->int,b:spec_fn(int)->int| generators(left,true).contains(a) && generators(right,()).contains(b) implies commutes(eq,a,b) by {
        assert(a =~= (|s:int|s));
        assert forall|x:int,y:int| eq(x,y) implies #[trigger] eq(a(b(x)),b(a(y))) by {assert(a(b(x))==b(x));assert(a(y)==y);}
    }
    assert forall|id:bool,map:spec_fn(int)->int| reach(left,true).contains(id) && generators(right,()).contains(map) implies stable(eq,left,id,map) by {
        assert forall|s:int| #[trigger] yields_related(eq,left,left(id,map(s)),left(id,s)) by {parity_bisimulation(map(s)%2==0,s%2==0);}
    }
    assert forall|id:(),map:spec_fn(int)->int| reach(right,()).contains(id) && generators(left,true).contains(map) implies stable(eq,right,id,map) by {
        assert(map =~= (|s:int|s));
    }
    assert(basis(eq,left,true,right,()));generator_criterion(eq,left,true,right,());
    parity_bisimulation(false,true);
}

} // verus!
