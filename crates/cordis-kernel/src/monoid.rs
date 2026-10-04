//! Reachable continuations and finite-word generated transformation monoids.
//! Closure is unrestricted by an iterator rank or by a particular execution.
use vstd::prelude::*;
verus! {
pub type Family<S,I> = spec_fn(I)->crate::history::IteratorStep<S>;
pub open spec fn closed<S>(family:Family<S,nat>,set:ISet<nat>) -> bool {
    forall|i:nat,s:S| set.contains(i) && (#[trigger] family(i)(s)).2.is_some()
        ==> set.contains(family(i)(s).2.unwrap())
}
pub open spec fn reach<S>(family:Family<S,nat>,root:nat) -> ISet<nat> {
    ISet::new(|i:nat| forall|set:ISet<nat>| #[trigger] set.contains(root) && closed(family,set) ==> set.contains(i))
}
pub proof fn reach_least_closed<S>(family:Family<S,nat>,root:nat,set:ISet<nat>)
    ensures reach(family,root).contains(root), closed(family,reach(family,root)),
        set.contains(root) && closed(family,set) ==> reach(family,root).subset_of(set),
{
    assert forall|i:nat,s:S| reach(family,root).contains(i) && (#[trigger] family(i)(s)).2.is_some()
        implies reach(family,root).contains(family(i)(s).2.unwrap()) by {
        let next=family(i)(s).2.unwrap();
        assert forall|candidate:ISet<nat>| #[trigger] candidate.contains(root) && closed(family,candidate)
            implies candidate.contains(next) by {
            assert(candidate.contains(i));
            assert(candidate.contains(next));
        }
    }
}
pub open spec fn represents<S>(generators:ISet<spec_fn(S)->S>,word:Seq<spec_fn(S)->S>,f:spec_fn(S)->S) -> bool {
    (forall|i:int| 0<=i<word.len() ==> generators.contains(#[trigger] word[i]))
        && crate::foundations::maps_equal(f,|s:S|crate::calculus::run(word,s))
}
pub open spec fn generated<S>(generators:ISet<spec_fn(S)->S>,f:spec_fn(S)->S) -> bool {
    exists|word:Seq<spec_fn(S)->S>| #[trigger] represents(generators,word,f)
}
pub proof fn generator_member<S>(generators:ISet<spec_fn(S)->S>,f:spec_fn(S)->S)
    requires generators.contains(f),
    ensures generated(generators,f),
{
    let word=seq![f];
    assert(word.drop_last() =~= Seq::<spec_fn(S)->S>::empty());
    assert(word.last()==f);
    assert forall|s:S| #[trigger] f(s)==crate::calculus::run(word,s) by { reveal_with_fuel(crate::calculus::run,2); }
    assert(represents(generators,word,f));
}
pub proof fn monoid_unit<S>(generators:ISet<spec_fn(S)->S>)
    ensures generated(generators,|s:S|s),
{
    let word=Seq::<spec_fn(S)->S>::empty();
    assert(represents(generators,word,|s:S|s));
}
pub proof fn monoid_composition<S>(generators:ISet<spec_fn(S)->S>,f:spec_fn(S)->S,g:spec_fn(S)->S)
    requires generated(generators,f),generated(generators,g),
    ensures generated(generators,crate::foundations::compose(f,g)),
{
    let left=choose|word:Seq<spec_fn(S)->S>| represents(generators,word,f);
    let right=choose|word:Seq<spec_fn(S)->S>| represents(generators,word,g);
    let word=right+left;
    assert forall|i:int| 0<=i<word.len() implies generators.contains(#[trigger] word[i]) by {
        if i<right.len() {assert(word[i]==right[i]);} else {assert(word[i]==left[i-right.len()]);}
    }
    assert forall|s:S| #[trigger] crate::foundations::compose(f,g)(s)==crate::calculus::run(word,s) by {
        crate::history::run_concatenation(right,left,s);
    }
    assert(represents(generators,word,crate::foundations::compose(f,g)));
}

/// Lemma 41(1): it suffices to check primitive generators, including inverses.
pub proof fn generator_commutation<S>(left:ISet<spec_fn(S)->S>,right:ISet<spec_fn(S)->S>,
    f:spec_fn(S)->S,g:spec_fn(S)->S)
    requires generated(left,f),generated(right,g),
        forall|a:spec_fn(S)->S,b:spec_fn(S)->S| left.contains(a) && right.contains(b)
            ==> #[trigger] crate::history::commutes(a,b),
    ensures crate::history::commutes(f,g),
{
    let xs=choose|word:Seq<spec_fn(S)->S>| represents(left,word,f);
    let ys=choose|word:Seq<spec_fn(S)->S>| represents(right,word,g);
    assert forall|i:int,j:int,s:S| 0<=i<xs.len() && 0<=j<ys.len()
        implies #[trigger] (xs[i])((ys[j])(s))==(ys[j])((xs[i])(s)) by {
        assert(crate::history::commutes(xs[i],ys[j]));
    }
    assert forall|s:S| #[trigger] f(g(s))==g(f(s)) by {
        crate::calculus::independent_groups(xs,ys,s);
    }
}

/// Definition 42(2) lifts from generators to their entire monoid as well.
pub proof fn generator_stability<S>(step:crate::history::IteratorStep<S>,generators:ISet<spec_fn(S)->S>,f:spec_fn(S)->S)
    requires generated(generators,f),
        forall|g:spec_fn(S)->S| generators.contains(g) ==> #[trigger] crate::history::stable_yield(step,g),
    ensures crate::history::stable_yield(step,f),
{
    let word=choose|word:Seq<spec_fn(S)->S>| represents(generators,word,f);
    assert forall|i:int| 0<=i<word.len() implies crate::history::stable_yield(step,#[trigger] word[i]) by { }
    assert forall|s:S| {
        let result=#[trigger] step(f(s));
        &&& result.1==step(s).1
        &&& result.2==step(s).2
    } by {crate::history::yield_stability_sequence(step,word,s);}
}
pub open spec fn effect_generators<S>(e:spec_fn(S)->crate::foundations::Tracked<S>) -> ISet<spec_fn(S)->S> {
    ISet::new(|f:spec_fn(S)->S| f==(|s:S|e(s).value) || exists|s:S| (#[trigger] e(s)).undo==f)
}
/// Lemma 41(2), including the inverses evaluated at their actual yield states.
pub proof fn composed_generators<S>(a:spec_fn(S)->crate::foundations::Tracked<S>,
    b:spec_fn(S)->crate::foundations::Tracked<S>,f:spec_fn(S)->S)
    requires effect_generators(|s:S|crate::foundations::diamond(a,b,s)).contains(f),
    ensures generated(effect_generators(a).union(effect_generators(b)),f),
{
    let joint=effect_generators(a).union(effect_generators(b));
    let e=|s:S|crate::foundations::diamond(a,b,s);
    if f==(|s:S|e(s).value) {
        let af=|s:S|a(s).value;let bf=|s:S|b(s).value;
        generator_member(joint,af);generator_member(joint,bf);monoid_composition(joint,af,bf);
        assert(f =~= crate::foundations::compose(af,bf));
    } else {
        let s=choose|s:S| (#[trigger] e(s)).undo==f;
        let bi=b(s).undo;let ai=a(b(s).value).undo;
        assert(effect_generators(b).contains(bi));assert(effect_generators(a).contains(ai));
        generator_member(joint,bi);generator_member(joint,ai);monoid_composition(joint,bi,ai);
    }
}

pub proof fn generated_word<S>(generators:ISet<spec_fn(S)->S>,word:Seq<spec_fn(S)->S>)
    requires forall|i:int| 0<=i<word.len() ==> generated(generators,#[trigger] word[i]),
    ensures generated(generators,|s:S|crate::calculus::run(word,s)),
    decreases word.len(),
{
    if word.len()==0 {
        monoid_unit(generators);
        assert((|s:S|crate::calculus::run(word,s)) =~= (|s:S|s));
    } else {
        let prefix=word.drop_last();
        generated_word(generators,prefix);
        monoid_composition(generators,word.last(),|s:S|crate::calculus::run(prefix,s));
        assert((|s:S|crate::calculus::run(word,s)) =~=
            crate::foundations::compose(word.last(),|s:S|crate::calculus::run(prefix,s)));
    }
}
pub proof fn generated_substitution<S>(left:ISet<spec_fn(S)->S>,right:ISet<spec_fn(S)->S>,f:spec_fn(S)->S)
    requires generated(left,f),
        forall|g:spec_fn(S)->S| left.contains(g) ==> #[trigger] generated(right,g),
    ensures generated(right,f),
{
    let word=choose|word:Seq<spec_fn(S)->S>| represents(left,word,f);
    assert forall|i:int| 0<=i<word.len() implies generated(right,#[trigger] word[i]) by { }
    generated_word(right,word);
    assert(f =~= (|s:S|crate::calculus::run(word,s)));
}
/// The whole inclusion of Lemma 41(2), beyond inclusion of its generators.
pub proof fn composed_monoid<S>(a:spec_fn(S)->crate::foundations::Tracked<S>,
    b:spec_fn(S)->crate::foundations::Tracked<S>,f:spec_fn(S)->S)
    requires generated(effect_generators(|s:S|crate::foundations::diamond(a,b,s)),f),
    ensures generated(effect_generators(a).union(effect_generators(b)),f),
{
    let source=effect_generators(|s:S|crate::foundations::diamond(a,b,s));
    let target=effect_generators(a).union(effect_generators(b));
    assert forall|g:spec_fn(S)->S| source.contains(g) implies #[trigger] generated(target,g) by {
        composed_generators(a,b,g);
    }
    generated_substitution(source,target,f);
}
} // verus!
