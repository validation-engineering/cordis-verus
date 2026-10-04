//! Theorem 43 on observational witnesses and actual returned inverses.
//! Quotient classes turn respecting maps into literal maps on observations;
//! hidden representatives and state-dependent inverses need not be equal.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, foundations as f, history as h, iterator_independence as ind, monoid as m,
    observation as o, permutation as p, quotient as q,
};
use vstd::prelude::*;
verus! {
pub open spec fn class<S>(eq:spec_fn(S,S)->bool,x:S)->ISet<S> { ISet::new(|y:S|eq(x,y)) }
pub proof fn classes<S>(eq:spec_fn(S,S)->bool,x:S,y:S)
    requires c::equivalence(eq), ensures (class(eq,x)==class(eq,y))==eq(x,y),
{
    if eq(x,y) { assert(class(eq,x) =~= class(eq,y)); }
    if class(eq,x)==class(eq,y) { assert(class(eq,y).contains(y));assert(class(eq,x).contains(y)); }
}
pub open spec fn quotient_map<S>(eq:spec_fn(S,S)->bool,map:spec_fn(S)->S,a:ISet<S>)->ISet<S> {
    if exists|x:S| a.contains(x) {class(eq,map(choose|x:S|a.contains(x)))} else {ISet::empty()}
}
pub proof fn map_class<S>(eq:spec_fn(S,S)->bool,map:spec_fn(S)->S,x:S)
    requires c::equivalence(eq),o::related_maps(eq,map,map),
    ensures quotient_map(eq,map,class(eq,x))==class(eq,map(x)),
{
    let a=class(eq,x);assert(a.contains(x));let y=choose|y:S|a.contains(y);
    assert(eq(x,y));assert(eq(map(x),map(y)));classes(eq,map(x),map(y));
}
pub open spec fn lift_word<S>(eq:spec_fn(S,S)->bool,maps:Seq<spec_fn(S)->S>)->Seq<spec_fn(ISet<S>)->ISet<S>> {
    maps.map(|i:int,map:spec_fn(S)->S| |a:ISet<S>|quotient_map(eq,map,a))
}
pub open spec fn respectful<S>(eq:spec_fn(S,S)->bool,maps:Seq<spec_fn(S)->S>)->bool {
    forall|i:int|0<=i<maps.len() ==> o::related_maps(eq,#[trigger] maps[i],maps[i])
}
pub open spec fn commuting<S>(eq:spec_fn(S,S)->bool,maps:Seq<spec_fn(S)->S>)->bool {
    forall|i:int,j:int|0<=i<maps.len() && 0<=j<maps.len() && i!=j ==> ind::commutes(eq,#[trigger] maps[i],#[trigger] maps[j])
}
pub proof fn run_classes<S>(eq:spec_fn(S,S)->bool,maps:Seq<spec_fn(S)->S>,x:S)
    requires c::equivalence(eq),respectful(eq,maps),
    ensures c::run(lift_word(eq,maps),class(eq,x))==class(eq,c::run(maps,x)), decreases maps.len(),
{
    if maps.len()>0 {
        run_classes(eq,maps.drop_last(),x);
        assert(lift_word(eq,maps).drop_last() =~= lift_word(eq,maps.drop_last()));
        map_class(eq,maps.last(),c::run(maps.drop_last(),x));
    }
}
pub proof fn quotient_commutation<S>(eq:spec_fn(S,S)->bool,left:spec_fn(S)->S,right:spec_fn(S)->S,a:ISet<S>)
    requires c::equivalence(eq),o::related_maps(eq,left,left),o::related_maps(eq,right,right),ind::commutes(eq,left,right),
    ensures quotient_map(eq,left,quotient_map(eq,right,a))==quotient_map(eq,right,quotient_map(eq,left,a)),
{
    if exists|x:S|a.contains(x) {
        let x=choose|x:S|a.contains(x);
        map_class(eq,left,right(x));map_class(eq,right,left(x));
        ind::commutes_at(eq,left,right,x,x);classes(eq,left(right(x)),right(left(x)));
    } else { assert(!(exists|x:S|ISet::<S>::empty().contains(x))); }
}
pub proof fn selected_classes<S>(eq:spec_fn(S,S)->bool,maps:Seq<spec_fn(S)->S>,order:Seq<nat>)
    requires respectful(eq,maps),forall|i:int|0<=i<order.len() ==> #[trigger] order[i]<maps.len(),
    ensures respectful(eq,p::selected(maps,order)),p::selected(lift_word(eq,maps),order)==lift_word(eq,p::selected(maps,order)),
{ assert(p::selected(lift_word(eq,maps),order) =~= lift_word(eq,p::selected(maps,order))); }
/// Range, coverage and no duplicates determine a permutation. Commutation is
/// required at distinct indices; the maps themselves may be equal.
pub proof fn permutation_execution<S>(eq:spec_fn(S,S)->bool,maps:Seq<spec_fn(S)->S>,left:Seq<nat>,right:Seq<nat>,x:S)
    requires c::equivalence(eq),respectful(eq,maps),commuting(eq,maps),p::permutation(left,maps.len()),p::permutation(right,maps.len()),
    ensures eq(c::run(p::selected(maps,left),x),c::run(p::selected(maps,right),x)),
{
    let lifted=lift_word(eq,maps);
    assert forall|i:int,j:int|0<=i<lifted.len() && 0<=j<lifted.len() && i!=j implies #[trigger] h::commutes(lifted[i],lifted[j]) by {
        assert forall|a:ISet<S>| #[trigger] (lifted[i])((lifted[j])(a))==(lifted[j])((lifted[i])(a)) by {quotient_commutation(eq,maps[i],maps[j],a);}
    }
    p::permutation_execution(lifted,left,right,class(eq,x));
    selected_classes(eq,maps,left);selected_classes(eq,maps,right);
    run_classes(eq,p::selected(maps,left),x);run_classes(eq,p::selected(maps,right),x);
    classes(eq,c::run(p::selected(maps,left),x),c::run(p::selected(maps,right),x));
}
pub open spec fn effect<S>(step:h::IteratorStep<S>)->spec_fn(S)->f::Tracked<S> { |x:S|f::Tracked{value:step(x).0,undo:step(x).1} }
pub open spec fn witnessed<S>(eq:spec_fn(S,S)->bool,effects:Seq<h::IteratorStep<S>>)->bool {
    forall|i:int|0<=i<effects.len() ==> o::witnessed_effect(eq,effect(#[trigger] effects[i]))
}
pub proof fn returned_respects<S>(eq:spec_fn(S,S)->bool,effects:Seq<h::IteratorStep<S>>,x:S)
    requires c::equivalence(eq),witnessed(eq,effects), ensures respectful(eq,p::returned(effects,x)),
{
    p::returned_length(effects,x);
    assert forall|i:int|0<=i<p::returned(effects,x).len() implies o::related_maps(eq,#[trigger] p::returned(effects,x)[i],p::returned(effects,x)[i]) by {
        p::returned_origin(effects,x,i);let input=choose|input:S|(#[trigger] (effects[i])(input)).1==p::returned(effects,x)[i];
        assert(eq(input,input));assert(o::witnessed_effect(eq,effect(effects[i])));
        assert(o::related_maps(eq,(effect(effects[i])(input)).undo,(effect(effects[i])(input)).undo));
    }
}
pub proof fn dynamic_recovery<S>(eq:spec_fn(S,S)->bool,effects:Seq<h::IteratorStep<S>>,x:S)
    requires c::equivalence(eq),witnessed(eq,effects),
    ensures eq(c::unwind(p::returned(effects,x),p::apply(effects,x)),x), decreases effects.len(),
{
    if effects.len()>0 {
        let prefix=effects.drop_last();let before=p::apply(prefix,x);let out=(effects.last())(before);
        let e=effect(effects.last());assert(o::witnessed_effect(eq,e));assert(eq((e(before).undo)(e(before).value),before));assert(eq((out.1)(out.0),before));
        returned_respects(eq,prefix,x);c::unwind_respects(p::returned(prefix,x),eq,(out.1)(out.0),before);
        dynamic_recovery(eq,prefix,x);assert(p::returned(effects,x).drop_last() =~= p::returned(prefix,x));
    }
}
/// A weaker sufficient condition: only the actual yielded inverses commute.
pub proof fn actual_inverse_recovery<S>(eq:spec_fn(S,S)->bool,effects:Seq<h::IteratorStep<S>>,x:S,order:Seq<nat>)
    requires c::equivalence(eq),witnessed(eq,effects),commuting(eq,p::returned(effects,x)),p::permutation(order,effects.len()),
    ensures eq(c::run(p::selected(p::returned(effects,x),order),p::apply(effects,x)),x),
{
    let inverses=p::returned(effects,x);p::returned_length(effects,x);returned_respects(eq,effects,x);dynamic_recovery(eq,effects,x);
    p::reverse_permutation(inverses);permutation_execution(eq,inverses,order,p::reverse_indices(inverses.len()),p::apply(effects,x));
    h::inverse_history(inverses,p::apply(effects,x));
}
pub open spec fn family<S>(step:h::IteratorStep<S>)->q::IteratorFamily<S,()> { |id:(),x:S|q::Iteration {state:step(x).0,undo:step(x).1,next:None} }
pub open spec fn independent<S>(eq:spec_fn(S,S)->bool,effects:Seq<h::IteratorStep<S>>)->bool {
    forall|i:int,j:int|0<=i<effects.len() && 0<=j<effects.len() && i!=j
        ==> ind::independent(eq,family(#[trigger] effects[i]),(),family(#[trigger] effects[j]),())
}
#[verifier::spinoff_prover]
pub proof fn inverse_generator<S>(step:h::IteratorStep<S>,input:S)
    ensures ind::transforms(family(step),(),step(input).1),
{
    let fam=family(step);let root=();let inverse=step(input).1;
    ind::reach_least_closed(fam,root,ISet::full());
    assert(ind::reach(fam,root).contains(root));
    assert(fam(root,input).undo==inverse);
    assert(exists|x:S|(#[trigger] fam(root,x)).undo==inverse);
    assert(ind::reach(fam,root).contains(root) && (inverse==ind::forward(fam,root) || exists|x:S|(#[trigger] fam(root,x)).undo==inverse));
    let candidate=|id:()|ind::reach(fam,root).contains(id) && (inverse==ind::forward(fam,id) || exists|x:S|(#[trigger] fam(id,x)).undo==inverse);
    assert(candidate(root));assert(exists|id:()|#[trigger] candidate(id));
    let gen=ind::generators(fam,root);
    assert(gen.contains(inverse)) by { if !gen.contains(inverse) {assert(!candidate(root));} }
    m::generator_member(gen,inverse);
}
pub proof fn independent_returns<S>(eq:spec_fn(S,S)->bool,effects:Seq<h::IteratorStep<S>>,x:S)
    requires independent(eq,effects), ensures commuting(eq,p::returned(effects,x)),
{
    p::returned_length(effects,x);
    assert forall|i:int,j:int|0<=i<p::returned(effects,x).len() && 0<=j<p::returned(effects,x).len() && i!=j
        implies ind::commutes(eq,#[trigger] p::returned(effects,x)[i],#[trigger] p::returned(effects,x)[j]) by {
        p::returned_origin(effects,x,i);p::returned_origin(effects,x,j);
        let a=choose|input:S|(#[trigger] (effects[i])(input)).1==p::returned(effects,x)[i];
        let b=choose|input:S|(#[trigger] (effects[j])(input)).1==p::returned(effects,x)[j];
        inverse_generator(effects[i],a);inverse_generator(effects[j],b);assert(ind::independent(eq,family(effects[i]),(),family(effects[j]),()));
    }
}
/// Theorem 43 on Definition 36 observations and Definition 42 independence.
pub proof fn arbitrary_inverse_recovery<S>(eq:spec_fn(S,S)->bool,effects:Seq<h::IteratorStep<S>>,x:S,order:Seq<nat>)
    requires c::equivalence(eq),witnessed(eq,effects),independent(eq,effects),p::permutation(order,effects.len()),
    ensures eq(c::run(p::selected(p::returned(effects,x),order),p::apply(effects,x)),x),
{ independent_returns(eq,effects,x);actual_inverse_recovery(eq,effects,x,order); }
pub open spec fn hidden(value:int)->h::IteratorStep<(int,int)> {
    |x:(int,int)| ((x.0,value),|y:(int,int)|(y.0,value),None)
}
pub open spec fn visible_eq()->spec_fn((int,int),(int,int))->bool { |a:(int,int),b:(int,int)|a.0==b.0 }
pub open spec fn visible(a:(int,int),b:(int,int))->bool { a.0==b.0 }
/// The actual inverses restore the visible field, but neither their commutation
/// nor their restoration is literal equality of the whole state.
pub proof fn nonliteral_example()
    ensures {
        let effects=seq![hidden(17),hidden(29)];let x=(7int,99int);
        let inverses=p::returned(effects,x);let final_state=p::apply(effects,x);
        &&& witnessed(visible_eq(),effects) && commuting(visible_eq(),inverses)
        &&& visible(c::run(p::selected(inverses,seq![0nat,1nat]),final_state),x)
        &&& visible(c::run(p::selected(inverses,seq![1nat,0nat]),final_state),x)
        &&& c::run(p::selected(inverses,seq![0nat,1nat]),final_state)!=x
        &&& c::run(p::selected(inverses,seq![0nat,1nat]),final_state)
            !=c::run(p::selected(inverses,seq![1nat,0nat]),final_state)
    },
{
    let effects=seq![hidden(17),hidden(29)];let x=(7int,99int);
    let inverses=p::returned(effects,x);let final_state=p::apply(effects,x);
    assert(c::equivalence(visible_eq()));
    assert forall|i:int|0<=i<effects.len() implies o::witnessed_effect(visible_eq(),effect(#[trigger] effects[i])) by {
        if i==0 {assert(effects[i]==hidden(17));} else {assert(i==1);assert(effects[i]==hidden(29));}
    }
    reveal_with_fuel(p::returned,3);reveal_with_fuel(p::apply,3);reveal_with_fuel(c::run,3);
    assert(inverses.len()==2);assert(final_state==(7int,29int));
    assert forall|i:int,j:int|0<=i<inverses.len() && 0<=j<inverses.len() && i!=j
        implies ind::commutes(visible_eq(),#[trigger] inverses[i],#[trigger] inverses[j]) by {
        assert((i==0 && j==1)||(i==1 && j==0));
    }
    assert(p::permutation(seq![0nat,1nat],2));assert(p::permutation(seq![1nat,0nat],2));
    actual_inverse_recovery(visible_eq(),effects,x,seq![0nat,1nat]);actual_inverse_recovery(visible_eq(),effects,x,seq![1nat,0nat]);
}
} // verus!
