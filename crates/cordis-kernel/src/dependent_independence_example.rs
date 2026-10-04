//! Shared-key translations with unrelated, non-enumerated continuation types.
//!
//! Left yields int outcomes; right yields bool outcomes. Their next indices
//! contain respectively an arbitrary predicate and an arbitrary set of ints.
//! The generic theorem uses those indices directly, with no enumeration map.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_independence as proof, iterator_bridge as ib, mediated as m,
    observational_grammar as og, partial_independence as p,
};
use vstd::prelude::*;

verus! {

pub type LeftIndex=(bool,spec_fn(int)->bool);
pub type RightIndex=(bool,ISet<int>);
pub open spec fn equality()->spec_fn((),int,int)->bool {|_:(),a:int,b:int|a==b}
pub open spec fn translation<B>(amount:int,outcome:B)->m::Operation<int,B> {
    |before:int|Some(m::ValueYield {value:before+amount,undo:|after:int|Some(after-amount),outcome})
}
pub open spec fn shift(amount:int)->m::PartialMap<int> {|v:int|Some(v+amount)}
pub proof fn translation_generators<B>(amount:int,outcome:B,f:m::PartialMap<int>)
    requires p::value_generators(translation(amount,outcome)).contains(f),
    ensures f==shift(amount) || f==shift(-amount),
{
    let op=translation(amount,outcome);
    if f==p::value_forward(op) {assert(f =~= shift(amount));}
    else {let before=choose|v:int| #[trigger] op(v).is_some() && op(v).unwrap().undo==f;assert(f =~= shift(-amount));}
}
pub proof fn translation_independent<B,C>(a:int,b:int,x:B,y:C)
    ensures p::value_independent(|u:int,v:int|u==v,translation(a,x),translation(b,y)),
{
    let eq=|u:int,v:int|u==v;let left=translation(a,x);let right=translation(b,y);
    assert forall|f:m::PartialMap<int>,g:m::PartialMap<int>|p::value_generators(left).contains(f) && p::value_generators(right).contains(g)
        implies #[trigger] p::commutes(eq,f,g) by {
        translation_generators(a,x,f);translation_generators(b,y,g);
        assert forall|v:int| #[trigger] p::optional_equal(eq,p::compose(f,g)(v),p::compose(g,f)(v)) by {}
    }
    assert forall|g:m::PartialMap<int>|p::value_generators(right).contains(g) implies #[trigger] p::value_stable(eq,left,g) by {
        assert forall|v:int| #[trigger] g(v).is_some() implies {
            &&& left(v).is_some()==left(g(v).unwrap()).is_some()
            &&& (left(v).is_some() ==> left(v).unwrap().outcome==left(g(v).unwrap()).unwrap().outcome
                && m::partial_related(eq,left(v).unwrap().undo,left(g(v).unwrap()).unwrap().undo))
        } by {}
    }
    assert forall|f:m::PartialMap<int>|p::value_generators(left).contains(f) implies #[trigger] p::value_stable(eq,right,f) by {
        assert forall|v:int| #[trigger] f(v).is_some() implies {
            &&& right(v).is_some()==right(f(v).unwrap()).is_some()
            &&& (right(v).is_some() ==> right(v).unwrap().outcome==right(f(v).unwrap()).unwrap().outcome
                && m::partial_related(eq,right(v).unwrap().undo,right(f(v).unwrap()).unwrap().undo))
        } by {}
    }
}
pub open spec fn left_library()->d::Library<(),(),int,int,int> {
    d::Library {values:|_:(),_:int|true,arguments:|_:(),_:int|true,outcomes:|_:(),_:int|true,
        key:|_:()|(),allowed:ISet::full(),apply:|_:(),amount:int|translation(amount,amount)}
}
pub open spec fn right_library()->d::Library<(),bool,int,int,bool> {
    d::Library {values:|_:(),_:int|true,arguments:|_:bool,_:int|true,outcomes:|_:bool,_:bool|true,
        key:|_:bool|(),allowed:ISet::full(),apply:|op:bool,amount:int|translation(amount,op)}
}
pub open spec fn left_program()->d::Program<(),(),int,int,int,LeftIndex> {
    |id:LeftIndex|if id.0 {d::Node::Operation {operation:(),argument:5,
        select:|out:int|Some((false,|v:int|v==out))}}
    else {d::Node::Unit}
}
pub open spec fn right_program()->d::Program<(),bool,int,int,bool,RightIndex> {
    |id:RightIndex|if id.0 {d::Node::Operation {operation:true,argument:7,
        select:|out:bool|Some((false,if out {ISet::full()} else {ISet::empty()}))}}
    else {d::Node::Unit}
}
pub open spec fn left(predicate:spec_fn(int)->bool)->proof::Grammar<(),(),int,int,int,LeftIndex> {
    proof::Grammar {library:left_library(),program:left_program(),keys:ISet::full(),provisions:ISet::empty(),root:(true,predicate)}
}
pub open spec fn right(set:ISet<int>)->proof::Grammar<(),bool,int,int,bool,RightIndex> {
    proof::Grammar {library:right_library(),program:right_program(),keys:ISet::full(),provisions:ISet::empty(),root:(true,set)}
}
pub proof fn primitives()
    ensures og::primitive_theory(equality(),left_library()),og::primitive_theory(equality(),right_library()),
{
    let l=left_library();let r=right_library();let eq=equality();
    assert forall|op:(),amount:int|l.allowed.contains(op) && (l.arguments)(op,amount) implies
        #[trigger] d::operation_typed(l,op,amount) && og::operation_admissible(|u:int,v:int|eq((l.key)(op),u,v),(l.apply)(op,amount)) by {}
    assert forall|op:bool,amount:int|r.allowed.contains(op) && (r.arguments)(op,amount) implies
        #[trigger] d::operation_typed(r,op,amount) && og::operation_admissible(|u:int,v:int|eq((r.key)(op),u,v),(r.apply)(op,amount)) by {}
}
pub proof fn grammars(predicate:spec_fn(int)->bool,set:ISet<int>)
    ensures proof::valid(equality(),left(predicate)),proof::valid(equality(),right(set)),
        proof::separated(left(predicate),right(set)),proof::witnessed_keys(equality(),left(predicate),right(set)),
{
    primitives();let l=left(predicate);let r=right(set);
    assert forall|id:LeftIndex|!id.0 implies d::member(l.library,l.program,l.keys,l.provisions,id) by {d::constructor_member(l.library,l.program,l.keys,l.provisions,id);}
    assert forall|id:RightIndex|!id.0 implies d::member(r.library,r.program,r.keys,r.provisions,id) by {d::constructor_member(r.library,r.program,r.keys,r.provisions,id);}
    d::constructor_member(l.library,l.program,l.keys,l.provisions,l.root);d::constructor_member(r.library,r.program,r.keys,r.provisions,r.root);
    assert forall|a:(),x:int,b:bool,y:int| #![trigger (l.library.apply)(a,x),(r.library.apply)(b,y)]
        l.library.allowed.contains(a) && (l.library.arguments)(a,x) && r.library.allowed.contains(b) && (r.library.arguments)(b,y)
        && l.keys.contains((l.library.key)(a)) && r.keys.contains((r.library.key)(b)) && (l.library.key)(a)==(r.library.key)(b)
        implies p::value_independent(|u:int,v:int|equality()((l.library.key)(a),u,v),(l.library.apply)(a,x),(r.library.apply)(b,y)) by {translation_independent(x,y,x,b);}
}
/// Both actual translations execute on the same key, yield genuinely different
/// outcome types, and keep the typed predicate/set continuation payloads.
pub proof fn arbitrary_index_example(predicate:spec_fn(int)->bool,set:ISet<int>)
    ensures ib::independent(proof::equality(equality()),d::family(left_library(),left_program()),(true,predicate),d::family(right_library(),right_program()),(true,set)),
        {
            let input=Map::<(),int>::empty().insert((),10);let a=d::run(left_library(),left_program()((true,predicate)),input).unwrap();
            let b=d::run(right_library(),right_program()((true,set)),a.state).unwrap();
            &&& d::run(left_library(),left_program()((true,predicate)),input).is_some()
            &&& d::run(right_library(),right_program()((true,set)),a.state).is_some()
            &&& a.state[()]==15 && b.state[()]==22 && a.next.is_some() && b.next.is_some()
            &&& !a.next.unwrap().0 && a.next.unwrap().1(5) && !a.next.unwrap().1(7)
            &&& !b.next.unwrap().0 && b.next.unwrap().1==ISet::<int>::full()
            &&& d::run(left_library(),left_program()((true,predicate)),Map::empty()).is_none()
            &&& (a.undo)((b.undo)(b.state).unwrap())==Some(input)
        },
{
    grammars(predicate,set);proof::grammar_independence(equality(),left(predicate),right(set));
    let input=Map::<(),int>::empty().insert((),10);
    assert(input.insert((),15).insert((),22).insert((),15).insert((),10) =~= input);
}
}
