//! Scalar recovery interface for the executable Mixed/Fresh Xor library.
//!
//! Both the actual forward operation and its returned inverse are the same
//! mask transformation. Their bit-vector commutation supplies the value replay
//! theorem's scalar premise; this does not assert lifecycle guard commutation.
#[cfg(verus_keep_ghost)]
use crate::{grammar_recovery as gr, mixed_driver as md, Port};
use vstd::prelude::*;

verus! {

pub open spec fn value_xor(mask:u64)->spec_fn(u64)->u64 {|value:u64|value^mask}

/// Classify generators from the real interpreter's library, including every
/// inverse returned at every input value, rather than a separate example model.
pub proof fn generator_is_xor(key:Port,f:spec_fn(u64)->u64)
    requires gr::generator(md::library(),key,f),
    ensures exists|mask:u64| f==#[trigger] value_xor(mask),
{
    let lib=md::library();
    let (operation,mask)=choose|operation:Port,mask:u64|
        lib.allowed.contains(operation) && #[trigger] (lib.arguments)(operation,mask)
        && (lib.key)(operation)==key && {
            let call=(lib.apply)(operation,mask);
            f==gr::forward(call) || exists|value:u64| #[trigger] call(value).is_some()
                && f==gr::total(call(value).unwrap().undo)
        };
    let call=md::xor_operation(mask);
    if f==gr::forward(call) {
        assert(f =~= value_xor(mask));
    } else {
        let before=choose|value:u64| #[trigger] call(value).is_some()
            && f==gr::total(call(value).unwrap().undo);
        assert(f =~= value_xor(mask));
    }
}

/// All actual masks commute at the value level, including zero and u64::MAX.
/// Neither a commutation assumption nor an empty operation library is supplied.
pub proof fn scalar_interface()
    ensures gr::independent_keys(md::library()),
{
    assert forall|key:Port,f:spec_fn(u64)->u64,g:spec_fn(u64)->u64|
        gr::generator(md::library(),key,f) && gr::generator(md::library(),key,g)
        implies forall|value:u64| #[trigger] f(g(value))==g(f(value)) by {
        generator_is_xor(key,f);generator_is_xor(key,g);
        let left=choose|mask:u64| f==#[trigger] value_xor(mask);
        let right=choose|mask:u64| g==#[trigger] value_xor(mask);
        assert forall|value:u64| #[trigger] f(g(value))==g(f(value)) by {
            assert((value^right)^left==(value^left)^right) by(bit_vector);
        }
    }
}

/// Exact partial generators preserve definedness as well as values. Both
/// forward and captured inverse are the real Xor map on every input.
pub proof fn partial_generator(mask:u64,f:crate::mediated::PartialMap<u64>)
    requires crate::partial_independence::value_generators(md::xor_operation(mask)).contains(f),
    ensures f==(|value:u64|Some(value^mask)),
{
    let op=md::xor_operation(mask);
    if f==crate::partial_independence::value_forward(op) {assert(f =~= (|value:u64|Some(value^mask)));}
    else {
        let input=choose|input:u64| #[trigger] op(input).is_some() && op(input).unwrap().undo==f;
        assert(f =~= (|value:u64|Some(value^mask)));
    }
}
proof fn stable_partial(mask:u64,f:crate::mediated::PartialMap<u64>)
    ensures crate::partial_independence::value_stable(|a:u64,b:u64|a==b,md::xor_operation(mask),f),
{
    assert forall|value:u64| #[trigger] f(value).is_some() implies {
        let a=md::xor_operation(mask)(value);let b=md::xor_operation(mask)(f(value).unwrap());
        &&& a.is_some()==b.is_some()
        &&& a.is_some() ==> a.unwrap().outcome==b.unwrap().outcome
            && crate::mediated::partial_related(|a:u64,b:u64|a==b,a.unwrap().undo,b.unwrap().undo)
    } by {}
}
pub proof fn strict_pair(left:u64,right:u64)
    ensures crate::partial_independence::value_independent(|a:u64,b:u64|a==b,md::xor_operation(left),md::xor_operation(right)),
{
    let eq=|a:u64,b:u64|a==b;
    assert forall|f:crate::mediated::PartialMap<u64>,g:crate::mediated::PartialMap<u64>|
        crate::partial_independence::value_generators(md::xor_operation(left)).contains(f)
        && crate::partial_independence::value_generators(md::xor_operation(right)).contains(g)
        implies #[trigger] crate::partial_independence::commutes(eq,f,g) by {
        partial_generator(left,f);partial_generator(right,g);
        assert forall|v:u64| #[trigger] crate::partial_independence::optional_equal(eq,
            crate::partial_independence::compose(f,g)(v),crate::partial_independence::compose(g,f)(v)) by {
            assert((v^right)^left==(v^left)^right) by(bit_vector);
        }
    }
    assert forall|g:crate::mediated::PartialMap<u64>|crate::partial_independence::value_generators(md::xor_operation(right)).contains(g)
        implies #[trigger] crate::partial_independence::value_stable(eq,md::xor_operation(left),g) by {stable_partial(left,g);}
    assert forall|f:crate::mediated::PartialMap<u64>|crate::partial_independence::value_generators(md::xor_operation(left)).contains(f)
        implies #[trigger] crate::partial_independence::value_stable(eq,md::xor_operation(right),f) by {stable_partial(right,f);}
}
/// The actual executable library supplies raw outcome stability and strict
/// inverse commutation needed by constructive lifecycle deletion.
pub proof fn strict_interface()
    ensures crate::observational_grammar::primitive_theory(|_:Port,a:u64,b:u64|a==b,md::library()),
        crate::shared_replay::interface(|_:Port,a:u64,b:u64|a==b,md::library()),
{
    md::library_theory();crate::observational_grammar::exact_theory(|_:Port,a:u64,b:u64|a==b,md::library());
    assert forall|a:Port,b:Port,x:u64,y:u64|#![trigger (md::library().apply)(a,x),(md::library().apply)(b,y)]
        md::library().allowed.contains(a) && md::library().allowed.contains(b)
        && (md::library().arguments)(a,x) && (md::library().arguments)(b,y) && (md::library().key)(a)==(md::library().key)(b)
        implies crate::partial_independence::value_independent(|u:u64,v:u64|(|_:Port,c:u64,d:u64|c==d)((md::library().key)(a),u,v),(md::library().apply)(a,x),(md::library().apply)(b,y)) by {
            strict_pair(x,y);
            assert((|u:u64,v:u64|(|_:Port,c:u64,d:u64|c==d)((md::library().key)(a),u,v)) =~= (|u:u64,v:u64|u==v));
        }
}

}
