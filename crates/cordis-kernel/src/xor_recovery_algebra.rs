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

}
