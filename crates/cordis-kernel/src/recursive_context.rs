//! A foundational boundary of Definition 28's recursive context equation.
//!
//! Reading Γ → Γ as *all* mathematical functions, an inhabited context cannot
//! contain every endomorphism of itself while supporting distinct observations.
//! This diagonal obstruction is about that literal set/function reading. It
//! does not rule out a domain-theoretic or restricted/defunctionalized model.
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(G)]
#[verifier::reject_recursive_types(C)]
#[allow(clippy::type_complexity)]
pub struct Encoding<G,C> {
    pub pack:spec_fn(G,spec_fn(G)->G,C)->G,
    pub previous:spec_fn(G)->G,
    pub accumulator:spec_fn(G)->spec_fn(G)->G,
    pub coeffects:spec_fn(G)->C,
}

/// Only the constructor/projection half of the asserted recursive product is
/// needed. Function equality is pointwise, so no closure identity is assumed.
pub open spec fn product_laws<G,C>(encoding:Encoding<G,C>)->bool {
    &&& forall|state:G,map:spec_fn(G)->G,context:C| #[trigger] (encoding.previous)((encoding.pack)(state,map,context))==state
    &&& forall|state:G,map:spec_fn(G)->G,context:C| #[trigger] (encoding.coeffects)((encoding.pack)(state,map,context))==context
    &&& forall|state:G,map:spec_fn(G)->G,context:C,input:G|
        #[trigger] (encoding.accumulator)((encoding.pack)(state,map,context))(input)==map(input)
}

/// No retraction from all G endomorphisms into a nontrivial G exists: evaluating
/// the packed diagonal at its own packed context forces opposite answers.
pub proof fn unrestricted_accumulator_obstruction<G,C>(encoding:Encoding<G,C>,left:G,right:G,context:C)
    requires product_laws(encoding),left!=right,
    ensures false,
{
    let diagonal=|x:G|if (encoding.accumulator)(x)(x)==left {right} else {left};
    let packed=(encoding.pack)(left,diagonal,context);
    assert((encoding.accumulator)(packed)(packed)==diagonal(packed));
    if (encoding.accumulator)(packed)(packed)==left {assert(diagonal(packed)==right);}
    else {assert(diagonal(packed)==left);}
}

/// Even without two preselected context states, two coeffect observations force
/// them via pack/projection. Thus no inhabited literal model carries a Boolean
/// coeffect, a normal mutable store, or any other nontrivial coeffect carrier.
pub proof fn nontrivial_coeffect_obstruction<G,C>(encoding:Encoding<G,C>,initial:G,left:C,right:C)
    requires product_laws(encoding),left!=right,
    ensures false,
{
    let identity=|x:G|x;
    let a=(encoding.pack)(initial,identity,left);let b=(encoding.pack)(initial,identity,right);
    assert((encoding.coeffects)(a)==left);assert((encoding.coeffects)(b)==right);
    assert(a!=b);
    unrestricted_accumulator_obstruction(encoding,a,b,left);
}

/// The obstruction is specifically nontriviality, not a blanket rejection of
/// every product law. The singleton context/coeffect carrier satisfies these
/// projection equations; this does not assert an initial algebra or least mu
/// fixed-point interpretation.
pub open spec fn singleton()->Encoding<(),()> {
    Encoding{pack:|_:(),_:spec_fn(())->(),_:()|(),previous:|_:()|(),accumulator:|_:()|(|_:()|()),coeffects:|_:()|()}
}
pub proof fn singleton_model()
    ensures product_laws(singleton()),
{
    assert forall|state:(),map:spec_fn(())->(),context:(),input:()|
        #[trigger] (singleton().accumulator)((singleton().pack)(state,map,context))(input)==map(input) by {assert(map(input)==());}
}

} // verus!
