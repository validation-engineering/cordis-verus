//! Strict partial-map domain transport from actual inverse witnesses.
//! No failed application is made into a legal source transition. Identity
//! extension below is a separately proved algebraic view of forward maps.
#[cfg(verus_keep_ghost)]
use crate::{grammar_recovery as recovery, mediated as m, partial_independence as p};
use vstd::prelude::*;

verus! {

/// An actual inverse witness plus its foreign commutation transports enabledness.
/// Observational recovery suffices when the foreign map respects the observation.
pub proof fn enabled_after_witness<S>(eq:spec_fn(S,S)->bool,f:m::PartialMap<S>,g:m::PartialMap<S>,undo:m::PartialMap<S>,input:S)
    requires f(input).is_some(),undo(f(input).unwrap()).is_some(),eq(undo(f(input).unwrap()).unwrap(),input),
        g(input).is_some(),p::respects(eq,g),p::commutes(eq,undo,g),
    ensures g(f(input).unwrap()).is_some(),
{
    let middle=f(input).unwrap();let recovered=undo(middle).unwrap();
    assert(g(recovered).is_some());
    assert(p::optional_equal(eq,p::compose(undo,g)(middle),p::compose(g,undo)(middle)));
}

/// Two individually enabled effects yield a real partial diamond. The inverse
/// need only witness the actual first input; no uniform inverse is invented.
pub proof fn enabled_diamond<S>(eq:spec_fn(S,S)->bool,f:m::PartialMap<S>,g:m::PartialMap<S>,undo:m::PartialMap<S>,input:S)
    requires f(input).is_some(),undo(f(input).unwrap()).is_some(),eq(undo(f(input).unwrap()).unwrap(),input),
        g(input).is_some(),p::respects(eq,g),p::commutes(eq,undo,g),p::commutes(eq,f,g),
    ensures g(f(input).unwrap()).is_some(),f(g(input).unwrap()).is_some(),
        eq(f(g(input).unwrap()).unwrap(),g(f(input).unwrap()).unwrap()),
{
    enabled_after_witness(eq,f,g,undo,input);
    assert(p::optional_equal(eq,p::compose(f,g)(input),p::compose(g,f)(input)));
}

/// A useful forward-map bridge to recovery's identity extension. It requires
/// a genuine inverse at every successful forward input and commutation with
/// those inverses. It does not infer that arbitrary returned inverse maps have
/// their own inverse witnesses, nor discharge all of independent_keys.
pub proof fn forward_identity_extension<S>(f:m::PartialMap<S>,g:m::PartialMap<S>,inverses:spec_fn(S)->m::PartialMap<S>)
    requires p::commutes(|a:S,b:S|a==b,f,g),
        forall|input:S| #[trigger] f(input).is_some() ==> (inverses(input))(f(input).unwrap())==Some(input)
            && p::commutes(|a:S,b:S|a==b,inverses(input),g),
    ensures forall|input:S| #[trigger] recovery::total(f)(recovery::total(g)(input))==recovery::total(g)(recovery::total(f)(input)),
{
    assert forall|input:S| #[trigger] recovery::total(f)(recovery::total(g)(input))==recovery::total(g)(recovery::total(f)(input)) by {
        assert(p::optional_equal(|a:S,b:S|a==b,p::compose(f,g)(input),p::compose(g,f)(input)));
        if f(input).is_some() && g(input).is_some() {
            assert(p::respects(|a:S,b:S|a==b,g));
            enabled_diamond(|a:S,b:S|a==b,f,g,inverses(input),input);
        } else if f(input).is_some() {assert(g(f(input).unwrap()).is_none());}
        else if g(input).is_some() {assert(f(g(input).unwrap()).is_none());}
    }
}

/// Forward/forward commutation alone is insufficient for that extension.
/// Both strict composites fail, but the extensions take different branches.
pub proof fn forward_only_is_insufficient()
    ensures {
        let f=|v:int|if v==0 {Some(1int)} else {None};
        let g=|v:int|if v==0 {Some(2int)} else {None};
        &&& p::commutes(|a:int,b:int|a==b,f,g)
        &&& recovery::total(f)(recovery::total(g)(0))!=recovery::total(g)(recovery::total(f)(0))
    },
{
    let f=|v:int|if v==0 {Some(1int)} else {None};
    let g=|v:int|if v==0 {Some(2int)} else {None};
    let eq=|a:int,b:int|a==b;
    assert forall|input:int| #[trigger] p::optional_equal(eq,p::compose(f,g)(input),p::compose(g,f)(input)) by {}
}
}
