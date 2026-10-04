//! Key-local lifts, including inverse and continuation stability (Section 3.4).
//! Value absence is explicit; provision and restriction are therefore ordinary
//! local maps. Operation preconditions remain local observations of that slot.
use vstd::prelude::*;
verus! {
pub type Operation<V,O> = spec_fn(Option<V>)->(Option<V>,spec_fn(Option<V>)->Option<V>,O);

pub open spec fn get<K,V>(s:IMap<K,V>,k:K) -> Option<V> {
    if s.dom().contains(k) {Some(s[k])} else {None}
}
pub open spec fn put<K,V>(s:IMap<K,V>,k:K,v:Option<V>) -> IMap<K,V> {
    match v {Some(v)=>s.insert(k,v),None=>s.remove(k)}
}
pub open spec fn lift<K,V>(k:K,f:spec_fn(Option<V>)->Option<V>) -> spec_fn(IMap<K,V>)->IMap<K,V> {
    |s:IMap<K,V>|put(s,k,f(get(s,k)))
}
pub open spec fn stage<K,V,O>(k:K,op:Operation<V,O>,next:spec_fn(O)->Option<nat>) -> crate::history::IteratorStep<IMap<K,V>> {
    |s:IMap<K,V>| {
        let y=op(get(s,k));(put(s,k,y.0),lift(k,y.1),next(y.2))
    }
}
pub open spec fn local<K,V>(k:K,f:spec_fn(IMap<K,V>)->IMap<K,V>) -> bool {
    exists|g:spec_fn(Option<V>)->Option<V>| f==lift(k,g)
}

pub proof fn lookup_update<K,V>(s:IMap<K,V>,k:K,j:K,v:Option<V>)
    ensures get(put(s,k,v),k)==v,
        k!=j ==> get(put(s,k,v),j)==get(s,j),
{ }
pub proof fn update_commutes<K,V>(s:IMap<K,V>,k:K,j:K,v:Option<V>,w:Option<V>)
    requires k!=j,
    ensures put(put(s,k,v),j,w)==put(put(s,j,w),k,v),
{ assert(put(put(s,k,v),j,w) =~= put(put(s,j,w),k,v)); }
pub proof fn update_restore<K,V>(s:IMap<K,V>,k:K,v:Option<V>)
    ensures put(put(s,k,v),k,get(s,k))==s,
{ assert(put(put(s,k,v),k,get(s,k)) =~= s); }

/// Theorem 45 generator commutation covers all four forward/inverse pairings.
pub proof fn distinct_lifts_commute<K,V>(k:K,j:K,f:spec_fn(Option<V>)->Option<V>,g:spec_fn(Option<V>)->Option<V>)
    requires k!=j,
    ensures crate::history::commutes(lift(k,f),lift(j,g)),
{
    assert forall|s:IMap<K,V>| #[trigger] lift(k,f)(lift(j,g)(s))==lift(j,g)(lift(k,f)(s)) by {
        lookup_update(s,j,k,g(get(s,j)));lookup_update(s,k,j,f(get(s,k)));
        update_commutes(s,k,j,f(get(s,k)),g(get(s,j)));
    }
}

pub proof fn stage_generators_local<K,V,O>(k:K,op:Operation<V,O>,next:spec_fn(O)->Option<nat>,
    f:spec_fn(IMap<K,V>)->IMap<K,V>)
    requires crate::history::generators(stage(k,op,next)).contains(f),
    ensures local(k,f),
{
    let step=stage(k,op,next);
    if f==crate::history::forward_of(step) {
        let primitive=|v:Option<V>|op(v).0;
        assert(f =~= lift(k,primitive));
    } else {
        let s=choose|s:IMap<K,V>| (#[trigger] step(s)).1==f;
        assert(f==lift(k,op(get(s,k)).1));
    }
}

pub proof fn foreign_preserves_yield<K,V,O>(k:K,j:K,op:Operation<V,O>,next:spec_fn(O)->Option<nat>,
    f:spec_fn(Option<V>)->Option<V>)
    requires k!=j,
    ensures crate::history::stable_yield(stage(k,op,next),lift(j,f)),
{
    let current=stage(k,op,next);let foreign=lift(j,f);
    assert forall|s:IMap<K,V>| {
        let reached=#[trigger] current(foreign(s));
        &&& reached.1==current(s).1
        &&& reached.2==current(s).2
    } by { lookup_update(s,j,k,f(get(s,j))); }
}

/// Definedness and outcomes are unchanged as well as the returned continuation.
pub proof fn foreign_preserves_observation<K,V,O>(k:K,j:K,op:Operation<V,O>,
    defined:spec_fn(Option<V>)->bool,f:spec_fn(Option<V>)->Option<V>,s:IMap<K,V>)
    requires k!=j,
    ensures defined(get(lift(j,f)(s),k))==defined(get(s,k)),
        op(get(lift(j,f)(s),k)).2==op(get(s,k)).2,
{ lookup_update(s,j,k,f(get(s,j))); }

/// Full distinct-key stage independence, not just commuting resulting values.
pub proof fn distinct_key_independence<K,V,O,P>(k:K,j:K,left:Operation<V,O>,right:Operation<V,P>,
    ln:spec_fn(O)->Option<nat>,rn:spec_fn(P)->Option<nat>)
    requires k!=j,
    ensures crate::history::independent_stages(stage(k,left,ln),stage(j,right,rn)),
{
    let a=stage(k,left,ln);let b=stage(j,right,rn);
    assert forall|f:spec_fn(IMap<K,V>)->IMap<K,V>,g:spec_fn(IMap<K,V>)->IMap<K,V>|
        crate::history::generators(a).contains(f) && crate::history::generators(b).contains(g)
        implies #[trigger] crate::history::commutes(f,g) by {
        stage_generators_local(k,left,ln,f);stage_generators_local(j,right,rn,g);
        let fp=choose|p:spec_fn(Option<V>)->Option<V>| f==lift(k,p);
        let gp=choose|p:spec_fn(Option<V>)->Option<V>| g==lift(j,p);
        distinct_lifts_commute(k,j,fp,gp);
    }
    assert forall|g:spec_fn(IMap<K,V>)->IMap<K,V>| crate::history::generators(b).contains(g)
        implies #[trigger] crate::history::stable_yield(a,g) by {
        stage_generators_local(j,right,rn,g);
        let gp=choose|p:spec_fn(Option<V>)->Option<V>| g==lift(j,p);
        foreign_preserves_yield(k,j,left,ln,gp);
    }
    assert forall|f:spec_fn(IMap<K,V>)->IMap<K,V>| crate::history::generators(a).contains(f)
        implies #[trigger] crate::history::stable_yield(b,f) by {
        stage_generators_local(k,left,ln,f);
        let fp=choose|p:spec_fn(Option<V>)->Option<V>| f==lift(k,p);
        foreign_preserves_yield(j,k,right,rn,fp);
    }
}

/// A primitive inverse needs to recover only the actual input slot. Other keys
/// are not required unchanged between applications in the general recovery law.
pub proof fn lifted_witness<K,V,O>(k:K,op:Operation<V,O>,next:spec_fn(O)->Option<nat>,s:IMap<K,V>)
    requires (op(get(s,k)).1)(op(get(s,k)).0)==get(s,k),
    ensures (stage(k,op,next)(s).1)(stage(k,op,next)(s).0)==s,
{
    let y=op(get(s,k));lookup_update(s,k,k,y.0);update_restore(s,k,y.0);
}

pub open spec fn value_stage<V,O>(op:Operation<V,O>,next:spec_fn(O)->Option<nat>) -> crate::history::IteratorStep<Option<V>> {
    |v:Option<V>| {let y=op(v);(y.0,y.1,next(y.2))}
}

pub proof fn generator_lift<K,V,O>(k:K,op:Operation<V,O>,next:spec_fn(O)->Option<nat>,
    f:spec_fn(IMap<K,V>)->IMap<K,V>)
    requires crate::history::generators(stage(k,op,next)).contains(f),
    ensures exists|g:spec_fn(Option<V>)->Option<V>|
        crate::history::generators(value_stage(op,next)).contains(g) && f==lift(k,g),
{
    let step=stage(k,op,next);let primitive=value_stage(op,next);
    if f==crate::history::forward_of(step) {
        let g=crate::history::forward_of(primitive);
        assert(f =~= lift(k,g));
        assert(crate::history::generators(primitive).contains(g));
    } else {
        let s=choose|s:IMap<K,V>| (#[trigger] step(s)).1==f;
        let g=op(get(s,k)).1;
        assert(primitive(get(s,k)).1==g);
        assert(crate::history::generators(primitive).contains(g));
        assert(f==lift(k,g));
    }
}
pub proof fn lift_commutation<K,V>(k:K,f:spec_fn(Option<V>)->Option<V>,g:spec_fn(Option<V>)->Option<V>)
    requires crate::history::commutes(f,g),
    ensures crate::history::commutes(lift(k,f),lift(k,g)),
{
    assert forall|s:IMap<K,V>| #[trigger] lift(k,f)(lift(k,g)(s))==lift(k,g)(lift(k,f)(s)) by {
        lookup_update(s,k,k,g(get(s,k)));lookup_update(s,k,k,f(get(s,k)));
        assert(f(g(get(s,k)))==g(f(get(s,k))));
        assert(lift(k,f)(lift(k,g)(s)) =~= lift(k,g)(lift(k,f)(s)));
    }
}
pub proof fn lift_stability<K,V,O>(k:K,op:Operation<V,O>,next:spec_fn(O)->Option<nat>,g:spec_fn(Option<V>)->Option<V>)
    requires crate::history::stable_yield(value_stage(op,next),g),
    ensures crate::history::stable_yield(stage(k,op,next),lift(k,g)),
{
    let current=stage(k,op,next);let foreign=lift(k,g);let primitive=value_stage(op,next);
    assert forall|s:IMap<K,V>| {
        let reached=#[trigger] current(foreign(s));
        &&& reached.1==current(s).1
        &&& reached.2==current(s).2
    } by {
        lookup_update(s,k,k,g(get(s,k)));
        assert(primitive(g(get(s,k))).1==primitive(get(s,k)).1);
        assert(primitive(g(get(s,k))).2==primitive(get(s,k)).2);
    }
}

/// Definition 46 supplies a value-level same-key commutativity witness. Lifting
/// that witness proves context independence; it is not assumed at context level.
pub proof fn shared_key_independence<K,V,O,P>(k:K,left:Operation<V,O>,right:Operation<V,P>,
    ln:spec_fn(O)->Option<nat>,rn:spec_fn(P)->Option<nat>)
    requires crate::history::independent_stages(value_stage(left,ln),value_stage(right,rn)),
    ensures crate::history::independent_stages(stage(k,left,ln),stage(k,right,rn)),
{
    let a=stage(k,left,ln);let b=stage(k,right,rn);
    let va=value_stage(left,ln);let vb=value_stage(right,rn);
    assert forall|f:spec_fn(IMap<K,V>)->IMap<K,V>,g:spec_fn(IMap<K,V>)->IMap<K,V>|
        crate::history::generators(a).contains(f) && crate::history::generators(b).contains(g)
        implies #[trigger] crate::history::commutes(f,g) by {
        generator_lift(k,left,ln,f);generator_lift(k,right,rn,g);
        let fp=choose|p:spec_fn(Option<V>)->Option<V>| crate::history::generators(va).contains(p) && f==lift(k,p);
        let gp=choose|p:spec_fn(Option<V>)->Option<V>| crate::history::generators(vb).contains(p) && g==lift(k,p);
        assert(crate::history::commutes(fp,gp));lift_commutation(k,fp,gp);
    }
    assert forall|g:spec_fn(IMap<K,V>)->IMap<K,V>| crate::history::generators(b).contains(g)
        implies #[trigger] crate::history::stable_yield(a,g) by {
        generator_lift(k,right,rn,g);
        let gp=choose|p:spec_fn(Option<V>)->Option<V>| crate::history::generators(vb).contains(p) && g==lift(k,p);
        assert(crate::history::stable_yield(va,gp));lift_stability(k,left,ln,gp);
    }
    assert forall|f:spec_fn(IMap<K,V>)->IMap<K,V>| crate::history::generators(a).contains(f)
        implies #[trigger] crate::history::stable_yield(b,f) by {
        generator_lift(k,left,ln,f);
        let fp=choose|p:spec_fn(Option<V>)->Option<V>| crate::history::generators(va).contains(p) && f==lift(k,p);
        assert(crate::history::stable_yield(vb,fp));lift_stability(k,right,rn,fp);
    }
}

/// Theorem 47's primitive cases: non-overlapping provision keys are separated;
/// overlapping operation keys consume their local coeffect witness.
pub proof fn compatible_key_independence<K,V,O,P>(k:K,j:K,left:Operation<V,O>,right:Operation<V,P>,
    ln:spec_fn(O)->Option<nat>,rn:spec_fn(P)->Option<nat>,left_provides:bool,right_provides:bool)
    requires (left_provides || right_provides) ==> k!=j,
        k==j && !left_provides && !right_provides ==>
            crate::history::independent_stages(value_stage(left,ln),value_stage(right,rn)),
    ensures crate::history::independent_stages(stage(k,left,ln),stage(j,right,rn)),
{
    if k!=j {distinct_key_independence(k,j,left,right,ln,rn);}
    else {shared_key_independence(k,left,right,ln,rn);}
}

/// A fixed program family may choose a different key, operation and next stage
/// at each continuation. Its result, inverse and continuation remain dynamic.
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(O)]
pub struct Primitive<K,V,O> {
    pub key: K,
    pub operation: Operation<V,O>,
    pub next: spec_fn(O)->Option<nat>,
    pub provides: bool,
}
pub type Primitives<K,V,O> = spec_fn(nat,nat)->Primitive<K,V,O>;
pub open spec fn lifted_family<K,V,O>(program:Primitives<K,V,O>) -> crate::canonical::Family<IMap<K,V>> {
    |owner:nat,id:nat| {let p=program(owner,id);stage(p.key,p.operation,p.next)}
}
pub open spec fn compatible_family<K,V,O>(program:Primitives<K,V,O>) -> bool {
    forall|a:nat,b:nat,i:nat,j:nat| #![trigger program(a,i),program(b,j)] a!=b ==> {
        let l=program(a,i);let r=program(b,j);
        &&& (l.provides || r.provides) ==> l.key!=r.key
        &&& l.key==r.key && !l.provides && !r.provides ==>
            crate::history::independent_stages(value_stage(l.operation,l.next),value_stage(r.operation,r.next))
    }
}

/// The local declaration/coeffect obligations imply independence of every
/// cross-owner reachable continuation (and hence also of this whole family).
pub proof fn family_independence<K,V,O>(program:Primitives<K,V,O>)
    requires compatible_family(program),
    ensures crate::canonical::independent(lifted_family(program)),
{
    let family=lifted_family(program);
    assert forall|a:nat,b:nat,i:nat,j:nat| a!=b implies
        #[trigger] crate::history::independent_stages(family(a,i),family(b,j)) by {
        let l=program(a,i);let r=program(b,j);
        compatible_key_independence(l.key,r.key,l.operation,r.operation,l.next,r.next,l.provides,r.provides);
    }
}

/// A complete end-to-end bridge from local coeffects to dynamic schedule
/// uniqueness. Neither equal histories nor an assumed context-level diamond
/// is supplied by the caller.
pub proof fn coeffect_schedule_independence<K,V,O>(program:Primitives<K,V,O>,
    left:Seq<nat>,right:Seq<nat>,initial:crate::canonical::Machine<IMap<K,V>>)
    requires compatible_family(program),
        crate::canonical::complete(lifted_family(program),left,initial),
        crate::canonical::complete(lifted_family(program),right,initial),
    ensures crate::canonical::execute(lifted_family(program),left,initial)
        ==crate::canonical::execute(lifted_family(program),right,initial),
{
    family_independence(program);
    crate::canonical::complete_confluence(lifted_family(program),left,right,initial);
}
} // verus!
