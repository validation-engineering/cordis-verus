//! Typed finite coeffect contexts, isolation, and interception (Definitions 19–27).
//! A carrier `U` represents a disjoint sum of key-specific value types; a
//! `FiberCodec` gives an actual bijection for each represented Rust type.
//! These are mathematical context operations, not a proof of host callbacks.
use vstd::prelude::*;

verus! {

pub type Family<K,U> = spec_fn(K,U)->bool;

/// A finite dependent partial map, represented inside an ordinary Rust type.
pub open spec fn typed<K,U>(family:Family<K,U>,table:Map<K,U>) -> bool {
    forall|k:K| table.dom().contains(k) ==> family(k,table[k])
}
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(U)]
#[verifier::reject_recursive_types(T)]
pub struct FiberCodec<K,U,T> {
    pub key:K,
    pub encode:spec_fn(T)->U,
    pub decode:spec_fn(U)->Option<T>,
}
pub open spec fn codec<K,U,T>(family:Family<K,U>,c:FiberCodec<K,U,T>) -> bool {
    &&& forall|t:T| #[trigger] (c.decode)((c.encode)(t))==Some(t)
        && family(c.key,(c.encode)(t))
    &&& forall|u:U| family(c.key,u) == #[trigger] (c.decode)(u).is_some()
    &&& forall|u:U| family(c.key,u) ==> #[trigger] (c.encode)((c.decode)(u).unwrap())==u
}
pub open spec fn get<K,U>(table:Map<K,U>,k:K) -> Option<U> {
    if table.dom().contains(k) {Some(table[k])} else {None}
}
pub open spec fn set<K,U>(table:Map<K,U>,k:K,value:U) -> Option<Map<K,U>> {
    if table.dom().contains(k) {None} else {Some(table.insert(k,value))}
}
pub open spec fn revoke<K,U>(table:Map<K,U>,k:K) -> Option<Map<K,U>> {
    if table.dom().contains(k) {Some(table.remove(k))} else {None}
}
#[verifier::reject_recursive_types(S)]
pub struct PartialYield<S> {pub state:S,pub undo:spec_fn(S)->Option<S>}
pub open spec fn provide<K,U>(table:Map<K,U>,k:K,value:U)->Option<PartialYield<Map<K,U>>> {
    match set(table,k,value) {None=>None,Some(state)=>Some(PartialYield {
        state,undo:|s:Map<K,U>|revoke(s,k),
    })}
}
pub proof fn provision_witness<K,U>(table:Map<K,U>,k:K,u:U)
    ensures provide(table,k,u).is_some()==!table.dom().contains(k),
        provide(table,k,u).is_some() ==> (provide(table,k,u).unwrap().undo)(provide(table,k,u).unwrap().state)==Some(table),
{
    if !table.dom().contains(k) {assert(table.insert(k,u).remove(k) =~= table);}
}
pub open spec fn typed_get<K,U,T>(table:Map<K,U>,c:FiberCodec<K,U,T>) -> Option<T> {
    match get(table,c.key) {None=>None,Some(u)=>(c.decode)(u)}
}
pub open spec fn typed_set<K,U,T>(table:Map<K,U>,c:FiberCodec<K,U,T>,t:T) -> Option<Map<K,U>> {
    set(table,c.key,(c.encode)(t))
}
pub proof fn codec_bijection<K,U,T>(family:Family<K,U>,c:FiberCodec<K,U,T>,a:T,b:T,u:U)
    requires codec(family,c),
    ensures (c.encode)(a)==(c.encode)(b) ==> a==b,
        family(c.key,u) ==> (c.decode)(u).is_some()
            && (c.encode)((c.decode)(u).unwrap())==u,
{
    assert((c.decode)((c.encode)(a))==Some(a));
    assert((c.decode)((c.encode)(b))==Some(b));
}
pub proof fn typed_access<K,U,T>(family:Family<K,U>,table:Map<K,U>,c:FiberCodec<K,U,T>)
    requires typed(family,table),codec(family,c),
    ensures typed_get(table,c).is_some()==table.dom().contains(c.key),
        typed_get(table,c).is_some() ==> (c.encode)(typed_get(table,c).unwrap())==table[c.key],
{ }
pub proof fn typed_provision<K,U,T>(family:Family<K,U>,table:Map<K,U>,c:FiberCodec<K,U,T>,t:T)
    requires typed(family,table),codec(family,c),!table.dom().contains(c.key),
    ensures typed_set(table,c,t).is_some(),
        typed(family,typed_set(table,c,t).unwrap()),
        typed_get(typed_set(table,c,t).unwrap(),c)==Some(t),
        revoke(typed_set(table,c,t).unwrap(),c.key)==Some(table),
        forall|k:K| k!=c.key ==> get(typed_set(table,c,t).unwrap(),k)==get(table,k),
{
    assert(table.insert(c.key,(c.encode)(t)).remove(c.key) =~= table);
}
pub proof fn revoke_preserves_typing<K,U>(family:Family<K,U>,table:Map<K,U>,k:K)
    requires typed(family,table),
    ensures revoke(table,k).is_some() ==> typed(family,revoke(table,k).unwrap()),
{ }

/// The embedding retains the finite support even though the operational
/// semantics elsewhere use possibly infinite `IMap` as their ambient type.
pub open spec fn embed<K,U>(table:Map<K,U>) -> IMap<K,U> {
    IMap::new(|k:K| table.dom().contains(k),|k:K|table[k])
}
pub proof fn finite_embedding<K,U>(a:Map<K,U>,b:Map<K,U>,k:K,u:U)
    ensures embed(a)==embed(b) ==> a==b,
        embed(a.insert(k,u))==embed(a).insert(k,u),
        embed(a.remove(k))==embed(a).remove(k),
        crate::coeffects::get(embed(a),k)==get(a,k),
{
    if embed(a)==embed(b) {
        assert forall|j:K| a.dom().contains(j)==b.dom().contains(j) by {
            assert(embed(a).dom().contains(j)==embed(b).dom().contains(j));
        }
        assert forall|j:K| a.dom().contains(j) implies a[j]==b[j] by {
            assert(embed(a)[j]==embed(b)[j]);
        }
        assert(a =~= b);
    }
    assert(embed(a.insert(k,u)) =~= embed(a).insert(k,u));
    assert(embed(a.remove(k)) =~= embed(a).remove(k));
}

/// A concrete heterogeneous family witnesses that the encoding is not a
/// requirement that every dependency have the same value type.
#[derive(PartialEq, Eq, Structural)]
pub enum ExampleKey { Flag, Count }
#[derive(PartialEq, Eq, Structural)]
pub enum ExampleValue { Flag(bool), Count(int) }
pub open spec fn example_family(k:ExampleKey,u:ExampleValue)->bool {
    match (k,u) {(ExampleKey::Flag,ExampleValue::Flag(_))=>true,
        (ExampleKey::Count,ExampleValue::Count(_))=>true,_=>false}
}
pub open spec fn flag_codec()->FiberCodec<ExampleKey,ExampleValue,bool> {
    FiberCodec {key:ExampleKey::Flag,encode:|x:bool|ExampleValue::Flag(x),
        decode:|u:ExampleValue|match u {ExampleValue::Flag(x)=>Some(x),_=>None}}
}
pub open spec fn count_codec()->FiberCodec<ExampleKey,ExampleValue,int> {
    FiberCodec {key:ExampleKey::Count,encode:|x:int|ExampleValue::Count(x),
        decode:|u:ExampleValue|match u {ExampleValue::Count(x)=>Some(x),_=>None}}
}
pub proof fn heterogeneous_family()
    ensures codec(|k,u|example_family(k,u),flag_codec()),codec(|k,u|example_family(k,u),count_codec()),
        typed(|k,u|example_family(k,u),Map::empty().insert(ExampleKey::Flag,ExampleValue::Flag(true))
            .insert(ExampleKey::Count,ExampleValue::Count(42))),
{ }

/// Transport a key's actual typed operation, outcome, and returned partial
/// inverse through its codec. Values belonging to other fibers are rejected.
pub open spec fn encoded_inverse<K,U,T>(c:FiberCodec<K,U,T>,inverse:spec_fn(T)->Option<T>)
    ->spec_fn(U)->Option<U>
{
    |u:U| match (c.decode)(u) {None=>None,Some(t)=>match inverse(t) {
        None=>None,Some(v)=>Some((c.encode)(v)),
    }}
}
pub open spec fn encoded_operation<K,U,T,O>(c:FiberCodec<K,U,T>,op:crate::mediated::Operation<T,O>)
    ->crate::mediated::Operation<U,O>
{
    |u:U| match (c.decode)(u) {None=>None,Some(t)=>match op(t) {
        None=>None,Some(y)=>Some(crate::mediated::ValueYield {value:(c.encode)(y.value),
            undo:encoded_inverse(c,y.undo),outcome:y.outcome}),
    }}
}
pub proof fn encoded_operation_witness<K,U,T,O>(family:Family<K,U>,c:FiberCodec<K,U,T>,
    op:crate::mediated::Operation<T,O>)
    requires codec(family,c),crate::mediated::operation_admissible(|a:T,b:T|a==b,op),
    ensures crate::mediated::operation_admissible(|a:U,b:U|a==b,encoded_operation(c,op)),
{
    let encoded=encoded_operation(c,op);
    assert forall|u:U| #[trigger] encoded(u).is_some() implies
        (encoded(u).unwrap().undo)(encoded(u).unwrap().value)==Some(u) by {
        let t=(c.decode)(u).unwrap();let y=op(t).unwrap();
        assert((y.undo)(y.value)==Some(t));
        assert((c.decode)((c.encode)(y.value))==Some(y.value));
        assert(family(c.key,u));
        assert((c.encode)(t)==u);
    }
}
/// The generic mediated grammar really executes the encoded typed operation:
/// it preserves finite support and all other key-specific values, and selects
/// its continuation from the original operation's actual outcome.
pub proof fn typed_mediated_operation<K,U,T,O>(family:Family<K,U>,table:Map<K,U>,
    c:FiberCodec<K,U,T>,op:crate::mediated::Operation<T,O>,select:spec_fn(O)->Option<nat>)
    requires typed(family,table),codec(family,c),table.dom().contains(c.key),
        op(typed_get(table,c).unwrap()).is_some(),
        crate::mediated::operation_admissible(|a:T,b:T|a==b,op),
    ensures {
        let original=op(typed_get(table,c).unwrap()).unwrap();
        let table2=table.insert(c.key,(c.encode)(original.value));
        let node=crate::mediated::Node::Operation {key:c.key,operation:encoded_operation(c,op),select};
        let result=crate::mediated::run(node,embed(table));
        &&& result.is_some()
        &&& result.unwrap().state==embed(table2)
        &&& typed(family,table2)
        &&& result.unwrap().next==select(original.outcome)
        &&& (result.unwrap().undo)(result.unwrap().state)==Some(embed(table))
        &&& forall|k:K| k!=c.key ==> get(table2,k)==get(table,k)
    },
{
    typed_access(family,table,c);
    let original=op(typed_get(table,c).unwrap()).unwrap();
    assert((c.decode)((c.encode)(original.value))==Some(original.value));
    assert(family(c.key,(c.encode)(original.value)));
    finite_embedding(table,table,c.key,(c.encode)(original.value));
    encoded_operation_witness(family,c,op);
    let node=crate::mediated::Node::Operation {key:c.key,operation:encoded_operation(c,op),select};
    let keys=ISet::new(|k:K|true);
    crate::mediated::operation_admissible_lift(|k:K,a:U,b:U|a==b,keys,c.key,encoded_operation(c,op),select);
    assert(crate::mediated::stage_witness(node));
}
pub proof fn typed_mediated_provision<K,U,T,O>(family:Family<K,U>,table:Map<K,U>,
    c:FiberCodec<K,U,T>,t:T,next:Option<nat>)
    requires typed(family,table),codec(family,c),!table.dom().contains(c.key),
    ensures {
        let node=crate::mediated::Node::<K,U,O>::Provision {key:c.key,value:(c.encode)(t),next};
        let result=crate::mediated::run(node,embed(table));
        &&& result.is_some()
        &&& result.unwrap().state==embed(typed_set(table,c,t).unwrap())
        &&& typed(family,typed_set(table,c,t).unwrap())
        &&& result.unwrap().next==next
        &&& (result.unwrap().undo)(result.unwrap().state)==Some(embed(table))
    },
{
    typed_provision(family,table,c,t);
    finite_embedding(table,table,c.key,(c.encode)(t));
    assert(embed(table).insert(c.key,(c.encode)(t)).remove(c.key) =~= embed(table));
}

/// Realm resolution is not restricted to a finite map. The dependency table
/// retains the finite-support requirement of Definition 19.
#[verifier::reject_recursive_types(K)]
pub struct Isolated<K,R,U> {pub realms:IMap<K,R>,pub table:Map<R,U>}
pub open spec fn resolve<K,R>(fallback:spec_fn(K)->R,realms:IMap<K,R>,k:K)->R {
    if realms.dom().contains(k) {realms[k]} else {fallback(k)}
}
pub open spec fn realm_embedding<K,R>(fallback:spec_fn(K)->R)->bool {
    forall|a:K,b:K| #[trigger] fallback(a)==#[trigger] fallback(b) ==> a==b
}
pub proof fn unisolated_realms<K,R>(fallback:spec_fn(K)->R,realms:IMap<K,R>,a:K,b:K)
    requires realm_embedding(fallback),!realms.dom().contains(a),!realms.dom().contains(b),
    ensures resolve(fallback,realms,a)==fallback(a),
        (resolve(fallback,realms,a)==resolve(fallback,realms,b))==(a==b),
{ }
pub open spec fn isolated_get<K,R,U>(fallback:spec_fn(K)->R,c:Isolated<K,R,U>,k:K)->Option<U> {
    get(c.table,resolve(fallback,c.realms,k))
}
pub open spec fn isolate<K,R,U>(c:Isolated<K,R,U>,k:K,r:R)->Isolated<K,R,U> {
    Isolated {realms:c.realms.insert(k,r),table:c.table}
}
pub open spec fn isolated_set<K,R,U>(fallback:spec_fn(K)->R,c:Isolated<K,R,U>,k:K,u:U)
    ->Option<Isolated<K,R,U>>
{
    match set(c.table,resolve(fallback,c.realms,k),u) {None=>None,
        Some(table)=>Some(Isolated {realms:c.realms,table})}
}
/// The printed Definition 25 resolves the realm in the context supplied to
/// the inverse. It does not capture the realm of the original provision.
pub open spec fn isolated_revoke<K,R,U>(fallback:spec_fn(K)->R,c:Isolated<K,R,U>,k:K)
    ->Option<Isolated<K,R,U>>
{
    match revoke(c.table,resolve(fallback,c.realms,k)) {None=>None,
        Some(table)=>Some(Isolated {realms:c.realms,table})}
}
pub open spec fn isolated_provide<K,R,U>(fallback:spec_fn(K)->R,c:Isolated<K,R,U>,k:K,u:U)
    ->Option<PartialYield<Isolated<K,R,U>>>
{
    match isolated_set(fallback,c,k,u) {None=>None,Some(state)=>Some(PartialYield {
        state,undo:|s:Isolated<K,R,U>|isolated_revoke(fallback,s,k),
    })}
}
pub proof fn isolated_witness<K,R,U>(fallback:spec_fn(K)->R,c:Isolated<K,R,U>,k:K,u:U)
    ensures isolated_provide(fallback,c,k,u).is_some()==!c.table.dom().contains(resolve(fallback,c.realms,k)),
        isolated_provide(fallback,c,k,u).is_some() ==>
            (isolated_provide(fallback,c,k,u).unwrap().undo)(isolated_provide(fallback,c,k,u).unwrap().state)==Some(c),
{
    let r=resolve(fallback,c.realms,k);
    if !c.table.dom().contains(r) {assert(c.table.insert(r,u).remove(r) =~= c.table);}
}
pub proof fn isolation_resolution<K,R,U>(fallback:spec_fn(K)->R,c:Isolated<K,R,U>,k:K,r:R)
    ensures isolate(c,k,r).table==c.table,
        resolve(fallback,isolate(c,k,r).realms,k)==r,
        isolated_get(fallback,isolate(c,k,r),k)==get(c.table,r),
        forall|j:K| j!=k ==> isolated_get(fallback,isolate(c,k,r),j)==isolated_get(fallback,c,j),
{ }
pub proof fn isolation_overwrite<K,R,U>(c:Isolated<K,R,U>,k:K,r:R,s:R)
    ensures isolate(isolate(c,k,r),k,s)==isolate(c,k,s),
{
    assert(c.realms.insert(k,r).insert(k,s) =~= c.realms.insert(k,s));
}
pub proof fn isolation_alias<K,R,U>(fallback:spec_fn(K)->R,c:Isolated<K,R,U>,a:K,b:K)
    requires resolve(fallback,c.realms,a)==resolve(fallback,c.realms,b),
    ensures isolated_get(fallback,c,a)==isolated_get(fallback,c,b),
{ }
pub proof fn isolated_provision<K,R,U>(fallback:spec_fn(K)->R,c:Isolated<K,R,U>,k:K,u:U,family:Family<R,U>)
    requires typed(family,c.table),family(resolve(fallback,c.realms,k),u),
        !c.table.dom().contains(resolve(fallback,c.realms,k)),
    ensures isolated_set(fallback,c,k,u).is_some(),
        isolated_get(fallback,isolated_set(fallback,c,k,u).unwrap(),k)==Some(u),
        typed(family,isolated_set(fallback,c,k,u).unwrap().table),
        isolated_revoke(fallback,isolated_set(fallback,c,k,u).unwrap(),k)==Some(c),
{
    let r=resolve(fallback,c.realms,k);
    assert(c.table.insert(r,u).remove(r) =~= c.table);
}
/// A foreign table update at another resolved realm commutes with set and its
/// inverse; the realm lookup frame is a necessary hypothesis for this law.
pub proof fn isolated_disjoint_recovery<K,R,U>(fallback:spec_fn(K)->R,c:Isolated<K,R,U>,
    k:K,u:U,other:R,v:U)
    requires !c.table.dom().contains(resolve(fallback,c.realms,k)),
        other!=resolve(fallback,c.realms,k),
    ensures {
        let made=isolated_set(fallback,c,k,u).unwrap();
        let changed=Isolated {realms:made.realms,table:made.table.insert(other,v)};
        isolated_revoke(fallback,changed,k)==Some(Isolated {realms:c.realms,table:c.table.insert(other,v)})
    },
{
    let r=resolve(fallback,c.realms,k);
    assert(c.table.insert(r,u).insert(other,v).remove(r) =~= c.table.insert(other,v));
}

/// The host representation specializes realms to `(logical key, realm id)`.
/// Therefore default realms are injective and two different logical keys never
/// alias storage merely because their numeric realm ids happen to coincide.
pub open spec fn host_port(realms:Map<u64,u64>,key:u64)->crate::Port {
    crate::Port {key,realm:if realms.dom().contains(key) {realms[key]} else {0}}
}
pub open spec fn host_realm_table(realms:Map<u64,u64>)->IMap<u64,crate::Port> {
    IMap::new(|k:u64|realms.dom().contains(k),|k:u64|crate::Port {key:k,realm:realms[k]})
}
pub proof fn host_port_resolution(realms:Map<u64,u64>,key:u64,other:u64,realm:u64)
    ensures host_port(realms.insert(key,realm),key)==(crate::Port {key,realm}),
        resolve(|k:u64|crate::Port {key:k,realm:0},host_realm_table(realms),key)==host_port(realms,key),
        key!=other ==> host_port(realms.insert(key,realm),other)==host_port(realms,other),
        key!=other ==> host_port(realms,key)!=host_port(realms,other),
        !realms.dom().contains(key) ==> host_port(realms,key)==(crate::Port {key,realm:0}),
{ }

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(M)]
pub struct Metadata<K,M> {
    pub valid:Family<K,M>,pub empty:spec_fn(K)->M,pub merge:spec_fn(K,M,M)->M,
}
pub open spec fn metadata_monoid<K,M>(m:Metadata<K,M>)->bool {
    &&& forall|k:K| #[trigger] (m.valid)(k,(m.empty)(k))
    &&& forall|k:K,a:M,b:M| (m.valid)(k,a) && (m.valid)(k,b) ==>
        #[trigger] (m.valid)(k,(m.merge)(k,a,b))
    &&& forall|k:K,a:M| (m.valid)(k,a) ==>
        #[trigger] (m.merge)(k,(m.empty)(k),a)==a && (m.merge)(k,a,(m.empty)(k))==a
    &&& forall|k:K,a:M,b:M,c:M| (m.valid)(k,a) && (m.valid)(k,b) && (m.valid)(k,c) ==>
        #[trigger] (m.merge)(k,(m.merge)(k,a,b),c)==(m.merge)(k,a,(m.merge)(k,b,c))
}
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(M)]
#[verifier::reject_recursive_types(U)]
pub struct Intercepted<K,M,U> {
    pub carried:spec_fn(K)->M,pub providers:Map<K,spec_fn(M)->U>,
}
pub open spec fn provider_typed<K,M,U>(m:Metadata<K,M>,family:Family<K,U>,key:K,p:spec_fn(M)->U)->bool {
    forall|mu:M| (m.valid)(key,mu) ==> family(key,#[trigger] p(mu))
}
pub open spec fn interception_typed<K,M,U>(m:Metadata<K,M>,family:Family<K,U>,c:Intercepted<K,M,U>)->bool {
    &&& forall|k:K| #[trigger] (m.valid)(k,(c.carried)(k))
    &&& forall|k:K| c.providers.dom().contains(k) ==> provider_typed(m,family,k,c.providers[k])
}
pub open spec fn empty_interception<K,M,U>(m:Metadata<K,M>)->Intercepted<K,M,U> {
    Intercepted {carried:m.empty,providers:Map::empty()}
}
pub proof fn default_interception<K,M,U>(m:Metadata<K,M>,family:Family<K,U>,k:K)
    requires metadata_monoid(m),
    ensures interception_typed(m,family,empty_interception(m)),
        (empty_interception::<K,M,U>(m).carried)(k)==(m.empty)(k),
{ }
pub open spec fn intercepted_get<K,M,U>(m:Metadata<K,M>,c:Intercepted<K,M,U>,k:K,mu:M)->Option<U> {
    if c.providers.dom().contains(k) {Some((c.providers[k])((m.merge)(k,mu,(c.carried)(k))))} else {None}
}
pub open spec fn intercept<K,M,U>(m:Metadata<K,M>,c:Intercepted<K,M,U>,k:K,nu:M)->Intercepted<K,M,U> {
    Intercepted {carried:|j:K|if j==k {(m.merge)(k,(c.carried)(k),nu)} else {(c.carried)(j)},
        providers:c.providers}
}
pub open spec fn intercepted_set<K,M,U>(c:Intercepted<K,M,U>,k:K,p:spec_fn(M)->U)->Option<Intercepted<K,M,U>> {
    if c.providers.dom().contains(k) {None} else {
        Some(Intercepted {carried:c.carried,providers:c.providers.insert(k,p)})}
}
pub open spec fn intercepted_revoke<K,M,U>(c:Intercepted<K,M,U>,k:K)->Option<Intercepted<K,M,U>> {
    if c.providers.dom().contains(k) {Some(Intercepted {carried:c.carried,providers:c.providers.remove(k)})} else {None}
}
pub open spec fn intercepted_provide<K,M,U>(c:Intercepted<K,M,U>,k:K,p:spec_fn(M)->U)
    ->Option<PartialYield<Intercepted<K,M,U>>>
{
    match intercepted_set(c,k,p) {None=>None,Some(state)=>Some(PartialYield {
        state,undo:|s:Intercepted<K,M,U>|intercepted_revoke(s,k),
    })}
}
pub proof fn intercepted_witness<K,M,U>(c:Intercepted<K,M,U>,k:K,p:spec_fn(M)->U)
    ensures intercepted_provide(c,k,p).is_some()==!c.providers.dom().contains(k),
        intercepted_provide(c,k,p).is_some() ==>
            (intercepted_provide(c,k,p).unwrap().undo)(intercepted_provide(c,k,p).unwrap().state)==Some(c),
{
    if !c.providers.dom().contains(k) {assert(c.providers.insert(k,p).remove(k) =~= c.providers);}
}
pub open spec fn interception_equal<K,M,U>(a:Intercepted<K,M,U>,b:Intercepted<K,M,U>)->bool {
    a.providers==b.providers && forall|k:K| #[trigger] (a.carried)(k)==(b.carried)(k)
}
pub proof fn interception_access<K,M,U>(m:Metadata<K,M>,family:Family<K,U>,c:Intercepted<K,M,U>,k:K,mu:M)
    requires metadata_monoid(m),interception_typed(m,family,c),(m.valid)(k,mu),
    ensures intercepted_get(m,c,k,mu).is_some()==c.providers.dom().contains(k),
        intercepted_get(m,c,k,mu).is_some() ==> family(k,intercepted_get(m,c,k,mu).unwrap()),
{
    assert((m.valid)(k,(c.carried)(k)));
    assert((m.valid)(k,(m.merge)(k,mu,(c.carried)(k))));
}
pub proof fn intercept_preserves_typing<K,M,U>(m:Metadata<K,M>,family:Family<K,U>,c:Intercepted<K,M,U>,k:K,nu:M)
    requires metadata_monoid(m),interception_typed(m,family,c),(m.valid)(k,nu),
    ensures interception_typed(m,family,intercept(m,c,k,nu)),intercept(m,c,k,nu).providers==c.providers,
{
    assert((m.valid)(k,(c.carried)(k)));
    assert((m.valid)(k,(m.merge)(k,(c.carried)(k),nu)));
}
pub proof fn intercept_monoid_action<K,M,U>(m:Metadata<K,M>,family:Family<K,U>,c:Intercepted<K,M,U>,k:K,a:M,b:M)
    requires metadata_monoid(m),interception_typed(m,family,c),(m.valid)(k,a),(m.valid)(k,b),
    ensures interception_equal(intercept(m,c,k,(m.empty)(k)),c),
        interception_equal(intercept(m,intercept(m,c,k,a),k,b),intercept(m,c,k,(m.merge)(k,a,b))),
{
    assert((m.valid)(k,(c.carried)(k)));
    assert((m.merge)(k,(m.empty)(k),(c.carried)(k))==(c.carried)(k));
    assert((m.merge)(k,(c.carried)(k),(m.empty)(k))==(c.carried)(k));
    assert((m.merge)(k,(m.merge)(k,(c.carried)(k),a),b)==(m.merge)(k,(c.carried)(k),(m.merge)(k,a,b)));
}
pub proof fn interception_provision<K,M,U>(m:Metadata<K,M>,family:Family<K,U>,c:Intercepted<K,M,U>,
    k:K,p:spec_fn(M)->U,mu:M)
    requires metadata_monoid(m),interception_typed(m,family,c),provider_typed(m,family,k,p),
        !c.providers.dom().contains(k),(m.valid)(k,mu),
    ensures intercepted_set(c,k,p).is_some(),interception_typed(m,family,intercepted_set(c,k,p).unwrap()),
        intercepted_get(m,intercepted_set(c,k,p).unwrap(),k,mu)==Some(p((m.merge)(k,mu,(c.carried)(k)))),
        intercepted_revoke(intercepted_set(c,k,p).unwrap(),k)==Some(c),
{
    assert(c.providers.insert(k,p).remove(k) =~= c.providers);
}
/// Unlike the isolation inverse, this inverse is unaffected by subsequently
/// deriving more metadata: it always removes the same logical provider key.
pub proof fn interception_derived_recovery<K,M,U>(m:Metadata<K,M>,c:Intercepted<K,M,U>,
    k:K,p:spec_fn(M)->U,j:K,nu:M)
    requires !c.providers.dom().contains(k),
    ensures intercepted_revoke(intercept(m,intercepted_set(c,k,p).unwrap(),j,nu),k)==Some(intercept(m,c,j,nu)),
{
    assert(c.providers.insert(k,p).remove(k) =~= c.providers);
}
pub proof fn intercepted_declaration<K,M,U>(m:Metadata<K,M>,c:Intercepted<K,M,U>,d:Map<K,M>,k:K)
    requires d.dom().contains(k),d.dom().subset_of(c.providers.dom()),
    ensures intercepted_get(m,c,k,d[k]).is_some(),
        intercepted_get(m,c,k,d[k])==Some((c.providers[k])((m.merge)(k,d[k],(c.carried)(k)))),
{ }

/// One well-founded layer of the Definition 28 tower. A client may instantiate
/// `S` with another `FiniteLayer`, repeatedly, without any depth bound in the
/// theorem. This does not assert a solution of the printed non-positive
/// recursive equation `mu G. G * (G -> G) * Sigma`.
#[verifier::reject_recursive_types(S)]
pub struct FiniteLayer<S,K,U> {
    pub inner:crate::foundations::Tracked<S>,pub coeffects:Map<K,U>,
}
pub open spec fn finite_layer<S,K,U>(inner:S,coeffects:Map<K,U>)->FiniteLayer<S,K,U> {
    FiniteLayer {inner:crate::foundations::unit(inner),coeffects}
}
pub open spec fn layer_sequence<S,K,U>(effects:Seq<spec_fn(S)->crate::foundations::Tracked<S>>,
    c:FiniteLayer<S,K,U>)->FiniteLayer<S,K,U>
{
    FiniteLayer {inner:crate::foundations::apply_effects(effects,c.inner),coeffects:c.coeffects}
}
pub proof fn finite_layer_recovery<S,K,U>(effects:Seq<spec_fn(S)->crate::foundations::Tracked<S>>,
    c:FiniteLayer<S,K,U>,family:Family<K,U>)
    requires typed(family,c.coeffects),
        forall|i:int| 0<=i<effects.len() ==> crate::foundations::witnessed(effects[i]),
    ensures typed(family,layer_sequence(effects,c).coeffects),
        layer_sequence(effects,c).coeffects==c.coeffects,
        crate::foundations::tracked_equal(crate::foundations::recover(layer_sequence(effects,c).inner),
            crate::foundations::recover(c.inner)),
{
    crate::foundations::dynamic_sequence_sound(effects,c.inner);
}
/// A derived context has its own view, while the parent value remains in the
/// stack. Discarding the derived view returns the retained parent; applying an
/// identity function to the child alone would not have that meaning.
pub open spec fn derive_scope<S>(parents:Seq<S>,derive:spec_fn(S)->S)->Seq<S>
    recommends parents.len()>0,
{
    parents.push(derive(parents.last()))
}
pub open spec fn discard_scope<S>(scopes:Seq<S>)->Option<Seq<S>> {
    if scopes.len()>1 {Some(scopes.drop_last())} else {None}
}
pub proof fn derived_realization<S>(parents:Seq<S>,derive:spec_fn(S)->S,edited:S)
    requires parents.len()>0,
    ensures derive_scope(parents,derive).last()==derive(parents.last()),
        discard_scope(derive_scope(parents,derive))==Some(parents),
        discard_scope(derive_scope(parents,derive).update(parents.len() as int,edited))==Some(parents),
        forall|i:int| 0<=i<parents.len() ==> derive_scope(parents,derive)[i]==parents[i],
{
    assert(parents.push(derive(parents.last())).drop_last() =~= parents);
    assert(parents.push(derive(parents.last())).update(parents.len() as int,edited).drop_last() =~= parents);
}

} // verus!
