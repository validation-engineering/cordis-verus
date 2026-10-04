//! Explicit dependent-value interpretation for the conditional paper APIs.
//!
//! A common sum carrier U does not make every key have the same value type.
//! The all-input projection gate records each key's actual fiber. Finiteness
//! is supplied separately by a Map representation; no recursive Gamma model
//! or unrestricted callback refinement follows from these interpretation laws.
#[cfg(verus_keep_ghost)]
use crate::{
    contexts as t, iterators as it, paper_components as c, paper_observations as p, quotient as q,
};
use vstd::prelude::*;

verus! {

pub open spec fn projection_typed<G,K,U>(types:t::Family<K,U>,coeffects:spec_fn(G)->IMap<K,U>)->bool {
    forall|a:G,key:K| #[trigger] coeffects(a).dom().contains(key) ==> types(key,coeffects(a)[key])
}
pub open spec fn registry_typed<G,N,K,U,I>(types:t::Family<K,U>,view:p::View<G,N,K,U,I>)->bool {
    forall|a:G,n:N,key:K| p::registered(view,a,n) && #[trigger] (view.registry)(a)[n].table.dom().contains(key)
        ==> types(key,(view.registry)(a)[n].table[key])
}
pub open spec fn typed_component<G,K,U,I>(types:t::Family<K,U>,eq:spec_fn(K,U,U)->bool,
    coeffects:spec_fn(G)->IMap<K,U>,family:q::IteratorFamily<G,I>,installs:spec_fn(I,G)->ISet<K>,component:c::Component<K,I>)->bool {
    projection_typed(types,coeffects) && c::component(eq,coeffects,family,installs,component)
}

/// No uniqueness assumption is needed for typing: every selectable owner is
/// in the same key-specific fiber, including malformed overlapping registries.
pub proof fn registry_projection<G,N,K,U,I>(types:t::Family<K,U>,view:p::View<G,N,K,U,I>,keys:ISet<K>)
    requires registry_typed(types,view),
    ensures projection_typed(types,|a:G|p::project(view,a,keys)),
{
    assert forall|a:G,key:K| #[trigger] p::project(view,a,keys).dom().contains(key)
        implies types(key,p::project(view,a,keys)[key]) by {
        assert(exists|n:N|p::owns(view,a,key,n));p::selected_owner_is_binding(view,a,key);
        let n=p::owner(view,a,key);assert(p::registered(view,a,n));
        assert((view.registry)(a)[n].table.dom().contains(key));
    }
}

/// Finite dependent contexts embed without changing a key's value type.
pub proof fn finite_projection<G,K,U>(types:t::Family<K,U>,tables:spec_fn(G)->Map<K,U>)
    requires forall|a:G| #[trigger] t::typed(types,tables(a)),
    ensures projection_typed(types,|a:G|t::embed(tables(a))),
{
    assert forall|a:G,key:K| #[trigger] t::embed(tables(a)).dom().contains(key)
        implies types(key,t::embed(tables(a))[key]) by {assert(t::typed(types,tables(a)));}
}

/// The actual codec, not the sum-carrier label, recovers the represented Rust
/// value type. The successful access keeps its original encoded value.
pub proof fn typed_access<G,K,U,V>(types:t::Family<K,U>,coeffects:spec_fn(G)->IMap<K,U>,codec:t::FiberCodec<K,U,V>,a:G)
    requires projection_typed(types,coeffects),t::codec(types,codec),coeffects(a).dom().contains(codec.key),
    ensures (codec.decode)(coeffects(a)[codec.key]).is_some(),
        (codec.encode)((codec.decode)(coeffects(a)[codec.key]).unwrap())==coeffects(a)[codec.key],
{ }

/// All-input typing is a property of the supplied context interpretation.
/// Both the real forward result and the real returned inverse are again G;
/// this theorem neither invents an inverse nor turns a partial family total.
pub proof fn total_outputs_typed<G,K,U,I>(types:t::Family<K,U>,coeffects:spec_fn(G)->IMap<K,U>,family:q::IteratorFamily<G,I>,id:I,a:G,b:G)
    requires projection_typed(types,coeffects),
    ensures forall|key:K| #[trigger] coeffects(family(id,a).state).dom().contains(key)
            ==> types(key,coeffects(family(id,a).state)[key]),
        forall|key:K| #[trigger] coeffects((family(id,a).undo)(b)).dom().contains(key)
            ==> types(key,coeffects((family(id,a).undo)(b))[key]),
{ }

pub struct Example {pub flag:bool,pub count:int}
pub open spec fn example_table(a:Example)->Map<t::ExampleKey,t::ExampleValue> {
    Map::empty().insert(t::ExampleKey::Flag,t::ExampleValue::Flag(a.flag))
        .insert(t::ExampleKey::Count,t::ExampleValue::Count(a.count))
}
pub open spec fn example_projection(a:Example)->IMap<t::ExampleKey,t::ExampleValue> {t::embed(example_table(a))}
pub open spec fn example_family()->q::IteratorFamily<Example,bool> {
    |_:bool,a:Example|q::Iteration {state:Example {count:a.count+1,..a},
        undo:|b:Example|Example {count:b.count-1,..b},next:None}
}
pub open spec fn example_component()->c::Component<t::ExampleKey,bool> {
    c::Component {dependencies:ISet::full(),provisions:ISet::empty(),root:false}
}
pub open spec fn example_equal()->spec_fn(t::ExampleKey,t::ExampleValue,t::ExampleValue)->bool {
    |_:t::ExampleKey,a:t::ExampleValue,b:t::ExampleValue|a==b
}
pub proof fn example_interpretation()
    ensures projection_typed(|k,u|t::example_family(k,u),|a:Example|example_projection(a)),
        forall|a:Example| t::typed(|k,u|t::example_family(k,u),#[trigger] example_table(a)),
{
    assert forall|a:Example| t::typed(|k,u|t::example_family(k,u),#[trigger] example_table(a)) by {
        assert forall|key:t::ExampleKey| example_table(a).dom().contains(key)
            implies t::example_family(key,example_table(a)[key]) by {match key {t::ExampleKey::Flag=>{},t::ExampleKey::Count=>{}}}
    }
    finite_projection(|k,u|t::example_family(k,u),|a:Example|example_table(a));
}

pub proof fn example_observation(a:Example,b:Example)
    ensures c::observed(example_equal(),|g:Example|example_projection(g),ISet::full(),a,b)==(a==b),
{
    let eq=example_equal();let get=|g:Example|example_projection(g);
    if c::observed(eq,get,ISet::full(),a,b) {
        assert(get(a).dom().contains(t::ExampleKey::Flag));
        assert(get(a).dom().contains(t::ExampleKey::Count));
        assert(ISet::<t::ExampleKey>::full().contains(t::ExampleKey::Flag));
        assert(ISet::<t::ExampleKey>::full().contains(t::ExampleKey::Count));
        assert(eq(t::ExampleKey::Flag,get(a)[t::ExampleKey::Flag],get(b)[t::ExampleKey::Flag]));
        assert(eq(t::ExampleKey::Count,get(a)[t::ExampleKey::Count],get(b)[t::ExampleKey::Count]));
        assert(a.flag==b.flag);assert(a.count==b.count);
    }
}

/// An inhabited, nonempty heterogeneous interpretation with a value-changing
/// total component and its actual subtraction inverse. It supplies a typed
/// projection instance, not Definition 28's recursive effect/coeffect context.
pub proof fn heterogeneous_component()
    ensures typed_component(|k,u|t::example_family(k,u),example_equal(),|a:Example|example_projection(a),
            example_family(),|_:bool,_:Example|ISet::empty(),example_component()),
        (t::flag_codec().decode)(example_projection(Example {flag:true,count:4})[t::ExampleKey::Flag])==Some(true),
        (t::count_codec().decode)(example_projection(example_family()(false,Example {flag:true,count:4}).state)[t::ExampleKey::Count])==Some(5),
        (example_family()(false,Example {flag:true,count:4}).undo)(example_family()(false,Example {flag:true,count:4}).state)==(Example {flag:true,count:4}),
{
    example_interpretation();t::heterogeneous_family();
    let get=|a:Example|example_projection(a);let family=example_family();
    let component=example_component();let base=|a:Example,b:Example|c::observed(example_equal(),get,component.dependencies.union(component.provisions),a,b);
    assert(component.dependencies.union(component.provisions) =~= ISet::full());
    assert forall|a:Example,b:Example| #[trigger] base(a,b)==(a==b) by {example_observation(a,b);}
    let related=|_:bool,_:bool|true;
    assert(q::bisimulation(base,family,related));
    let names=ISet::<bool>::full();
    assert forall|id:bool| names.contains(id) implies {
        &&& q::iterator_related(base,family,id,id)
        &&& forall|a:Example| #[trigger] base((family(id,a).undo)(family(id,a).state),a)
        &&& forall|a:Example| #[trigger] family(id,a).next.is_some() ==> names.contains(family(id,a).next.unwrap())
    } by {assert(related(id,id));}
    assert(it::witnessed_closed(base,family,names));assert(names.contains(false));
    it::inductive_constructor(family,false);
}
}
