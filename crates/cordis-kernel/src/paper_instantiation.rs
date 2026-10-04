//! Definition 52's typed instantiation primitive over a supplied representation.
//!
//! Only fresh insertion of an Inactive component and retirement are represented;
//! there is no put operation accepting an arbitrary function-valued registry.
//! A separate background projection frames everything outside the registry.
//! This conditional primitive definition does not construct recursive Gamma,
//! prove Lemma 57's total witness, or promise future retention of a child.
//! `typed_instantiate` additionally binds the uniform value carrier to its
//! per-key dependent fibers; arbitrary IMap values are not presumed to be Sigma.
use crate::paper_components as c;
#[cfg(verus_keep_ghost)]
use crate::paper_observations as p;
use vstd::prelude::*;

verus! {

pub type Insert<G,N,K,I> = spec_fn(G,N,N,c::Component<K,I>)->Option<G>;

#[verifier::reject_recursive_types(G)]
#[verifier::reject_recursive_types(N)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(H)]
pub struct Editors<G,N,K,I,H> {
    pub insert:Insert<G,N,K,I>,
    pub retire:spec_fn(G,N)->Option<G>,
    pub background:spec_fn(G)->H,
}
pub struct Receipt<N> {pub child:N}
pub struct Landing<G,N,I> {
    pub state:G,
    pub name:N,
    pub inverse:Receipt<N>,
    pub next:Option<I>,
}

pub open spec fn inserted<G,N,K,V,I>(parent:N,component:c::Component<K,I>)->p::Fiber<G,N,K,V,I> {
    p::Fiber {component,parent:Some(parent),retired:false,table:IMap::empty(),theta:p::Theta::Inactive}
}
pub open spec fn enabled<G,N,K,V,I>(view:p::View<G,N,K,V,I>,a:G,parent:N,child:N,component:c::Component<K,I>)->bool {
    &&& p::registered(view,a,parent) && !p::registered(view,a,child)
    &&& forall|n:N| p::registered(view,a,n) ==>
        component.provisions.disjoint((view.registry)(a)[n].component.provisions)
}
/// Joint readback is injective; no surjectivity onto arbitrary Registry values
/// is required. H records the rest of G which neither primitive may change.
pub open spec fn faithful<G,N,K,V,I,H>(view:p::View<G,N,K,V,I>,background:spec_fn(G)->H)->bool {
    forall|a:G,b:G| #![trigger (view.registry)(a), (view.registry)(b)] (view.registry)(a)==(view.registry)(b) && background(a)==background(b) ==> a==b
}
pub open spec fn editor_laws<G,N,K,V,I,H>(view:p::View<G,N,K,V,I>,edit:Editors<G,N,K,I,H>)->bool {
    &&& faithful(view,edit.background)
    &&& forall|a:G,parent:N,child:N,component:c::Component<K,I>| {
        let out=#[trigger] (edit.insert)(a,parent,child,component);
        &&& out.is_some()==enabled(view,a,parent,child,component)
        &&& (out.is_some() ==> (view.registry)(out.unwrap())==(view.registry)(a).insert(child,inserted(parent,component))
            && (edit.background)(out.unwrap())==(edit.background)(a))
    }
    &&& forall|a:G,child:N| {
        let out=#[trigger] (edit.retire)(a,child);
        &&& out.is_some()==p::registered(view,a,child)
        &&& (out.is_some() ==> (view.registry)(out.unwrap())==(view.registry)(a).insert(child,
                p::Fiber {retired:true,..(view.registry)(a)[child]})
            && (edit.background)(out.unwrap())==(edit.background)(a))
    }
}

/// The input subtype is the original full-carrier component predicate, with
/// the child's interpretation and the actual component, not a local syntax
/// membership check or a witness restricted to the current successful state.
pub open spec fn typed_component<G,N,K,V,I>(eq:spec_fn(K,V,V)->bool,view:p::View<G,N,K,V,I>,
    installs:spec_fn(N,I,G)->ISet<K>,child:N,component:c::Component<K,I>)->bool {
    c::component(eq,|a:G|p::project(view,a,ISet::full()),(view.families)(child),
        |id:I,a:G|installs(child,id,a),component)
}
pub open spec fn instantiate<G,N,K,V,I,H>(eq:spec_fn(K,V,V)->bool,view:p::View<G,N,K,V,I>,
    edit:Editors<G,N,K,I,H>,installs:spec_fn(N,I,G)->ISet<K>,a:G,parent:N,child:N,
    component:c::Component<K,I>,body:spec_fn(N)->Option<I>)->Option<Landing<G,N,I>> {
    if typed_component(eq,view,installs,child,component) && enabled(view,a,parent,child,component) {
        match (edit.insert)(a,parent,child,component) {
            None=>None,
            Some(state)=>Some(Landing {state,name:child,inverse:Receipt{child},next:body(child)}),
        }
    } else {None}
}
pub open spec fn undo<G,N,K,I,H>(edit:Editors<G,N,K,I,H>,receipt:Receipt<N>,a:G)->Option<G> {
    (edit.retire)(a,receipt.child)
}

/// Explicit dependent-Sigma entry point. The predicate holds on all G inputs,
/// so the component witness is not checked on a differently typed carrier or
/// only on the particular successful source state.
pub open spec fn typed_instantiate<G,N,K,V,I,H>(types:spec_fn(K,V)->bool,eq:spec_fn(K,V,V)->bool,view:p::View<G,N,K,V,I>,
    edit:Editors<G,N,K,I,H>,installs:spec_fn(N,I,G)->ISet<K>,a:G,parent:N,child:N,
    component:c::Component<K,I>,body:spec_fn(N)->Option<I>)->Option<Landing<G,N,I>> {
    if crate::paper_typed_context::projection_typed(types,|g:G|p::project(view,g,ISet::full())) {
        instantiate(eq,view,edit,installs,a,parent,child,component,body)
    }else{None}
}

pub proof fn typed_instantiation<G,N,K,V,I,H>(eq:spec_fn(K,V,V)->bool,view:p::View<G,N,K,V,I>,
    edit:Editors<G,N,K,I,H>,installs:spec_fn(N,I,G)->ISet<K>,a:G,parent:N,child:N,
    component:c::Component<K,I>,body:spec_fn(N)->Option<I>)
    requires editor_laws(view,edit),typed_component(eq,view,installs,child,component),enabled(view,a,parent,child,component),
    ensures instantiate(eq,view,edit,installs,a,parent,child,component,body).is_some(),
        {
            let y=instantiate(eq,view,edit,installs,a,parent,child,component,body).unwrap();
            &&& y.name==child && y.inverse.child==child && y.next==body(child)
            &&& (view.registry)(y.state)==(view.registry)(a).insert(child,inserted(parent,component))
            &&& (edit.background)(y.state)==(edit.background)(a)
            &&& (view.registry)(y.state)[child].component==component
            &&& child!=parent
        },
{
    assert((edit.insert)(a,parent,child,component).is_some());
}

pub proof fn dependent_typed_instantiation<G,N,K,V,I,H>(types:spec_fn(K,V)->bool,eq:spec_fn(K,V,V)->bool,view:p::View<G,N,K,V,I>,
    edit:Editors<G,N,K,I,H>,installs:spec_fn(N,I,G)->ISet<K>,a:G,parent:N,child:N,
    component:c::Component<K,I>,body:spec_fn(N)->Option<I>)
    requires editor_laws(view,edit),typed_component(eq,view,installs,child,component),enabled(view,a,parent,child,component),
        crate::paper_typed_context::projection_typed(types,|g:G|p::project(view,g,ISet::full())),
    ensures typed_instantiate(types,eq,view,edit,installs,a,parent,child,component,body).is_some(),
        {
            let y=typed_instantiate(types,eq,view,edit,installs,a,parent,child,component,body).unwrap();
            &&& y.name==child && y.inverse.child==child && y.next==body(child)
            &&& (view.registry)(y.state)==(view.registry)(a).insert(child,inserted(parent,component))
            &&& (edit.background)(y.state)==(edit.background)(a)
        },
{
    typed_instantiation(eq,view,edit,installs,a,parent,child,component,body);
}

/// A genuine missing binding remains failure. No arbitrary input is recovered
/// by treating a failed retirement as an identity map.
pub proof fn captured_retirement<G,N,K,V,I,H>(view:p::View<G,N,K,V,I>,edit:Editors<G,N,K,I,H>,receipt:Receipt<N>,a:G)
    requires editor_laws(view,edit),
    ensures undo(edit,receipt,a).is_some()==p::registered(view,a,receipt.child),
        undo(edit,receipt,a).is_some() ==> {
            let z=undo(edit,receipt,a).unwrap();
            &&& (view.registry)(z)==(view.registry)(a).insert(receipt.child,
                p::Fiber{retired:true,..(view.registry)(a)[receipt.child]})
            &&& (edit.background)(z)==(edit.background)(a)
        },
{ }

pub proof fn immediate_retirement<G,N,K,V,I,H>(eq:spec_fn(K,V,V)->bool,view:p::View<G,N,K,V,I>,
    edit:Editors<G,N,K,I,H>,installs:spec_fn(N,I,G)->ISet<K>,a:G,parent:N,child:N,
    component:c::Component<K,I>,body:spec_fn(N)->Option<I>)
    requires editor_laws(view,edit),typed_component(eq,view,installs,child,component),enabled(view,a,parent,child,component),
    ensures {
        let y=instantiate(eq,view,edit,installs,a,parent,child,component,body).unwrap();
        &&& instantiate(eq,view,edit,installs,a,parent,child,component,body).is_some()
        &&& undo(edit,y.inverse,y.state).is_some()
        &&& (view.registry)(undo(edit,y.inverse,y.state).unwrap())==(view.registry)(a).insert(child,
            p::Fiber{retired:true,..inserted(parent,component)})
        &&& (edit.background)(undo(edit,y.inverse,y.state).unwrap())==(edit.background)(a)
    },
{
    typed_instantiation(eq,view,edit,installs,a,parent,child,component,body);
    let y=instantiate(eq,view,edit,installs,a,parent,child,component,body).unwrap();
    assert(p::registered(view,y.state,child));
    captured_retirement(view,edit,y.inverse,y.state);
    assert((view.registry)(undo(edit,y.inverse,y.state).unwrap()) =~= (view.registry)(a).insert(child,
        p::Fiber{retired:true,..inserted(parent,component)}));
}

/// Presence/value equality per owner suffices for equality of the union only
/// when the old union is unambiguous; arbitrary selectors on ambiguous inputs
/// cannot silently be assumed stable under a metadata edit.
pub proof fn unchanged_bindings_projection<G,N,K,V,I>(view:p::View<G,N,K,V,I>,a:G,z:G,keys:ISet<K>)
    requires p::unambiguous(view,a),
        forall|n:N,k:K| p::lookup(view,a,n,k)==p::lookup(view,z,n,k),
    ensures p::unambiguous(view,z),p::project(view,a,keys)==p::project(view,z,keys),
{
    assert forall|k:K,n:N,m:N| p::owns(view,z,k,n) && p::owns(view,z,k,m) implies n==m by {
        assert(p::owns(view,a,k,n));assert(p::owns(view,a,k,m));
    }
    assert forall|k:K| p::project(view,a,keys).dom().contains(k)==p::project(view,z,keys).dom().contains(k) by {
        if p::project(view,a,keys).dom().contains(k) {let n=choose|n:N|p::owns(view,a,k,n);assert(p::owns(view,z,k,n));}
        if p::project(view,z,keys).dom().contains(k) {let n=choose|n:N|p::owns(view,z,k,n);assert(p::owns(view,a,k,n));}
    }
    assert forall|k:K| p::project(view,a,keys).dom().contains(k)
        implies p::project(view,a,keys)[k]==p::project(view,z,keys)[k] by {
        assert(exists|n:N|p::owns(view,a,k,n));assert(exists|n:N|p::owns(view,z,k,n));
        p::selected_owner_is_binding(view,a,k);p::selected_owner_is_binding(view,z,k);
        assert(p::owns(view,a,k,p::owner(view,z,k)));
        assert(p::owner(view,a,k)==p::owner(view,z,k));
        assert(p::lookup(view,a,p::owner(view,a,k),k)==p::lookup(view,z,p::owner(view,z,k),k));
    }
    assert(p::project(view,a,keys) =~= p::project(view,z,keys));
}

pub proof fn immediate_table_recovery<G,N,K,V,I,H>(eq:spec_fn(K,V,V)->bool,view:p::View<G,N,K,V,I>,
    edit:Editors<G,N,K,I,H>,installs:spec_fn(N,I,G)->ISet<K>,a:G,parent:N,child:N,
    component:c::Component<K,I>,body:spec_fn(N)->Option<I>,keys:ISet<K>)
    requires editor_laws(view,edit),typed_component(eq,view,installs,child,component),enabled(view,a,parent,child,component),p::unambiguous(view,a),
    ensures {
        let y=instantiate(eq,view,edit,installs,a,parent,child,component,body).unwrap();
        let z=undo(edit,y.inverse,y.state).unwrap();
        &&& p::project(view,y.state,keys)==p::project(view,a,keys)
        &&& p::project(view,z,keys)==p::project(view,a,keys)
        &&& p::registered(view,z,child) && (view.registry)(z)[child].retired
        &&& !p::registered(view,a,child)
    },
{
    immediate_retirement(eq,view,edit,installs,a,parent,child,component,body);
    typed_instantiation(eq,view,edit,installs,a,parent,child,component,body);
    let y=instantiate(eq,view,edit,installs,a,parent,child,component,body).unwrap();let z=undo(edit,y.inverse,y.state).unwrap();
    assert forall|n:N,k:K| p::lookup(view,a,n,k)==p::lookup(view,y.state,n,k) by {if n==child {assert(!p::registered(view,a,n));}}
    assert forall|n:N,k:K| p::lookup(view,a,n,k)==p::lookup(view,z,n,k) by {if n==child {assert(!p::registered(view,a,n));}}
    unchanged_bindings_projection(view,a,y.state,keys);unchanged_bindings_projection(view,a,z,keys);
}

/// A concrete image-closed representation, containing no arbitrary G -> G
/// fields. Active accumulators are interpreted as identity; roots are boolean
/// Unit indices. This is an inhabited instance of the local editing interface,
/// not an implementation of the recursive type equation for original Gamma.
pub struct Row {
    pub component:c::Component<bool,bool>,pub parent:Option<usize>,pub retired:bool,
    pub table:IMap<bool,int>,pub active:bool,
}
pub struct SmallState {pub rows:IMap<usize,Row>,pub background:int}
pub open spec fn row_view(row:Row)->p::Fiber<SmallState,usize,bool,int,bool> {
    p::Fiber {component:row.component,parent:row.parent,retired:row.retired,table:row.table,
        theta:if row.active {p::Theta::Active{accumulator:|a:SmallState|a,committed:ISet::empty()}}else{p::Theta::Inactive}}
}
pub open spec fn small_view()->p::View<SmallState,usize,bool,int,bool> {
    p::View {registry:|a:SmallState|IMap::new(|n:usize|a.rows.dom().contains(n),|n:usize|row_view(a.rows[n])),
        families:|_:usize|c::unit(),select_owner:|_:SmallState,_:bool|0}
}
pub open spec fn small_editors()->Editors<SmallState,usize,bool,bool,int> {
    Editors {
        background:|a:SmallState|a.background,
        insert:|a:SmallState,parent:usize,child:usize,component:c::Component<bool,bool>| {
            if enabled(small_view(),a,parent,child,component) {
                Some(SmallState {rows:a.rows.insert(child,Row{component,parent:Some(parent),retired:false,table:IMap::empty(),active:false}),..a})
            }else{None}
        },
        retire:|a:SmallState,child:usize| {
            if a.rows.dom().contains(child) {Some(SmallState {rows:a.rows.insert(child,Row{retired:true,..a.rows[child]}),..a})}else{None}
        },
    }
}

pub proof fn small_representation_is_faithful()
    ensures faithful(small_view(),small_editors().background),
{
    let view=small_view();
    assert forall|a:SmallState,b:SmallState| #![trigger (view.registry)(a), (view.registry)(b)] (view.registry)(a)==(view.registry)(b)
        && (small_editors().background)(a)==(small_editors().background)(b) implies a==b by {
        assert((view.registry)(a).dom() =~= a.rows.dom());
        assert((view.registry)(b).dom() =~= b.rows.dom());
        assert(a.rows.dom() == b.rows.dom());
        assert forall|n:usize| a.rows.dom().contains(n) implies a.rows[n]==b.rows[n] by {
            assert((view.registry)(a)[n]==row_view(a.rows[n]));
            assert((view.registry)(b)[n]==row_view(b.rows[n]));
            assert(row_view(a.rows[n])==row_view(b.rows[n]));
            assert(a.rows[n].active==b.rows[n].active);
        }
        assert(a.rows =~= b.rows);
    }
}
pub proof fn small_editors_satisfy_laws()
    ensures editor_laws(small_view(),small_editors()),
{
    small_representation_is_faithful();let view=small_view();let edit=small_editors();
    assert forall|a:SmallState,parent:usize,child:usize,component:c::Component<bool,bool>| {
        let out=#[trigger] (edit.insert)(a,parent,child,component);
        &&& out.is_some()==enabled(view,a,parent,child,component)
        &&& (out.is_some() ==> (view.registry)(out.unwrap())==(view.registry)(a).insert(child,inserted(parent,component))
            && (edit.background)(out.unwrap())==(edit.background)(a))
    } by {
        if enabled(view,a,parent,child,component) {
            let z=(edit.insert)(a,parent,child,component).unwrap();
            assert((view.registry)(z) =~= (view.registry)(a).insert(child,inserted(parent,component)));
        }
    }
    assert forall|a:SmallState,child:usize| {
        let out=#[trigger] (edit.retire)(a,child);
        &&& out.is_some()==p::registered(view,a,child)
        &&& (out.is_some() ==> (view.registry)(out.unwrap())==(view.registry)(a).insert(child,
            p::Fiber {retired:true,..(view.registry)(a)[child]}) && (edit.background)(out.unwrap())==(edit.background)(a))
    } by {
        if p::registered(view,a,child) {
            let z=(edit.retire)(a,child).unwrap();
            assert((view.registry)(z) =~= (view.registry)(a).insert(child,p::Fiber{retired:true,..(view.registry)(a)[child]}));
        }
    }
}

pub open spec fn before()->SmallState {
    SmallState {rows:IMap::empty().insert(0,Row {
        component:c::Component{dependencies:ISet::empty(),provisions:ISet::empty().insert(true),root:false},
        parent:None,retired:false,table:IMap::empty().insert(true,7),active:true}),background:99}
}
pub open spec fn child_component()->c::Component<bool,bool> {
    c::Component{dependencies:ISet::empty().insert(true),provisions:ISet::empty().insert(false),root:true}
}
pub open spec fn no_installs(_n:usize,_id:bool,_a:SmallState)->ISet<bool> {ISet::empty()}

pub proof fn small_component_has_full_witness(child:usize)
    ensures typed_component(|_:bool,a:int,b:int|a==b,small_view(),|n:usize,id:bool,a:SmallState|no_installs(n,id,a),child,child_component()),
{
    let view=small_view();let comp=child_component();let eq=|_:bool,a:int,b:int|a==b;
    let projection=|a:SmallState|p::project(view,a,ISet::full());
    let base=|a:SmallState,b:SmallState|c::observed(eq,projection,comp.dependencies.union(comp.provisions),a,b);
    assert forall|a:SmallState| #[trigger] base(a,a) by { }
    c::unit_witnessed(base,comp.root);
}

/// A nonempty Active parent, fresh child, nonempty child interface and a real
/// name-dependent continuation exercise every public gate. Retirement leaves
/// the child registered and empty; it does not restore literal registry equality.
pub proof fn nonempty_typed_instantiation()
    ensures {
        let a=before();let view=small_view();let edit=small_editors();
        let out=typed_instantiate(|_:bool,_:int|true,|_:bool,x:int,y:int|x==y,view,edit,|n:usize,id:bool,s:SmallState|no_installs(n,id,s),
            a,0,1,child_component(),|n:usize|Some(n==1));
        &&& out.is_some() && out.unwrap().name==1 && out.unwrap().next==Some(true)
        &&& out.unwrap().inverse.child==1
        &&& undo(edit,out.unwrap().inverse,out.unwrap().state).is_some()
        &&& p::lookup(view,a,0,true)==Some(7)
        &&& p::project(view,undo(edit,out.unwrap().inverse,out.unwrap().state).unwrap(),ISet::full())==p::project(view,a,ISet::full())
        &&& !p::registered(view,a,1)
        &&& p::registered(view,undo(edit,out.unwrap().inverse,out.unwrap().state).unwrap(),1)
        &&& (view.registry)(undo(edit,out.unwrap().inverse,out.unwrap().state).unwrap())[1].retired
        &&& undo(edit,Receipt{child:1usize},a).is_none()
    },
{
    let a=before();let view=small_view();let edit=small_editors();let comp=child_component();
    small_editors_satisfy_laws();small_component_has_full_witness(1);
    assert(crate::paper_typed_context::projection_typed(|_:bool,_:int|true,|g:SmallState|p::project(view,g,ISet::full())));
    assert forall|n:usize| p::registered(view,a,n) implies comp.provisions.disjoint((view.registry)(a)[n].component.provisions) by {assert(n==0);}
    assert(p::unambiguous(view,a));
    typed_instantiation(|_:bool,x:int,y:int|x==y,view,edit,|n:usize,id:bool,s:SmallState|no_installs(n,id,s),a,0,1,comp,|n:usize|Some(n==1));
    immediate_retirement(|_:bool,x:int,y:int|x==y,view,edit,|n:usize,id:bool,s:SmallState|no_installs(n,id,s),a,0,1,comp,|n:usize|Some(n==1));
    immediate_table_recovery(|_:bool,x:int,y:int|x==y,view,edit,|n:usize,id:bool,s:SmallState|no_installs(n,id,s),a,0,1,comp,|n:usize|Some(n==1),ISet::full());
}

} // verus!
