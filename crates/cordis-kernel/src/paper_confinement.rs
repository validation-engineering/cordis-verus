//! Definition 55, separated from the stronger implementation write frame.
//!
//! The printed read clause ranges over the source registry. Its symmetric,
//! presence-aware strengthening is named separately: adding a foreign binding
//! can distinguish the two. All map and iterator contracts below are total;
//! they neither totalize strict failures nor assert that a recursive context
//! model exists. A child exception denotes a supplied primitive, not a whole
//! execution or a supplied successor-simulation theorem.
#[cfg(verus_keep_ghost)]
use crate::{
    iterator_independence as reach, iterators as it, paper_components as c,
    paper_observations as p, quotient as q, semantics as s, Port,
};
use vstd::prelude::*;

verus! {

/// Both actors must be present. No equality of registries, declarations or
/// lifecycle fields is a premise for comparing the tables they can read.
pub open spec fn actor_pair<G,N,K,V,I>(view:p::View<G,N,K,V,I>,a:G,b:G,n:N)->bool {
    p::registered(view,a,n) && p::registered(view,b,n)
}

/// The source-indexed literal reading of Definition 55(2). An absent foreign
/// fiber contributes no binding, through `lookup`, just like an empty table.
pub open spec fn literal_reads<G,N,K,V,I>(view:p::View<G,N,K,V,I>,a:G,b:G,n:N,d:ISet<K>)->bool {
    &&& actor_pair(view,a,b,n)
    &&& (view.registry)(a)[n].table==(view.registry)(b)[n].table
    &&& forall|m:N,k:K| p::registered(view,a,m) && d.contains(k)
        ==> p::lookup(view,a,m,k)==p::lookup(view,b,m,k)
}

/// A symmetric reading compares presence and values at every possible owner.
/// Empty or absent foreign entries remain indistinguishable at these keys.
pub open spec fn symmetric_reads<G,N,K,V,I>(view:p::View<G,N,K,V,I>,a:G,b:G,n:N,d:ISet<K>)->bool {
    &&& actor_pair(view,a,b,n)
    &&& (view.registry)(a)[n].table==(view.registry)(b)[n].table
    &&& forall|m:N,k:K| d.contains(k) ==> p::lookup(view,a,m,k)==p::lookup(view,b,m,k)
}

pub proof fn symmetric_implies_literal<G,N,K,V,I>(view:p::View<G,N,K,V,I>,a:G,b:G,n:N,d:ISet<K>)
    requires symmetric_reads(view,a,b,n,d),
    ensures literal_reads(view,a,b,n,d),literal_reads(view,b,a,n,d),
{ }

pub proof fn bidirectional_literal<G,N,K,V,I>(view:p::View<G,N,K,V,I>,a:G,b:G,n:N,d:ISet<K>)
    ensures (literal_reads(view,a,b,n,d) && literal_reads(view,b,a,n,d))
        ==symmetric_reads(view,a,b,n,d),
{
    if symmetric_reads(view,a,b,n,d) {symmetric_implies_literal(view,a,b,n,d);}
    if literal_reads(view,a,b,n,d) && literal_reads(view,b,a,n,d) {
        assert forall|m:N,k:K| d.contains(k)
            implies p::lookup(view,a,m,k)==p::lookup(view,b,m,k) by {
            if p::registered(view,a,m) {
                assert(p::lookup(view,a,m,k)==p::lookup(view,b,m,k));
            } else if p::registered(view,b,m) {
                assert(p::lookup(view,b,m,k)==p::lookup(view,a,m,k));
            }
        }
    }
}

/// Definition 55(1): all non-table fiber fields are unchanged. Foreign tables
/// may change presence as well as values inside `d`; only its complement is
/// framed. The actor's table is unrestricted by confinement alone.
pub open spec fn writes<G,N,K,V,I>(view:p::View<G,N,K,V,I>,a:G,z:G,n:N,d:ISet<K>)->bool {
    &&& actor_pair(view,a,z,n)
    &&& (view.registry)(a).dom()==(view.registry)(z).dom()
    &&& forall|m:N| p::registered(view,a,m)
        ==> p::exact_metadata(view,m,(view.registry)(a)[m],(view.registry)(z)[m])
    &&& forall|m:N,k:K| p::registered(view,a,m) && m!=n && !d.contains(k)
        ==> p::lookup(view,a,m,k)==p::lookup(view,z,m,k)
}

/// Fixed-declaration presentation. This does not require every registry state
/// to carry the same declaration; callers choose the interface parameter.
pub open spec fn map_confined<G,N,K,V,I>(view:p::View<G,N,K,V,I>,n:N,d:ISet<K>,f:spec_fn(G)->G)->bool {
    &&& forall|a:G| p::registered(view,a,n) ==> writes(view,a,f(a),n,d)
    &&& forall|a:G,b:G| #[trigger] literal_reads(view,a,b,n,d) ==> literal_reads(view,f(a),f(b),n,d)
}

/// The literal registry-indexed definition reads `d_n` from each source state.
/// In particular, the read antecedent does not compare either declaration or
/// any other control field of the two inputs.
pub open spec fn map_confined_from_registry<G,N,K,V,I>(view:p::View<G,N,K,V,I>,n:N,f:spec_fn(G)->G)->bool {
    &&& forall|a:G| p::registered(view,a,n)
        ==> writes(view,a,f(a),n,(view.registry)(a)[n].component.dependencies)
    &&& forall|a:G,b:G| #[trigger] literal_reads(view,a,b,n,(view.registry)(a)[n].component.dependencies)
        ==> literal_reads(view,f(a),f(b),n,(view.registry)(a)[n].component.dependencies)
}

/// The boolean classifier is an independently supplied instantiation-primitive
/// relation for an iterator at this actor. It is not a confinement conclusion.
/// Every ordinary reachable iterator is constrained at all inputs, including
/// every actual returned inverse as a whole total map on `G`.
pub open spec fn effect_confined<G,N,K,V,I>(view:p::View<G,N,K,V,I>,n:N,root:I,child:spec_fn(N,I)->bool)->bool {
    let family=(view.families)(n);
    forall|id:I| reach::reach(family,root).contains(id) ==> child(n,id) || {
        &&& map_confined_from_registry(view,n,reach::forward(family,id))
        &&& forall|input:G| map_confined_from_registry(view,n,(#[trigger] family(id,input)).undo)
    }
}

pub proof fn ordinary_reachable_obligations<G,N,K,V,I>(view:p::View<G,N,K,V,I>,n:N,root:I,
    child:spec_fn(N,I)->bool,id:I,input:G)
    requires effect_confined(view,n,root,child),reach::reach((view.families)(n),root).contains(id),!child(n,id),
    ensures map_confined_from_registry(view,n,reach::forward((view.families)(n),id)),
        map_confined_from_registry(view,n,((view.families)(n)(id,input)).undo),
{ }

pub type ReadState=IMap<usize,IMap<usize,int>>;
pub open spec fn read_family()->q::IteratorFamily<ReadState,()> {
    |_:(),a:ReadState|q::Iteration {state:a,undo:|b:ReadState|b,next:None}
}
pub open spec fn read_keys()->ISet<usize> {ISet::empty().insert(7)}
pub open spec fn read_view()->p::View<ReadState,usize,usize,int,()> {
    p::View {registry:|a:ReadState|IMap::new(|n:usize|a.dom().contains(n),|n:usize|p::Fiber {
        component:c::Component {dependencies:if n==0 {read_keys()}else{ISet::empty()},
            provisions:if n==1 {read_keys()}else{ISet::empty()},root:()},
        parent:None,retired:false,table:a[n],theta:p::Theta::Inactive,
    }),families:|_:usize|read_family(),select_owner:|_:ReadState,_:usize|1usize}
}
pub open spec fn read_before()->ReadState {IMap::empty().insert(0,IMap::empty())}
pub open spec fn read_after()->ReadState {read_before().insert(1,IMap::empty().insert(7,42))}

/// A concrete inhabited carrier with an actual nonempty actor registry. This
/// pair is a definition-level counterexample, not a claimed lifecycle trace.
pub proof fn source_index_is_not_symmetric()
    ensures actor_pair(read_view(),read_before(),read_after(),0),
        (read_view().registry)(read_before()).dom().contains(0),
        p::lookup(read_view(),read_after(),1,7)==Some(42),
        literal_reads(read_view(),read_before(),read_after(),0,read_keys()),
        !literal_reads(read_view(),read_after(),read_before(),0,read_keys()),
        !symmetric_reads(read_view(),read_before(),read_after(),0,read_keys()),
{
    let v=read_view();let a=read_before();let b=read_after();
    assert forall|m:usize,k:usize| p::registered(v,a,m) && read_keys().contains(k)
        implies p::lookup(v,a,m,k)==p::lookup(v,b,m,k) by {assert(m==0);}
    assert(p::lookup(v,a,1,7)==None);
    assert(p::lookup(v,b,1,7)==Some(42));
}

/// Unlike the stronger implementation frame, the printed Writes clause allows
/// a foreign dependency binding to appear while that foreign fiber stays put.
pub proof fn writes_allow_dependency_presence()
    ensures {
        let a=read_before().insert(1,IMap::empty());let b=read_after();
        &&& writes(read_view(),a,b,0,read_keys())
        &&& (read_view().registry)(a).dom()==(read_view().registry)(b).dom()
        &&& (read_view().registry)(a)[1].table.dom()!=(read_view().registry)(b)[1].table.dom()
    },
{
    let v=read_view();let a=read_before().insert(1,IMap::empty());let b=read_after();
    it::equality_respect(read_family(),());
    assert forall|m:usize| p::registered(v,a,m)
        implies p::exact_metadata(v,m,(v.registry)(a)[m],(v.registry)(b)[m]) by { }
    assert forall|m:usize,k:usize| p::registered(v,a,m) && m!=0 && !read_keys().contains(k)
        implies p::lookup(v,a,m,k)==p::lookup(v,b,m,k) by {assert(m==1);assert(k!=7);}
    assert(!(v.registry)(a)[1].table.dom().contains(7));
    assert((v.registry)(b)[1].table.dom().contains(7));
}

/// The implementation's foreign-domain-preserving frame implies the printed
/// Writes clause. The converse is intentionally false, as the example above
/// shows. This adapter makes no claim about Definition 55's separate Reads.
pub proof fn implementation_writes<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize)
    requires s::shaped(a),s::shaped(z),s::registered(a,actor),s::confined_write(a,z,actor),
    ensures writes(p::from_model(model),a,z,actor,a.control.fibers[actor].dependencies),
{
    let view=p::from_model(model);let d=a.control.fibers[actor].dependencies;
    assert(actor_pair(view,a,z,actor));
    assert((view.registry)(a).dom() =~= (view.registry)(z).dom());
    assert forall|m:usize| p::registered(view,a,m)
        implies p::exact_metadata(view,m,(view.registry)(a)[m],(view.registry)(z)[m]) by {
        assert(s::registered(a,m));
        p::strong_frame_metadata(model,a,z,m);
    }
    assert forall|m:usize,k:Port| p::registered(view,a,m) && m!=actor && !d.contains(k)
        implies p::lookup(view,a,m,k)==p::lookup(view,z,m,k) by {
        assert(s::registered(a,m));
        assert(a.tables[m].dom()==z.tables[m].dom());
        if a.tables[m].dom().contains(k) {assert(a.tables[m][k]==z.tables[m][k]);}
    }
}

} // verus!
