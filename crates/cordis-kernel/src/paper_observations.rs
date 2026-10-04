//! Definition 58 and Equation 54 over an explicitly supplied Gamma carrier.
//!
//! Function fields use Definition 34: arbitrary iterator indices are interpreted
//! by greatest bisimulation, and accumulators are actual total G -> G maps.
//! This interface neither constructs Definition 28's recursive Gamma nor turns
//! a strict partial interpreter into such a total model. Its projection includes
//! every lifecycle phase. Structural Child simulation is a separate obligation.
#[cfg(verus_keep_ghost)]
use crate::{
    functional_quotient as fq, iterators as it, observation as o, projection, refinement as r,
    rule_frames as frames, semantics as s, Binding, Phase, Port,
};
use crate::{paper_components as c, quotient as q};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(G)]
#[verifier::reject_recursive_types(N)]
#[verifier::reject_recursive_types(K)]
pub enum Theta<G,N,K,I> {
    Inactive,
    Loading {current:I,accumulator:spec_fn(G)->G,committed:ISet<(K,N)>},
    Active {accumulator:spec_fn(G)->G,committed:ISet<(K,N)>},
    Unloading {accumulator:spec_fn(G)->G,committed:ISet<(K,N)>},
}
#[verifier::reject_recursive_types(G)]
#[verifier::reject_recursive_types(N)]
#[verifier::reject_recursive_types(K)]
pub struct Fiber<G,N,K,V,I> {
    pub component:c::Component<K,I>,
    pub parent:Option<N>,
    pub retired:bool,
    pub table:IMap<K,V>,
    pub theta:Theta<G,N,K,I>,
}
pub type Registry<G,N,K,V,I> = IMap<N,Fiber<G,N,K,V,I>>;

#[verifier::reject_recursive_types(G)]
#[verifier::reject_recursive_types(N)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(I)]
pub struct View<G,N,K,V,I> {
    pub registry:spec_fn(G)->Registry<G,N,K,V,I>,
    pub families:spec_fn(N)->q::IteratorFamily<G,I>,
    /// Tie breaker on malformed overlapping registries. `owner` checks that it
    /// selects an actual binding, so no validity is assumed of this function.
    pub select_owner:spec_fn(G,K)->N,
}

pub open spec fn registered<G,N,K,V,I>(view:View<G,N,K,V,I>,a:G,n:N)->bool {(view.registry)(a).dom().contains(n)}
pub open spec fn lookup<G,N,K,V,I>(view:View<G,N,K,V,I>,a:G,n:N,k:K)->Option<V> {
    if registered(view,a,n) && (view.registry)(a)[n].table.dom().contains(k) {Some((view.registry)(a)[n].table[k])}else{None}
}
pub open spec fn owns<G,N,K,V,I>(view:View<G,N,K,V,I>,a:G,k:K,n:N)->bool {lookup(view,a,n,k).is_some()}
pub open spec fn owner<G,N,K,V,I>(view:View<G,N,K,V,I>,a:G,k:K)->N {
    if owns(view,a,k,(view.select_owner)(a,k)) {(view.select_owner)(a,k)}else{choose|n:N|owns(view,a,k,n)}
}
pub open spec fn unambiguous<G,N,K,V,I>(view:View<G,N,K,V,I>,a:G)->bool {
    forall|k:K,n:N,m:N| owns(view,a,k,n) && owns(view,a,k,m) ==> n==m
}
/// On a well-formed registry ownership is unique. No Active-only publication
/// filter occurs here; arbitrary malformed overlapping owners use a choice.
pub open spec fn project<G,N,K,V,I>(view:View<G,N,K,V,I>,a:G,keys:ISet<K>)->IMap<K,V> {
    IMap::new(|k:K|keys.contains(k) && exists|n:N|owns(view,a,k,n),
        |k:K|(view.registry)(a)[owner(view,a,k)].table[k])
}
pub open spec fn observed<G,N,K,V,I>(eq:spec_fn(K,V,V)->bool,view:View<G,N,K,V,I>,a:G,b:G)->bool {
    o::context_equal(eq,ISet::full(),project(view,a,ISet::full()),project(view,b,ISet::full()))
}

pub proof fn selected_owner_is_binding<G,N,K,V,I>(view:View<G,N,K,V,I>,a:G,k:K)
    requires exists|n:N|owns(view,a,k,n),
    ensures owns(view,a,k,owner(view,a,k)),
{ }

/// A selector is merely a representation choice on malformed registries.
/// Changing it cannot change a well-defined union with unique owners.
pub proof fn unique_projection_ignores_selector<G,N,K,V,I>(view:View<G,N,K,V,I>,a:G,keys:ISet<K>,selector:spec_fn(G,K)->N)
    requires unambiguous(view,a),
    ensures project(view,a,keys)==project(View{select_owner:selector,..view},a,keys),
{
    let other=View{select_owner:selector,..view};
    assert forall|k:K| project(view,a,keys).dom().contains(k)
        implies project(view,a,keys)[k]==project(other,a,keys)[k] by {
        assert(exists|n:N|owns(view,a,k,n));
        selected_owner_is_binding(view,a,k);
        assert(owns(other,a,k,owner(view,a,k)));
        assert(exists|n:N|owns(other,a,k,n));
        selected_owner_is_binding(other,a,k);
        assert(owns(view,a,k,owner(other,a,k)));
        assert(owner(view,a,k)==owner(other,a,k));
    }
    assert forall|k:K| project(view,a,keys).dom().contains(k)==project(other,a,keys).dom().contains(k) by {
        if project(view,a,keys).dom().contains(k) {
            let n=choose|n:N|owns(view,a,k,n);assert(owns(other,a,k,n));
        }
        if project(other,a,keys).dom().contains(k) {
            let n=choose|n:N|owns(other,a,k,n);assert(owns(view,a,k,n));
        }
    }
    assert(project(view,a,keys) =~= project(other,a,keys));
}

pub open spec fn theta_related<G,N,K,I>(base:spec_fn(G,G)->bool,family:q::IteratorFamily<G,I>,
    left:Theta<G,N,K,I>,right:Theta<G,N,K,I>)->bool {
    match (left,right) {
        (Theta::Inactive,Theta::Inactive)=>true,
        (Theta::Loading {current:i,accumulator:g,committed:a},Theta::Loading {current:j,accumulator:h,committed:b})=>
            a==b && q::iterator_related(base,family,i,j) && o::related_maps(base,g,h),
        (Theta::Active {accumulator:g,committed:a},Theta::Active {accumulator:h,committed:b})=>a==b && o::related_maps(base,g,h),
        (Theta::Unloading {accumulator:g,committed:a},Theta::Unloading {accumulator:h,committed:b})=>a==b && o::related_maps(base,g,h),
        _=>false,
    }
}
pub open spec fn fields_related<G,N,K,V,I>(base:spec_fn(G,G)->bool,view:View<G,N,K,V,I>,n:N,
    left:Fiber<G,N,K,V,I>,right:Fiber<G,N,K,V,I>)->bool {
    &&& left.parent==right.parent && left.retired==right.retired
    &&& left.component.dependencies==right.component.dependencies
    &&& left.component.provisions==right.component.provisions
    &&& q::iterator_related(base,(view.families)(n),left.component.root,right.component.root)
    &&& theta_related(base,(view.families)(n),left.theta,right.theta)
}
/// Exact semantic equality for Writes. Function identities are interpreted;
/// it does not silently replace extensional equality by a token comparison.
pub open spec fn exact_metadata<G,N,K,V,I>(view:View<G,N,K,V,I>,n:N,
    left:Fiber<G,N,K,V,I>,right:Fiber<G,N,K,V,I>)->bool {
    fields_related(|a:G,b:G|a==b,view,n,left,right)
}
/// Equation 54. The base for function fields is all-table observation, not
/// observation of only the table belonging to the field's owner.
pub open spec fn related<G,N,K,V,I>(eq:spec_fn(K,V,V)->bool,view:View<G,N,K,V,I>,a:G,b:G)->bool {
    &&& observed(eq,view,a,b)
    &&& (view.registry)(a).dom()==(view.registry)(b).dom()
    &&& forall|n:N| registered(view,a,n) ==> fields_related(
        |x:G,y:G|observed(eq,view,x,y),view,n,(view.registry)(a)[n],(view.registry)(b)[n])
}

/// The whole-state relation licenses application of the actual function
/// fields at arbitrary related contexts, not merely at the compared states.
pub proof fn accumulator_application<G,N,K,V,I>(eq:spec_fn(K,V,V)->bool,
    view:View<G,N,K,V,I>,a:G,b:G,n:N,x:G,y:G)
    requires related(eq,view,a,b),registered(view,a,n),observed(eq,view,x,y),
    ensures observed(eq,view,
        theta_accumulator((view.registry)(a)[n].theta)(x),theta_accumulator((view.registry)(b)[n].theta)(y)),
{
    let base=|u:G,v:G|observed(eq,view,u,v);
    assert(fields_related(base,view,n,(view.registry)(a)[n],(view.registry)(b)[n]));
    match ((view.registry)(a)[n].theta,(view.registry)(b)[n].theta) {
        (Theta::Inactive,Theta::Inactive)=>{},
        (Theta::Loading{current:_,accumulator:g,committed:_},Theta::Loading{current:_,accumulator:h,committed:_})|
        (Theta::Active{accumulator:g,committed:_},Theta::Active{accumulator:h,committed:_})|
        (Theta::Unloading{accumulator:g,committed:_},Theta::Unloading{accumulator:h,committed:_})=>{
            assert(o::related_maps(base,g,h));assert(base(g(x),h(y)));
        },
        _=>{},
    }
}

pub proof fn root_application<G,N,K,V,I>(eq:spec_fn(K,V,V)->bool,
    view:View<G,N,K,V,I>,a:G,b:G,n:N,x:G,y:G)
    requires related(eq,view,a,b),registered(view,a,n),observed(eq,view,x,y),
    ensures {
        let family=(view.families)(n);let left=family((view.registry)(a)[n].component.root,x);
        let right=family((view.registry)(b)[n].component.root,y);
        let base=|u:G,v:G|observed(eq,view,u,v);
        &&& base(left.state,right.state)
        &&& o::related_maps(base,left.undo,right.undo)
        &&& q::continuation(|i:I,j:I|q::iterator_related(base,family,i,j),left.next,right.next)
    },
{
    let base=|u:G,v:G|observed(eq,view,u,v);let family=(view.families)(n);
    let i=(view.registry)(a)[n].component.root;let j=(view.registry)(b)[n].component.root;
    assert(fields_related(base,view,n,(view.registry)(a)[n],(view.registry)(b)[n]));
    q::iterator_unfolding(base,family,i,j);
    assert(q::iterator_clause(base,family,i,j));
    assert(base(family(i,x).state,family(j,y).state));
}

pub open spec fn committed(bindings:ISet<Binding>)->ISet<(Port,usize)> {
    ISet::new(|pair:(Port,usize)|bindings.contains(Binding {key:pair.0.key,realm:pair.0.realm,provider:pair.1}))
}
pub open spec fn model_fiber<V>(model:s::Model<V>,a:s::State<V>,n:usize)->Fiber<s::State<V>,usize,Port,V,nat> {
    let f=a.control.fibers[n];let g=fq::accumulator(model,a.accumulators[n]);let view=committed(f.committed);
    Fiber {component:c::Component {dependencies:f.dependencies,provisions:f.provisions,root:a.effects[n]},
        parent:f.parent,retired:f.retired,table:a.tables[n],
        theta:match f.phase {
            Phase::Inactive=>Theta::Inactive,
            Phase::Loading=>Theta::Loading {current:a.iterators[n].unwrap(),accumulator:g,committed:view},
            Phase::Active=>Theta::Active {accumulator:g,committed:view},
            Phase::Unloading=>Theta::Unloading {accumulator:g,committed:view},
        }}
}
pub open spec fn from_model<V>(model:s::Model<V>)->View<s::State<V>,usize,Port,V,nat> {
    View {registry:|a:s::State<V>|IMap::new(|n:usize|s::registered(a,n),|n:usize|model_fiber(model,a,n)),
        families:|n:usize|fq::family(model,n),select_owner:|a:s::State<V>,k:Port|projection::owner(a,k)}
}

pub proof fn strong_frame_metadata<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,n:usize)
    requires s::shaped(a),s::shaped(z),s::registered(a,n),
        a.control==z.control,a.effects==z.effects,a.iterators==z.iterators,a.accumulators==z.accumulators,
    ensures exact_metadata(from_model(model),n,(from_model(model).registry)(a)[n],(from_model(model).registry)(z)[n]),
{
    it::equality_respect(fq::family(model,n),a.effects[n]);
    if a.control.fibers[n].phase==Phase::Loading {it::equality_respect(fq::family(model,n),a.iterators[n].unwrap());}
}

pub proof fn model_projection<V>(model:s::Model<V>,a:s::State<V>,keys:ISet<Port>)
    ensures project(from_model(model),a,keys)==projection::project(a,keys),
{
    let view=from_model(model);
    assert forall|k:Port,n:usize| #[trigger] owns(view,a,k,n)==projection::owns(a,k,n) by { }
    assert forall|k:Port| project(view,a,keys).dom().contains(k)
        implies project(view,a,keys)[k]==projection::project(a,keys)[k] by {
        assert(exists|n:usize|projection::owns(a,k,n));
        assert(projection::owns(a,k,projection::owner(a,k)));
        assert(owns(view,a,k,projection::owner(a,k)));
        assert(owner(view,a,k)==projection::owner(a,k));
    }
    assert forall|k:Port| project(view,a,keys).dom().contains(k)==projection::project(a,keys).dom().contains(k) by {
        if project(view,a,keys).dom().contains(k) {
            let n=choose|n:usize|owns(view,a,k,n);assert(projection::owns(a,k,n));
        }
        if projection::project(a,keys).dom().contains(k) {
            let n=choose|n:usize|projection::owns(a,k,n);assert(owns(view,a,k,n));
        }
    }
    assert(project(view,a,keys) =~= projection::project(a,keys));
}

/// Existing model observations instantiate the generic function-field API.
/// Iterator IDs, inverse tokens and accumulator lengths may differ already in
/// the premise; the adapter never tightens them back to literal equality.
pub proof fn model_related<V>(eq:spec_fn(Port,V,V)->bool,model:s::Model<V>,a:s::State<V>,b:s::State<V>)
    requires s::shaped(a),s::shaped(b),fq::related(eq,model,a,b),
    ensures related(eq,from_model(model),a,b),
{
    let view=from_model(model);
    assert forall|x:s::State<V>,y:s::State<V>| #[trigger] observed(eq,view,x,y)==fq::observed(eq,x,y) by {
        model_projection(model,x,ISet::full());model_projection(model,y,ISet::full());
    }
    assert((|x:s::State<V>,y:s::State<V>|observed(eq,view,x,y)) =~= (|x:s::State<V>,y:s::State<V>|fq::observed(eq,x,y)));
    assert((view.registry)(a).dom() =~= a.control.fibers.dom());
    assert((view.registry)(b).dom() =~= b.control.fibers.dom());
    assert(observed(eq,view,a,b));
    assert forall|n:usize| registered(view,a,n) implies fields_related(
        |x:s::State<V>,y:s::State<V>|observed(eq,view,x,y),view,n,(view.registry)(a)[n],(view.registry)(b)[n]) by {
        assert(s::registered(a,n));
        assert(fq::iterator_related(eq,model,n,a.effects[n],b.effects[n]));
        assert(fq::continuations(eq,model,n,a.iterators[n],b.iterators[n]));
        assert(fq::accumulators_related(eq,model,a.accumulators[n],b.accumulators[n]));
        if a.control.fibers[n].phase==Phase::Loading {assert(a.iterators[n].is_some());assert(b.iterators[n].is_some());}
    }
}

pub open spec fn paper_rule(rule:r::Rule)->bool {
    match rule {r::Rule::Insert|r::Rule::Retire|r::Rule::Remove|r::Rule::Begin|r::Rule::Iter|
        r::Rule::Finish|r::Rule::Divert|r::Rule::Leave|r::Rule::Unload=>true,_=>false}
}
#[verifier::reject_recursive_types(G)]
#[verifier::reject_recursive_types(N)]
pub struct Execution<G,N> {
    pub states:spec_fn(nat)->G,
    pub labels:spec_fn(nat)->(N,crate::refinement::Rule),
    /// Some(t) has states 0..=t. None denotes an infinite execution.
    pub length:Option<nat>,
}
pub open spec fn has_state<G,N>(trace:Execution<G,N>,t:nat)->bool {trace.length.is_none() || t<=trace.length.unwrap()}
pub open spec fn has_step<G,N>(trace:Execution<G,N>,t:nat)->bool {trace.length.is_none() || t<trace.length.unwrap()}
pub open spec fn execution<G,N,K,V,I>(view:View<G,N,K,V,I>,
    step:spec_fn(G,G,N,r::Rule)->bool,trace:Execution<G,N>)->bool {
    &&& (view.registry)((trace.states)(0)).dom().is_empty()
    &&& forall|t:nat| has_step(trace,t) ==> paper_rule((trace.labels)(t).1)
        && step((trace.states)(t),(trace.states)(t+1),(trace.labels)(t).0,(trace.labels)(t).1)
}
pub open spec fn installed<G,N,K,V,I>(view:View<G,N,K,V,I>,a:G,n:N)->bool {
    registered(view,a,n) && match (view.registry)(a)[n].theta {Theta::Inactive=>false,_=>true}
}
/// Maximal installed intervals include final finite intervals and infinite
/// open tails; they do not assert eventual resolution of a finite prefix.
pub open spec fn episode<G,N,K,V,I>(view:View<G,N,K,V,I>,trace:Execution<G,N>,n:N,b:nat,u:Option<nat>)->bool {
    &&& b>0 && has_state(trace,b) && !installed(view,(trace.states)((b-1) as nat),n)
    &&& match u {
        Some(last)=>b<=last && has_state(trace,last)
            && (forall|t:nat| b<=t<=last ==> #[trigger] installed(view,(trace.states)(t),n))
            && (has_state(trace,last+1) ==> !installed(view,(trace.states)(last+1),n)),
        None=>trace.length.is_none() && forall|t:nat| t>=b ==> #[trigger] installed(view,(trace.states)(t),n),
    }
}
pub open spec fn finite_execution<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>)->Execution<s::State<V>,usize> {
    Execution {states:|t:nat|states[t as int],labels:|t:nat|labels[t as int],length:Some(labels.len())}
}
pub proof fn model_execution<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>)
    requires s::execution(model,states,labels),states.first().control.fibers.dom().is_empty(),
    ensures execution(from_model(model),|a:s::State<V>,b:s::State<V>,n:usize,r:r::Rule|s::step(model,a,b,n,r),finite_execution(states,labels)),
{
    assert forall|t:nat| has_step(finite_execution(states,labels),t) implies paper_rule(labels[t as int].1)
        && s::step(model,states[t as int],states[(t+1) as int],labels[t as int].0,labels[t as int].1) by {
        assert(s::step(model,states[t as int],states[t as int+1],labels[t as int].0,labels[t as int].1));
    }
}

pub proof fn model_episode<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,n:usize,b:nat,u:nat)
    requires states.len()==labels.len()+1,
    ensures episode(from_model(model),finite_execution(states,labels),n,b,Some(u))
        ==crate::lifecycle_ordering::episode(states,n,b as int,u as int),
{
    assert forall|t:int| 0<=t<states.len() implies
        installed(from_model(model),states[t],n)==crate::lifecycle_ordering::installed(states[t],n) by { }
    if episode(from_model(model),finite_execution(states,labels),n,b,Some(u)) {
        assert forall|t:int| b<=t<=u implies crate::lifecycle_ordering::installed(states[t],n) by {
            assert(installed(from_model(model),(finite_execution(states,labels).states)(t as nat),n));
        }
    }
    if crate::lifecycle_ordering::episode(states,n,b as int,u as int) {
        assert forall|t:nat| b<=t<=u implies #[trigger] installed(from_model(model),(finite_execution(states,labels).states)(t),n) by {
            assert(crate::lifecycle_ordering::installed(states[t as int],n));
        }
    }
}

pub open spec fn theta_accumulator<G,N,K,I>(theta:Theta<G,N,K,I>)->spec_fn(G)->G {
    match theta {Theta::Inactive=>|a:G|a,Theta::Loading{current:_,accumulator:g,committed:_}|
        Theta::Active{accumulator:g,committed:_}|Theta::Unloading{accumulator:g,committed:_}=>g}
}
pub open spec fn theta_current<G,N,K,I>(theta:Theta<G,N,K,I>)->Option<I> {
    match theta {Theta::Loading{current:i,accumulator:_,committed:_}=>Some(i),_=>None}
}
/// Equation 52: the `landing` argument records which actual Divert premise was
/// used. It is not an assertion that an iterator succeeds off the actual trace.
pub open spec fn state_map<G,N,K,V,I>(view:View<G,N,K,V,I>,source:G,n:N,rule:r::Rule,landing:bool)->spec_fn(G)->G {
    let theta=(view.registry)(source)[n].theta;
    if rule==r::Rule::Iter || rule==r::Rule::Finish || (rule==r::Rule::Divert && landing) {
        |a:G|(view.families)(n)(theta_current(theta).unwrap(),a).state
    } else if rule==r::Rule::Unload {theta_accumulator(theta)}else{|a:G|a}
}
/// The actual nine-rule factorization instantiates Equation 53, retaining both
/// the actual restoration stack and the bracket's frozen computed values.
pub proof fn model_factorization<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,n:usize,rule:r::Rule)
    requires s::shaped(a),s::step(model,a,z,n,rule),
    ensures z==frames::bracket(z,n,rule,state_map(from_model(model),a,n,rule,
        crate::entangled::lands(model,a,z,n,rule))(a)),
        forall|x:s::State<V>| #[trigger] state_map(from_model(model),a,n,rule,
            crate::entangled::lands(model,a,z,n,rule))(x)==frames::apply(model,frames::source(model,a,z,n,rule),x),
{
    frames::factorization(model,a,z,n,rule);
    assert forall|x:s::State<V>| #[trigger] state_map(from_model(model),a,n,rule,
        crate::entangled::lands(model,a,z,n,rule))(x)==frames::apply(model,frames::source(model,a,z,n,rule),x) by {
        if rule==r::Rule::Iter || rule==r::Rule::Finish || crate::entangled::lands(model,a,z,n,rule) {
            assert(s::registered(a,n));assert(a.control.fibers[n].phase==Phase::Loading);
        } else if rule==r::Rule::Unload {assert(s::registered(a,n));assert(a.control.fibers[n].phase==Phase::Unloading);}
    }
}

pub struct Example {pub visible:int,pub hidden:int,pub root:bool,pub pick:bool}
pub open spec fn example_accumulator(pick:bool)->spec_fn(Example)->Example {
    |a:Example|Example {hidden:if pick {9}else{7},..a}
}
pub open spec fn example_view()->View<Example,bool,bool,int,bool> {
    View {registry:|a:Example|IMap::empty().insert(false,Fiber {
        component:c::Component {dependencies:ISet::empty().insert(false),provisions:ISet::empty().insert(false),root:a.root},
        parent:None,retired:false,table:IMap::empty().insert(false,a.visible),
        theta:Theta::Active {accumulator:example_accumulator(a.pick),committed:ISet::empty()}}),
        families:|_:bool|c::unit(),select_owner:|_:Example,_:bool|false}
}
pub open spec fn example_a()->Example {Example {visible:4,hidden:3,root:false,pick:false}}
pub open spec fn example_b()->Example {Example {visible:4,hidden:6,root:true,pick:true}}
pub proof fn example_projection(a:Example)
    ensures project(example_view(),a,ISet::full())==IMap::<bool,int>::empty().insert(false,a.visible),
{
    let view=example_view();
    assert(owns(view,a,false,false));
    assert(owner(view,a,false)==false);
    assert(project(view,a,ISet::full()) =~= IMap::<bool,int>::empty().insert(false,a.visible));
}
/// Nonempty tables, different boolean effect indices, and extensionally
/// different accumulator functions satisfy Equation 54. No literal index or
/// accumulator equality is used to make the relation hold.
pub proof fn nonliteral_fields_example()
    ensures related(|_:bool,a:int,b:int|a==b,example_view(),example_a(),example_b()),
        (example_view().registry)(example_a())[false].component.root!=(example_view().registry)(example_b())[false].component.root,
        example_accumulator(false)(example_a())!=example_accumulator(true)(example_a()),
        project(example_view(),example_a(),ISet::full()).dom().contains(false),
        c::component(|_:bool,a:int,b:int|a==b,|a:Example|project(example_view(),a,ISet::full()),
            c::unit(),|_:bool,_:Example|ISet::empty(),(example_view().registry)(example_a())[false].component),
{
    let view=example_view();let eq=|_:bool,a:int,b:int|a==b;
    example_projection(example_a());example_projection(example_b());
    let base=|a:Example,b:Example|observed(eq,view,a,b);
    assert forall|a:Example,b:Example| #[trigger] base(a,b)==(a.visible==b.visible) by {
        example_projection(a);example_projection(b);
        c::singleton_observation(eq,ISet::full(),false,a.visible,b.visible);
    }
    c::unit_related(base,false,true);
    assert(o::related_maps(base,example_accumulator(false),example_accumulator(true)));
    assert forall|n:bool| registered(view,example_a(),n) implies fields_related(base,view,n,
        (view.registry)(example_a())[n],(view.registry)(example_b())[n]) by {assert(n==false);}
    assert(base(example_a(),example_b()));
    let coeffects=|a:Example|project(view,a,ISet::full());
    let component=(view.registry)(example_a())[false].component;
    let narrow=|a:Example,b:Example|c::observed(eq,coeffects,component.dependencies.union(component.provisions),a,b);
    assert forall|a:Example| #[trigger] narrow(a,a) by {example_projection(a);}
    c::unit_witnessed(narrow,component.root);
}

} // verus!
