//! Actual two-actor Iter exchange for Unit/Operation nodes.
//!
//! Same-key operations use raw outcome and partial inverse stability in
//! addition to observational value commutation. Both histories are generated
//! by their own real calls; their fresh journal indices are transposed.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus, dependent_grammar as d, dependent_lift as dep, grammar_lift as lift, mediated as m,
    mixed_grammar as g, observational_grammar as og, observational_lift as ol,
    partial_independence as pi, preservation as inv, projection as p, refinement as r,
    semantics as s, shared_replay as replay, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// A local law only for this pair of operations. No disjoint-provider premise
/// is imposed: two clients may resolve the same key in a third actor's table.
pub open spec fn pair_independent<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,left:dep::Node<A,X,U,B,I>,right:dep::Node<A,X,U,B,J>)->bool {
    match (left,right) {
        (d::Node::Operation {operation:a,argument:x,..},d::Node::Operation {operation:b,argument:y,..})=>
            (lib.key)(a)!=(lib.key)(b) || pi::value_independent(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x),(lib.apply)(b,y)),
        _=>true,
    }
}
pub open spec fn operational<A,X,U,B,I>(node:g::Node<A,X,U,B,I>)->bool {
    match node {g::Node::Dependent {node}=>replay::operational(node),_=>false}
}
pub open spec fn node<A,X,U,B,I>(value:g::Node<A,X,U,B,I>)->dep::Node<A,X,U,B,I> {
    match value {g::Node::Dependent {node}=>node,_=>d::Node::Unit}
}
pub open spec fn inverse<U>(receipt:g::Receipt<U>)->m::PartialMap<IMap<Port,U>> {
    match receipt {g::Receipt::Table {receipt}=>lift::projected_inverse(receipt),_=>|_:IMap<Port,U>|None}
}

pub proof fn local_independence<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,left:dep::Node<A,X,U,B,I>,right:dep::Node<A,X,U,B,J>,
    lk:ISet<Port>,lp:ISet<Port>,rk:ISet<Port>,rp:ISet<Port>)
    requires og::primitive_theory(eq,lib),replay::operational(left),replay::operational(right),
        d::permitted(lib,lk,lp,left),d::permitted(lib,rk,rp,right),pair_independent(eq,lib,left,right),
    ensures pi::independent(eq,dep::stage(lib,left),dep::stage(lib,right)),
{
    replay::context_equivalence(eq,lib);replay::stage_respects(eq,lib,left,lk,lp);replay::stage_respects(eq,lib,right,rk,rp);
    match left {
        d::Node::Unit=>{pi::unit_independence::<Port,U,B,B>(eq,dep::stage(lib,right));},
        d::Node::Operation {operation:a,argument:x,select:an}=>{match right {
            d::Node::Unit=>{pi::unit_independence::<Port,U,B,B>(eq,dep::stage(lib,left));},
            d::Node::Operation {operation:b,argument:y,select:bn}=>{
                if (lib.key)(a)==(lib.key)(b) {
                    pi::shared_operations(eq,(lib.key)(a),(lib.apply)(a,x),(lib.apply)(b,y),|out:B|dep::marker(an(out)),|out:B|dep::marker(bn(out)));
                } else {pi::distinct_nodes(eq,dep::stage(lib,left),dep::stage(lib,right));}
            },_=>{},
        }},_=>{},
    }
}

/// Strict forward domains, raw outcomes, and both freshly yielded inverse
/// relations follow from the local independence witness and the original runs.
pub proof fn context_exchange<U,B>(eq:spec_fn(Port,U,U)->bool,left:m::Node<Port,U,B>,right:m::Node<Port,U,B>,input:IMap<Port,U>)
    requires calculus::equivalence(pi::context_eq(eq)),pi::independent(eq,left,right),m::run(left,input).is_some(),m::run(right,m::run(left,input).unwrap().state).is_some(),
    ensures {
        let first=m::run(left,input).unwrap();let second=m::run(right,first.state).unwrap();
        let reverse_first=m::run(right,input).unwrap();let reverse_last=m::run(left,reverse_first.state).unwrap();
        &&& m::run(right,input).is_some() && m::run(left,reverse_first.state).is_some()
        &&& pi::context_eq(eq)(second.state,reverse_last.state)
        &&& pi::outcome(left,input)==pi::outcome(left,reverse_first.state)
        &&& pi::outcome(right,first.state)==pi::outcome(right,input)
        &&& m::partial_related(pi::context_eq(eq),first.undo,reverse_last.undo)
        &&& m::partial_related(pi::context_eq(eq),reverse_first.undo,second.undo)
    },
{
    let lf=pi::forward(left);let rf=pi::forward(right);
    assert(pi::generators(left).contains(lf));assert(pi::generators(right).contains(rf));
    assert(pi::commutes(pi::context_eq(eq),lf,rf));
    assert(pi::optional_equal(pi::context_eq(eq),pi::compose(lf,rf)(input),pi::compose(rf,lf)(input)));
    assert(m::run(right,input).is_some());
    assert(pi::stable(eq,right,lf));assert(lf(input).is_some());
    assert(pi::stable(eq,left,rf));assert(rf(input).is_some());
}

pub open spec fn same_data<U>(a:s::State<U>,b:s::State<U>)->bool {a.control==b.control && a.tables==b.tables}
pub proof fn run_same_data<A,X,U,B,I>(lib:g::Library<A,X,U,B>,n:dep::Node<A,X,U,B,I>,a:s::State<U>,b:s::State<U>,actor:usize)
    requires same_data(a,b),
    ensures dep::run(lib,n,a,actor).is_some()==dep::run(lib,n,b,actor).is_some(),
        dep::run(lib,n,a,actor).is_some() ==> {
            let left=dep::run(lib,n,a,actor).unwrap();let right=dep::run(lib,n,b,actor).unwrap();
            &&& same_data(left.state,right.state) && left.receipt==right.receipt && left.next==right.next
        },
{
    match n {d::Node::Operation {operation,..}=>{assert(lift::resolve(a,actor,(lib.key)(operation))==lift::resolve(b,actor,(lib.key)(operation)));},_=>{}}
}
pub proof fn same_data_projection<U>(a:s::State<U>,b:s::State<U>)
    requires same_data(a,b),inv::well_formed(a),inv::well_formed(b),
    ensures p::project(a,ISet::full())==p::project(b,ISet::full()),
{
    p::unique_owner(a);p::unique_owner(b);
    assert(p::bindings_equal(a,b)) by {assert forall|key:Port,id:usize| p::owns(a,key,id)==p::owns(b,key,id)
        && (p::owns(a,key,id) ==> a.tables[id][key]==b.tables[id][key]) by {}}
    p::projection_equal(a,b,ISet::full());
}

pub proof fn operation_domains<A,X,U,B,I>(lib:g::Library<A,X,U,B>,n:dep::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),replay::operational(n),dep::run(lib,n,a,actor).is_some(),
    ensures {
        let z=dep::run(lib,n,a,actor).unwrap().state;
        &&& inv::well_formed(z) && z.control==a.control && z.effects==a.effects && z.iterators==a.iterators && z.accumulators==a.accumulators
        &&& forall|id:usize| s::registered(a,id) ==> z.tables[id].dom()==a.tables[id].dom()
    },
{
    lift::run_preservation(dep::stage(lib,n),a,actor);
    if let d::Node::Operation {operation,argument,..}=n {
        let key=(lib.key)(operation);let provider=lift::resolve(a,actor,key).unwrap();
        let value=(lib.apply)(operation,argument)(a.tables[provider][key]).unwrap().value;
        assert(a.tables[provider].insert(key,value).dom() =~= a.tables[provider].dom());
    }
}
pub proof fn publication<U>(a:s::State<U>,b:s::State<U>,actor:usize)
    requires a.control==b.control,forall|id:usize| s::registered(a,id) ==> a.tables[id].dom()==b.tables[id].dom(),
    ensures s::coherent(a,actor)==s::coherent(b,actor),
{
    assert forall|key:Port,id:usize| s::publishes(a,key,id)==s::publishes(b,key,id) by {}
}

/// Lift the context diamond through actual committed-provider resolution.
/// Controls stay fixed, so reversal never redirects a captured provider.
pub proof fn run_exchange<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,left:dep::Node<A,X,U,B,I>,right:dep::Node<A,X,U,B,I>,
    a:s::State<U>,actor:usize,other:usize)
    requires og::primitive_theory(eq,lib),inv::well_formed(a),s::registered(a,actor),s::registered(a,other),
        a.control.fibers[actor].phase!=Phase::Inactive,a.control.fibers[other].phase!=Phase::Inactive,
        replay::operational(left),replay::operational(right),pair_independent(eq,lib,left,right),
        d::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,left),
        d::permitted(lib,dep::declarations(a,other),a.control.fibers[other].provisions,right),
        dep::run(lib,left,a,actor).is_some(),dep::run(lib,right,dep::run(lib,left,a,actor).unwrap().state,other).is_some(),
    ensures {
        let first=dep::run(lib,left,a,actor).unwrap();let second=dep::run(lib,right,first.state,other).unwrap();
        let reverse_first=dep::run(lib,right,a,other).unwrap();let reverse_last=dep::run(lib,left,reverse_first.state,actor).unwrap();
        &&& dep::run(lib,right,a,other).is_some() && dep::run(lib,left,reverse_first.state,actor).is_some()
        &&& first.next==reverse_last.next && second.next==reverse_first.next
        &&& second.state.control==a.control && reverse_last.state.control==a.control
        &&& pi::context_eq(eq)(p::project(second.state,ISet::full()),p::project(reverse_last.state,ISet::full()))
        &&& pi::outcome(dep::stage(lib,left),p::project(a,ISet::full()))==pi::outcome(dep::stage(lib,left),p::project(reverse_first.state,ISet::full()))
        &&& pi::outcome(dep::stage(lib,right),p::project(first.state,ISet::full()))==pi::outcome(dep::stage(lib,right),p::project(a,ISet::full()))
        &&& m::partial_related(pi::context_eq(eq),lift::projected_inverse(first.receipt),lift::projected_inverse(reverse_last.receipt))
        &&& m::partial_related(pi::context_eq(eq),lift::projected_inverse(second.receipt),lift::projected_inverse(reverse_first.receipt))
    },
{
    local_independence(eq,lib,left,right,dep::declarations(a,actor),a.control.fibers[actor].provisions,dep::declarations(a,other),a.control.fibers[other].provisions);
    operation_domains(lib,left,a,actor);let first=dep::run(lib,left,a,actor).unwrap();
    operation_domains(lib,right,first.state,other);let second=dep::run(lib,right,first.state,other).unwrap();
    lift::run_projects(dep::stage(lib,left),a,actor);lift::run_projects(dep::stage(lib,right),first.state,other);
    replay::context_equivalence(eq,lib);
    context_exchange(eq,dep::stage(lib,left),dep::stage(lib,right),p::project(a,ISet::full()));
    let allowed=|_:Port,_:m::Operation<U,B>|true;
    lift::run_definedness(dep::stage(lib,right),allowed,a,other);
    operation_domains(lib,right,a,other);let reverse_first=dep::run(lib,right,a,other).unwrap();
    lift::run_projects(dep::stage(lib,right),a,other);
    lift::run_definedness(dep::stage(lib,left),allowed,reverse_first.state,actor);
    operation_domains(lib,left,reverse_first.state,actor);let reverse_last=dep::run(lib,left,reverse_first.state,actor).unwrap();
    lift::run_projects(dep::stage(lib,left),reverse_first.state,actor);
    replay::actual_next(lib,left,a,reverse_first.state,actor);replay::actual_next(lib,right,first.state,a,other);
    replay::actual_receipt_projects(lib,left,a,actor);replay::actual_receipt_projects(lib,right,first.state,other);
    replay::actual_receipt_projects(lib,right,a,other);replay::actual_receipt_projects(lib,left,reverse_first.state,actor);
    replay::context_equivalence(eq,lib);
    assert forall|x:IMap<Port,U>,y:IMap<Port,U>| #![trigger (lift::projected_inverse(second.receipt))(x),(lift::projected_inverse(reverse_first.receipt))(y)]
        pi::context_eq(eq)(x,y) implies {
            &&& (lift::projected_inverse(second.receipt))(x).is_some()==(lift::projected_inverse(reverse_first.receipt))(y).is_some()
            &&& ((lift::projected_inverse(second.receipt))(x).is_some() ==> pi::context_eq(eq)((lift::projected_inverse(second.receipt))(x).unwrap(),(lift::projected_inverse(reverse_first.receipt))(y).unwrap()))
        } by {
            let ctx=pi::context_eq(eq);assert(ctx(y,x));
            assert((lift::projected_inverse(reverse_first.receipt))(y).is_some()==(lift::projected_inverse(second.receipt))(x).is_some());
            if (lift::projected_inverse(second.receipt))(x).is_some() {assert(ctx((lift::projected_inverse(reverse_first.receipt))(y).unwrap(),(lift::projected_inverse(second.receipt))(x).unwrap()));}
        }
}


pub open spec fn receipt_names<U>(a:lift::Receipt<U>,b:lift::Receipt<U>)->bool {
    a.actor==b.actor && match (a.inverse,b.inverse) {
        (lift::Inverse::Unit,lift::Inverse::Unit)=>true,
        (lift::Inverse::Operation {provider:p,key:k,..},lift::Inverse::Operation {provider:q,key:j,..})=>p==q && k==j,
        (lift::Inverse::Provision {key:k},lift::Inverse::Provision {key:j})=>k==j,
        _=>false,
    }
}
pub open spec fn mixed_names<U>(a:g::Receipt<U>,b:g::Receipt<U>)->bool {
    match (a,b) {(g::Receipt::Table {receipt:x},g::Receipt::Table {receipt:y})=>receipt_names(x,y),_=>false}
}
pub proof fn stable_receipt_names<A,X,U,B,I>(lib:g::Library<A,X,U,B>,n:dep::Node<A,X,U,B,I>,a:s::State<U>,b:s::State<U>,actor:usize)
    requires a.control==b.control,dep::run(lib,n,a,actor).is_some(),dep::run(lib,n,b,actor).is_some(),
    ensures receipt_names(dep::run(lib,n,a,actor).unwrap().receipt,dep::run(lib,n,b,actor).unwrap().receipt),
{
    if let d::Node::Operation {operation,..}=n {assert(lift::resolve(a,actor,(lib.key)(operation))==lift::resolve(b,actor,(lib.key)(operation)));}
}

/// Iter does not publish or unpublish a table. Unit returns None and therefore
/// cannot satisfy the Iter next guard, though the run-level lemmas cover Unit.
pub proof fn iter_frame<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize)
    requires inv::well_formed(a.state),g::step(lib,programs,a,z,actor,r::Rule::Iter),operational(programs(actor)(a.current[actor].unwrap())),
    ensures {
        let n=node(programs(actor)(a.current[actor].unwrap()));let out=dep::run(lib,n,a.state,actor).unwrap();
        &&& dep::run(lib,n,a.state,actor).is_some() && out.next.is_some()
        &&& z.state.control==a.state.control && same_data(z.state,out.state)
        &&& z.roots==a.roots && z.current==a.current.insert(actor,out.next)
        &&& z.history==a.history.push(g::entry(lib,programs,a,actor))
        &&& z.state.accumulators==a.state.accumulators.insert(actor,a.state.accumulators[actor].push(a.history.len()))
        &&& forall|id:usize| s::registered(a.state,id) ==> z.state.tables[id].dom()==a.state.tables[id].dom()
    },
{
    let n=node(programs(actor)(a.current[actor].unwrap()));operation_domains(lib,n,a.state,actor);
    assert(z.state.control.fibers =~= a.state.control.fibers);
}

pub open spec fn first_reversed<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,other:usize)->g::Configuration<U,I> {
    g::land(lib,programs,a,other,Phase::Loading)
}
pub open spec fn last_reversed<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,actor:usize,other:usize)->g::Configuration<U,I> {
    g::land(lib,programs,first_reversed(lib,programs,a,other),actor,Phase::Loading)
}

/// A genuine two-actor lifecycle diamond, with actual entries in the reverse
/// order. The two new inverse maps need only be partially related; captured
/// provider names and arbitrary-I continuation selections agree exactly.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn diamond<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,other:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),actor!=other,
        g::step(lib,programs,a,b,actor,r::Rule::Iter),g::step(lib,programs,b,z,other,r::Rule::Iter),
        operational(programs(actor)(a.current[actor].unwrap())),operational(programs(other)(a.current[other].unwrap())),
        pair_independent(eq,lib,node(programs(actor)(a.current[actor].unwrap())),node(programs(other)(a.current[other].unwrap()))),
    ensures {
        let middle=first_reversed(lib,programs,a,other);let last=last_reversed(lib,programs,a,actor,other);let h=a.history.len();
        &&& g::step(lib,programs,a,middle,other,r::Rule::Iter) && g::step(lib,programs,middle,last,actor,r::Rule::Iter)
        &&& g::well_formed(lib,programs,middle) && g::well_formed(lib,programs,last)
        &&& z.state.control==last.state.control && z.roots==last.roots && z.current==last.current
        &&& pi::context_eq(eq)(p::project(z.state,ISet::full()),p::project(last.state,ISet::full()))
        &&& z.history.len()==h+2 && last.history.len()==h+2
        &&& forall|i:int| 0<=i<h ==> z.history[i]==a.history[i] && last.history[i]==a.history[i]
        &&& last.history[h as int]==g::entry(lib,programs,a,other)
        &&& last.history[h as int+1]==g::entry(lib,programs,middle,actor)
        &&& last.history[h as int].input==a.state && last.history[h as int+1].input==middle.state
        &&& g::owner(z.history[h as int].landed.receipt)==actor && g::owner(last.history[h as int+1].landed.receipt)==actor
        &&& g::owner(z.history[h as int+1].landed.receipt)==other && g::owner(last.history[h as int].landed.receipt)==other
        &&& mixed_names(z.history[h as int].landed.receipt,last.history[h as int+1].landed.receipt)
        &&& mixed_names(z.history[h as int+1].landed.receipt,last.history[h as int].landed.receipt)
        &&& pi::outcome(dep::stage(lib,node(programs(actor)(a.current[actor].unwrap()))),p::project(a.state,ISet::full()))
            ==pi::outcome(dep::stage(lib,node(programs(actor)(a.current[actor].unwrap()))),p::project(middle.state,ISet::full()))
        &&& pi::outcome(dep::stage(lib,node(programs(other)(a.current[other].unwrap()))),p::project(b.state,ISet::full()))
            ==pi::outcome(dep::stage(lib,node(programs(other)(a.current[other].unwrap()))),p::project(a.state,ISet::full()))
        &&& z.history[h as int].landed.next==last.history[h as int+1].landed.next
        &&& z.history[h as int+1].landed.next==last.history[h as int].landed.next
        &&& m::partial_related(pi::context_eq(eq),inverse(z.history[h as int].landed.receipt),inverse(last.history[h as int+1].landed.receipt))
        &&& m::partial_related(pi::context_eq(eq),inverse(z.history[h as int+1].landed.receipt),inverse(last.history[h as int].landed.receipt))
        &&& z.state.accumulators[actor]==a.state.accumulators[actor].push(h)
        &&& z.state.accumulators[other]==a.state.accumulators[other].push(h+1)
        &&& last.state.accumulators[actor]==a.state.accumulators[actor].push(h+1)
        &&& last.state.accumulators[other]==a.state.accumulators[other].push(h)
        &&& forall|id:usize| s::registered(a.state,id) && id!=actor && id!=other ==> last.state.accumulators[id]==a.state.accumulators[id]
    },
{
    iter_frame(lib,programs,a,b,actor);ol::configuration_preservation(eq,lib,programs,a,b,actor,r::Rule::Iter);
    assert(b.current[other]==a.current[other]);iter_frame(lib,programs,b,z,other);
    ol::configuration_preservation(eq,lib,programs,b,z,other,r::Rule::Iter);
    let left=node(programs(actor)(a.current[actor].unwrap()));let right=node(programs(other)(a.current[other].unwrap()));
    ol::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());
    ol::run_members(eq,lib,programs,b.state,other,b.current[other].unwrap());
    let first=dep::run(lib,left,a.state,actor).unwrap();
    run_same_data(lib,right,b.state,first.state,other);
    assert(dep::run(lib,right,first.state,other).is_some());
    run_exchange(eq,lib,left,right,a.state,actor,other);
    let second=dep::run(lib,right,first.state,other).unwrap();
    let reverse_first=dep::run(lib,right,a.state,other).unwrap();let reverse_last=dep::run(lib,left,reverse_first.state,actor).unwrap();
    publication(a.state,b.state,other);
    let middle=first_reversed(lib,programs,a,other);let last=last_reversed(lib,programs,a,actor,other);
    assert(g::step(lib,programs,a,middle,other,r::Rule::Iter));
    ol::configuration_preservation(eq,lib,programs,a,middle,other,r::Rule::Iter);iter_frame(lib,programs,a,middle,other);
    run_same_data(lib,left,reverse_first.state,middle.state,actor);publication(a.state,middle.state,actor);
    assert(middle.current[actor]==a.current[actor]);
    assert(g::step(lib,programs,middle,last,actor,r::Rule::Iter));
    ol::configuration_preservation(eq,lib,programs,middle,last,actor,r::Rule::Iter);iter_frame(lib,programs,middle,last,actor);
    operation_domains(lib,left,a.state,actor);operation_domains(lib,right,a.state,other);
    operation_domains(lib,right,first.state,other);operation_domains(lib,left,reverse_first.state,actor);
    same_data_projection(b.state,first.state);same_data_projection(middle.state,reverse_first.state);
    same_data_projection(z.state,second.state);same_data_projection(last.state,reverse_last.state);
    stable_receipt_names(lib,left,a.state,middle.state,actor);stable_receipt_names(lib,right,b.state,a.state,other);
    assert(z.current =~= last.current);
    let h=a.history.len();
    assert forall|i:int| 0<=i<h implies z.history[i]==a.history[i] && last.history[i]==a.history[i] by {assert(b.history[i]==a.history[i]);assert(middle.history[i]==a.history[i]);}
}

pub open spec fn shift(amount:int)->m::PartialMap<int> {|v:int|Some(v+amount)}
pub proof fn translation_generator(amount:int,f:m::PartialMap<int>)
    requires pi::value_generators(crate::recovery_examples::translation(amount)).contains(f),
    ensures f==shift(amount) || f==shift(-amount),
{
    let op=crate::recovery_examples::translation(amount);
    if f==pi::value_forward(op) {assert(f =~= shift(amount));}
    else {
        let before=choose|v:int| #[trigger] op(v).is_some() && op(v).unwrap().undo==f;
        assert(f =~= shift(-amount));
    }
}
/// Real translation operations satisfy all three parts, including raw outcome
/// stability and the relation between their actual returned subtraction maps.
pub proof fn translations_independent(a:int,b:int)
    ensures pi::value_independent(|x:int,y:int|x==y,crate::recovery_examples::translation(a),crate::recovery_examples::translation(b)),
{
    let left=crate::recovery_examples::translation(a);let right=crate::recovery_examples::translation(b);let eq=|x:int,y:int|x==y;
    assert forall|f:m::PartialMap<int>,g:m::PartialMap<int>| pi::value_generators(left).contains(f) && pi::value_generators(right).contains(g)
        implies #[trigger] pi::commutes(eq,f,g) by {
        translation_generator(a,f);translation_generator(b,g);
        assert forall|v:int| #[trigger] pi::optional_equal(eq,pi::compose(f,g)(v),pi::compose(g,f)(v)) by {}
    }
    assert forall|g:m::PartialMap<int>| pi::value_generators(right).contains(g) implies #[trigger] pi::value_stable(eq,left,g) by {
        translation_generator(b,g);
        assert forall|v:int| #[trigger] g(v).is_some() implies {
            let x=left(v);let y=left(g(v).unwrap());
            &&& x.is_some()==y.is_some()
            &&& (x.is_some() ==> x.unwrap().outcome==y.unwrap().outcome && m::partial_related(eq,x.unwrap().undo,y.unwrap().undo))
        } by {}
    }
    assert forall|f:m::PartialMap<int>| pi::value_generators(left).contains(f) implies #[trigger] pi::value_stable(eq,right,f) by {
        translation_generator(a,f);
        assert forall|v:int| #[trigger] f(v).is_some() implies {
            let x=right(v);let y=right(f(v).unwrap());
            &&& x.is_some()==y.is_some()
            &&& (x.is_some() ==> x.unwrap().outcome==y.unwrap().outcome && m::partial_related(eq,x.unwrap().undo,y.unwrap().undo))
        } by {}
    }
}

#[derive(PartialEq,Eq,Structural)]
pub enum ExampleStage {Provide,Work,Done}
pub open spec fn example_key()->Port {crate::recovery_examples::key(0)}
pub open spec fn example_keys()->ISet<Port> {ISet::empty().insert(example_key())}
pub open spec fn example_view()->ISet<Binding> {ISet::empty().insert(Binding {key:example_key().key,realm:example_key().realm,provider:0})}
pub open spec fn example_programs()->g::Programs<Port,int,int,(),ExampleStage> {
    |actor:usize| |stage:ExampleStage|match stage {
        ExampleStage::Provide=>g::Node::Dependent {node:d::Node::Provision {key:example_key(),value:10,next:None}},
        ExampleStage::Work=>g::Node::Dependent {node:d::Node::Operation {operation:example_key(),argument:if actor==1 {2}else{3},select:|_:()|Some(ExampleStage::Done)}},
        ExampleStage::Done=>g::Node::Dependent {node:d::Node::Unit},
    }
}
#[verifier::opaque]
pub open spec fn example_trace()->Seq<g::Configuration<int,ExampleStage>> {
    let lib=crate::recovery_examples::library();let programs=example_programs();
    let a0=g::empty::<int,ExampleStage>();
    let a1=crate::mixed_transposition::insert(a0,0,None,ISet::empty(),example_keys(),ExampleStage::Provide);
    let a2=g::edit(a1,0,Phase::Loading,ISet::empty(),Some(ExampleStage::Provide),Seq::empty());
    let a3=g::land(lib,programs,a2,0,Phase::Active);
    let a4=crate::mixed_transposition::insert(a3,1,None,example_keys(),ISet::empty(),ExampleStage::Work);
    let a5=crate::mixed_transposition::insert(a4,2,None,example_keys(),ISet::empty(),ExampleStage::Work);
    let a6=g::edit(a5,1,Phase::Loading,example_view(),Some(ExampleStage::Work),Seq::empty());
    let a7=g::edit(a6,2,Phase::Loading,example_view(),Some(ExampleStage::Work),Seq::empty());
    let a8=g::land(lib,programs,a7,1,Phase::Loading);let a9=g::land(lib,programs,a8,2,Phase::Loading);
    seq![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9]
}
pub open spec fn example_labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Finish),
        (1usize,r::Rule::Insert),(2usize,r::Rule::Insert),(1usize,r::Rule::Begin),(2usize,r::Rule::Begin),
        (1usize,r::Rule::Iter),(2usize,r::Rule::Iter)]
}

pub proof fn example_target(a:s::State<int>,actor:usize)
    requires s::registered(a,actor),!a.control.fibers[actor].retired,a.control.fibers[actor].dependencies==example_keys(),s::publishes(a,example_key(),0),
    ensures s::target(a,actor,example_view()),
{
    let binding=Binding {key:example_key().key,realm:example_key().realm,provider:0};
    assert forall|key:Port| a.control.fibers[actor].dependencies.contains(key) implies exists|b:Binding|
        example_view().contains(b) && b.key==key.key && b.realm==key.realm by {
        assert(key==example_key());assert(example_view().contains(binding));
    }
}

pub proof fn example_resolve(a:s::State<int>,actor:usize)
    requires s::registered(a,actor),a.control.fibers[actor].dependencies==example_keys(),a.control.fibers[actor].provisions.is_empty(),a.control.fibers[actor].committed==example_view(),
    ensures lift::resolve(a,actor,example_key())==Some(0usize),
{
    let binding=Binding {key:example_key().key,realm:example_key().realm,provider:0};
    assert(a.control.fibers[actor].committed.contains(binding));assert(lift::names_key(binding,example_key()));
    assert(exists|b:Binding| a.control.fibers[actor].committed.contains(b) && lift::names_key(b,example_key()));
    let picked=choose|b:Binding| a.control.fibers[actor].committed.contains(b) && lift::names_key(b,example_key());
    assert(picked==binding);
}

pub proof fn example_execution()
    ensures g::execution(crate::recovery_examples::library(),example_programs(),example_trace(),example_labels()),
        example_trace().first()==g::empty::<int,ExampleStage>(),example_trace().len()==10,
{
    let lib=crate::recovery_examples::library();let programs=example_programs();
    crate::mixed_syntax::constructor_member(lib,programs,0,example_keys(),example_keys(),ExampleStage::Provide);
    crate::mixed_syntax::constructor_member(lib,programs,1,example_keys(),ISet::empty(),ExampleStage::Done);
    crate::mixed_syntax::constructor_member(lib,programs,1,example_keys(),ISet::empty(),ExampleStage::Work);
    crate::mixed_syntax::constructor_member(lib,programs,2,example_keys(),ISet::empty(),ExampleStage::Done);
    crate::mixed_syntax::constructor_member(lib,programs,2,example_keys(),ISet::empty(),ExampleStage::Work);
    assert(ISet::<Port>::empty().union(example_keys()) =~= example_keys());
    assert(example_keys().union(ISet::empty()) =~= example_keys());
    reveal(example_trace);let a=example_trace();let labels=example_labels();
    assert(g::step(lib,programs,a[0],a[1],0,r::Rule::Insert));assert(g::step(lib,programs,a[1],a[2],0,r::Rule::Begin));
    assert(g::step(lib,programs,a[2],a[3],0,r::Rule::Finish));
    assert(g::step(lib,programs,a[3],a[4],1,r::Rule::Insert));assert(g::step(lib,programs,a[4],a[5],2,r::Rule::Insert));
    example_target(a[5].state,1);example_target(a[6].state,2);
    assert(g::step(lib,programs,a[5],a[6],1,r::Rule::Begin));assert(g::step(lib,programs,a[6],a[7],2,r::Rule::Begin));
    example_target(a[7].state,1);example_resolve(a[7].state,1);
    assert(g::step(lib,programs,a[7],a[8],1,r::Rule::Iter));
    example_target(a[8].state,2);example_resolve(a[8].state,2);
    assert(g::step(lib,programs,a[8],a[9],2,r::Rule::Iter));
    assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,a[i],a[i+1],labels[i].0,labels[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else {assert(i==8);}
    }
}

/// Two real clients share Active provider 0. Original values are 10 -> 12 ->
/// 15; the reverse schedule is 10 -> 13 -> 15 with freshly recorded entries.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn shared_provider()
    ensures {
        let lib=crate::recovery_examples::library();let programs=example_programs();let eq=crate::recovery_examples::equality();
        let a=example_trace()[7];let b=example_trace()[8];let z=example_trace()[9];
        let middle=first_reversed(lib,programs,a,2);let last=last_reversed(lib,programs,a,1,2);
        &&& g::step(lib,programs,a,b,1,r::Rule::Iter) && g::step(lib,programs,b,z,2,r::Rule::Iter)
        &&& g::step(lib,programs,a,middle,2,r::Rule::Iter) && g::step(lib,programs,middle,last,1,r::Rule::Iter)
        &&& g::well_formed(lib,programs,last)
        &&& a.state.tables[0usize][example_key()]==10 && b.state.tables[0usize][example_key()]==12 && z.state.tables[0usize][example_key()]==15
        &&& middle.state.tables[0usize][example_key()]==13 && last.state.tables[0usize][example_key()]==15
        &&& z.current==last.current && z.current[1usize]==Some(ExampleStage::Done) && z.current[2usize]==Some(ExampleStage::Done)
        &&& m::partial_related(pi::context_eq(eq),inverse(z.history[1].landed.receipt),inverse(last.history[2].landed.receipt))
        &&& m::partial_related(pi::context_eq(eq),inverse(z.history[2].landed.receipt),inverse(last.history[1].landed.receipt))
        &&& z.state.accumulators[1usize]==seq![1nat] && z.state.accumulators[2usize]==seq![2nat]
        &&& last.state.accumulators[1usize]==seq![2nat] && last.state.accumulators[2usize]==seq![1nat]
        &&& last.history[1].input==a.state && last.history[2].input==middle.state
    },
{
    example_execution();crate::recovery_examples::primitive_theory();translations_independent(2,3);
    let eq=crate::recovery_examples::equality();let lib=crate::recovery_examples::library();let programs=example_programs();
    og::exact_theory(eq,lib);ol::from_empty_safe(eq,lib,programs,example_trace(),example_labels());
    reveal(example_trace);let a=example_trace()[7];let b=example_trace()[8];let z=example_trace()[9];
    diamond(eq,lib,programs,a,b,z,1,2);
    let middle=first_reversed(lib,programs,a,2);let last=last_reversed(lib,programs,a,1,2);
    example_resolve(a.state,2);example_resolve(middle.state,1);
    assert(z.state.accumulators[1usize] =~= seq![1nat]);assert(z.state.accumulators[2usize] =~= seq![2nat]);
    assert(last.state.accumulators[1usize] =~= seq![2nat]);assert(last.state.accumulators[2usize] =~= seq![1nat]);
}

/// Commuting value updates alone do not retain an arbitrary continuation I.
/// This real dependent call selects its old integer input as the next index.
pub proof fn raw_outcome_changes_continuation()
    ensures {
        let op=|v:int|Some(m::ValueYield {value:v+1,undo:|w:int|Some(w-1),outcome:v});
        let lib=d::Library {values:|_:Port,_:int|true,arguments:|_:(),_:()|true,outcomes:|_:(),_:int|true,
            key:|_:()|example_key(),allowed:ISet::full(),apply:|_:(),_:()|op};
        let n=d::Node::Operation {operation:(),argument:(),select:|old:int|Some(old)};
        let start=Map::empty().insert(example_key(),0int);let first=d::run(lib,n,start).unwrap();let second=d::run(lib,n,first.state).unwrap();
        &&& pi::commutes(|a:int,b:int|a==b,pi::value_forward(op),pi::value_forward(op))
        &&& d::run(lib,n,start).is_some() && d::run(lib,n,first.state).is_some()
        &&& first.next==Some(0int) && second.next==Some(1int)
        &&& !pair_independent(|_:Port,a:int,b:int|a==b,lib,n,n)
    },
{
    let eq=|a:int,b:int|a==b;let op=|v:int|Some(m::ValueYield {value:v+1,undo:|w:int|Some(w-1),outcome:v});
    let f=pi::value_forward(op);
    assert forall|v:int| #[trigger] pi::optional_equal(eq,pi::compose(f,f)(v),pi::compose(f,f)(v)) by {}
    assert(pi::value_generators(op).contains(f));
    if pi::value_independent(eq,op,op) {
        assert(pi::value_stable(eq,op,f));assert(f(0).is_some());assert(op(0).unwrap().outcome==op(f(0).unwrap()).unwrap().outcome);assert(false);
    }
    assert(!pi::value_independent(eq,op,op));
    let lib=d::Library {values:|_:Port,_:int|true,arguments:|_:(),_:()|true,outcomes:|_:(),_:int|true,
        key:|_:()|example_key(),allowed:ISet::full(),apply:|_:(),_:()|op};
    let n=d::Node::Operation {operation:(),argument:(),select:|old:int|Some(old)};
    let start=Map::empty().insert(example_key(),0int);let first=d::run(lib,n,start).unwrap();let second=d::run(lib,n,first.state).unwrap();
    assert(d::run(lib,n,start).is_some());assert(d::run(lib,n,first.state).is_some());
    assert(first.next==Some(0int));assert(second.next==Some(1int));
    let keyed=|_:Port,a:int,b:int|a==b;
    assert((|a:int,b:int|keyed((lib.key)(()),a,b)) =~= eq);
    assert(!pair_independent(keyed,lib,n,n));
}

} // verus!
