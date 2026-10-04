//! Definedness boundaries of the strict guarded fresh-child interpretation.
//!
//! These are actual successful prefixes of one fixed natural program. A child
//! declaration can block another allocation without changing any service table.
//! This disproves strict domain respect for that primitive, not every possible
//! reading of the paper's total iterator witness. The deadlock below concerns
//! the six core lifecycle rules; the separate error-exit extension is absent.
#[cfg(verus_keep_ghost)]
use crate::{
    allocation_inputs as a, fresh_grammar as f, fresh_semantics as g, global,
    mixed_transposition as insert, observational_grammar as og, projection as p, refinement as r,
    semantics as s, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// Both inputs come from the already proved allocation execution. The choice
/// remains fresh on both sides; only the existing child's declaration blocks it.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn allocation_domain_gap(keys:ISet<Port>)
    ensures {
        let left=a::trace(false)[3];let right=a::trace(false)[4];
        &&& g::well_formed(a::library(),a::programs(),left)
        &&& g::well_formed(a::library(),a::programs(),right)
        &&& s::registered(left.state,0) && s::registered(right.state,0)
        &&& !s::registered(left.state,3) && !s::registered(right.state,3)
        &&& left.state.control.fibers[0usize].dependencies.is_empty()
        &&& left.state.control.fibers[0usize].provisions.is_empty()
        &&& right.state.control.fibers[0usize].dependencies.is_empty()
        &&& right.state.control.fibers[0usize].provisions.is_empty()
        &&& !s::registered(left.state,2) && s::registered(right.state,2)
        &&& right.state.control.fibers[2usize].phase==Phase::Inactive
        &&& right.state.control.fibers[2usize].provisions==a::keys(a::key_a())
        &&& right.state.tables[2usize].is_empty()
        &&& p::project(left.state,keys)==IMap::<Port,int>::empty()
        &&& p::project(right.state,keys)==p::project(left.state,keys)
        &&& f::run(a::library(),a::programs()(0)(a::Stage::SpawnA),left.state,0,Some(3)).is_some()
        &&& f::run(a::library(),a::programs()(0)(a::Stage::SpawnA),right.state,0,Some(3)).is_none()
    },
{
    hide(g::well_formed);a::actual_execution(false);reveal(a::trace);
    let left=a::trace(false)[3];let right=a::trace(false)[4];
    assert forall|key:Port,n:usize| !p::owns(left.state,key,n) && !p::owns(right.state,key,n) by { }
    assert(g::well_formed(a::library(),a::programs(),left));
    assert(g::well_formed(a::library(),a::programs(),right));
    assert(f::run(a::library(),a::programs()(0)(a::Stage::SpawnA),left.state,0,Some(3)).is_some());
    assert(s::registered(right.state,2));
    assert(right.state.control.fibers[2usize].provisions.contains(a::key_a()));
    assert(a::keys(a::key_a()).contains(a::key_a()));
    assert(f::run(a::library(),a::programs()(0)(a::Stage::SpawnA),right.state,0,Some(3)).is_none());
    assert(p::project(left.state,keys) =~= IMap::<Port,int>::empty());
    assert(p::project(right.state,keys) =~= IMap::<Port,int>::empty());
}

pub open spec fn eligible_input(input:g::Configuration<int,a::Stage>)->bool {
    g::well_formed(a::library(),a::programs(),input)
        && s::registered(input.state,0) && !s::registered(input.state,3)
        && input.state.control.fibers[0usize].dependencies.is_empty()
        && input.state.control.fibers[0usize].provisions.is_empty()
}
pub open spec fn defined(input:g::Configuration<int,a::Stage>)->bool {
    f::run(a::library(),a::programs()(0)(a::Stage::SpawnA),input.state,0,Some(3)).is_some()
}
/// A necessary condition for Maybe-valued observational respect. Restricting
/// the inputs to authentic well-formed configurations only weakens the demand.
pub open spec fn strict_domain_respect(keys:ISet<Port>)->bool {
    forall|left:g::Configuration<int,a::Stage>,right:g::Configuration<int,a::Stage>|
        eligible_input(left) && eligible_input(right)
            && p::project(left.state,keys)==p::project(right.state,keys)
            ==> #[trigger] defined(left)==#[trigger] defined(right)
}

/// The failure occurs even for the finest all-table observation, and therefore
/// also at the parent's empty interface. Grammar membership does not repair it.
pub proof fn domain_respect_failure(keys:ISet<Port>)
    ensures !strict_domain_respect(keys),
        f::member(a::library(),a::programs(),0,ISet::empty(),ISet::empty(),a::Stage::SpawnA),
        f::natural(f::name_free::<a::Stage>(),a::programs()),
{
    allocation_domain_gap(keys);a::component_member(0,a::Stage::SpawnA);a::natural_program();
    let left=a::trace(false)[3];let right=a::trace(false)[4];
    assert(eligible_input(left) && eligible_input(right));
    if strict_domain_respect(keys) {assert(defined(left)==defined(right));}
}

/// Both roots contain the same SpawnA binder of allocation_inputs::programs.
/// Beginning root 1 first keeps its exact pending iterator across child 2's
/// successful birth and publication by root 0.
#[verifier::opaque]
pub open spec fn blocked_trace()->Seq<g::Configuration<int,a::Stage>> {
    let c0=g::empty::<int,a::Stage>();
    let c1=insert::insert(c0,0,None,ISet::empty(),ISet::empty(),a::Stage::SpawnA);
    let c2=insert::insert(c1,1,None,ISet::empty(),ISet::empty(),a::Stage::SpawnA);
    let c3=g::edit(c2,1,Phase::Loading,ISet::empty(),Some(a::Stage::SpawnA),Seq::empty());
    let c4=g::edit(c3,0,Phase::Loading,ISet::empty(),Some(a::Stage::SpawnA),Seq::empty());
    let c5=g::land(a::library(),a::programs(),c4,0,Phase::Active,Some(2));
    let c6=g::edit(c5,2,Phase::Loading,ISet::empty(),Some(a::Stage::ProvideA),Seq::empty());
    let c7=g::land(a::library(),a::programs(),c6,2,Phase::Active,None);
    seq![c0,c1,c2,c3,c4,c5,c6,c7]
}
pub open spec fn blocked_labels()->Seq<g::Label> {
    seq![(0usize,r::Rule::Insert,None),(1usize,r::Rule::Insert,None),
        (1usize,r::Rule::Begin,None),(0usize,r::Rule::Begin,None),
        (0usize,r::Rule::Finish,Some(2usize)),(2usize,r::Rule::Begin,None),(2usize,r::Rule::Finish,None)]
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn blocked_execution()
    ensures g::execution(a::library(),a::programs(),blocked_trace(),blocked_labels()),
        blocked_trace().first()==g::empty::<int,a::Stage>(),blocked_trace().len()==8,
        forall|i:int| 0<=i<blocked_trace().len() ==> g::well_formed(a::library(),a::programs(),blocked_trace()[i]),
        g::execution(a::library(),a::programs(),blocked_trace().subrange(2,8),blocked_labels().subrange(2,7)),
        forall|i:int| 2<=i<blocked_labels().len() ==> global::lifecycle_rule(blocked_labels()[i].1),
{
    let lib=a::library();let code=a::programs();let eq=crate::recovery_examples::equality();
    crate::recovery_examples::primitive_theory();og::exact_theory(eq,lib);
    a::component_member(0,a::Stage::SpawnA);a::component_member(1,a::Stage::SpawnA);g::empty_well_formed(lib,code);
    reveal(blocked_trace);let t=blocked_trace();let labels=blocked_labels();
    assert(g::step(lib,code,t[0],t[1],0,r::Rule::Insert,None));g::configuration_preservation(eq,lib,code,t[0],t[1],0,r::Rule::Insert,None);
    assert(g::step(lib,code,t[1],t[2],1,r::Rule::Insert,None));g::configuration_preservation(eq,lib,code,t[1],t[2],1,r::Rule::Insert,None);
    assert(g::step(lib,code,t[2],t[3],1,r::Rule::Begin,None));g::configuration_preservation(eq,lib,code,t[2],t[3],1,r::Rule::Begin,None);
    assert(g::step(lib,code,t[3],t[4],0,r::Rule::Begin,None));g::configuration_preservation(eq,lib,code,t[3],t[4],0,r::Rule::Begin,None);
    assert(g::step(lib,code,t[4],t[5],0,r::Rule::Finish,Some(2)));g::configuration_preservation(eq,lib,code,t[4],t[5],0,r::Rule::Finish,Some(2));
    assert(g::step(lib,code,t[5],t[6],2,r::Rule::Begin,None));g::configuration_preservation(eq,lib,code,t[5],t[6],2,r::Rule::Begin,None);
    assert(g::step(lib,code,t[6],t[7],2,r::Rule::Finish,None));g::configuration_preservation(eq,lib,code,t[6],t[7],2,r::Rule::Finish,None);
    assert forall|i:int| 0<=i<labels.len() implies g::step(lib,code,t[i],t[i+1],labels[i].0,labels[i].1,labels[i].2) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else {assert(i==6);}
    }
    assert forall|i:int| 0<=i<t.len() implies g::well_formed(lib,code,t[i]) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else {assert(i==7);}
    }
    assert forall|i:int| 0<=i<5 implies g::step(lib,code,t.subrange(2,8)[i],t.subrange(2,8)[i+1],
        labels.subrange(2,7)[i].0,labels.subrange(2,7)[i].1,labels.subrange(2,7)[i].2) by {assert(0<=i+2<labels.len());}
}

pub proof fn blocked_catalogue()
    ensures a::bounded_catalogue(blocked_trace(),blocked_labels()),
        forall|i:int| 0<=i<blocked_trace().len() ==> blocked_trace()[i].state.control.fibers.dom()
            .subset_of(ISet::empty().insert(0usize).insert(1usize).insert(2usize)),
{
    reveal(blocked_trace);let t=blocked_trace();let labels=blocked_labels();
    assert forall|i:int,id:usize| 0<=i<t.len() && s::registered(t[i].state,id) implies
        t[i].state.control.fibers[id].dependencies.is_empty()
            && t[i].state.control.fibers[id].provisions==a::provisions(t[i].roots[id]) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else {assert(i==7);}
    }
    assert forall|i:int| 0<=i<t.len() implies t[i].state.control.fibers.dom()
        .subset_of(ISet::empty().insert(0usize).insert(1usize).insert(2usize))
        && global::support_ranking(t[i].state.control,seq![0nat,0nat,1nat,1nat]) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else {assert(i==7);}
    }
    assert forall|i:int| 0<=i<labels.len() && g::landing(t[i],t[i+1],labels[i].1) implies {
        let out=f::run(a::library(),a::programs()(labels[i].0)(t[i].current[labels[i].0].unwrap()),t[i].state,labels[i].0,labels[i].2);
        &&& out.is_some() && out.unwrap().next.is_none()
    } by {if i==4 {} else {assert(i==6);}}
}

/// Restricting the domain to coherent Loading actors is insufficient: root 1
/// holds exactly the same iterator and committed view on both actual prefixes.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn pending_domain_gap(keys:ISet<Port>)
    ensures {
        let left=blocked_trace()[3];let right=blocked_trace()[5];
        &&& g::well_formed(a::library(),a::programs(),left) && g::well_formed(a::library(),a::programs(),right)
        &&& s::coherent(left.state,1) && s::coherent(right.state,1)
        &&& left.state.control.fibers[1usize].phase==Phase::Loading && right.state.control.fibers[1usize].phase==Phase::Loading
        &&& left.current[1usize]==Some(a::Stage::SpawnA) && right.current[1usize]==left.current[1usize]
        &&& left.state.control.fibers[1usize].committed==right.state.control.fibers[1usize].committed
        &&& !s::registered(left.state,3) && !s::registered(right.state,3)
        &&& right.state.control.fibers[2usize].phase==Phase::Inactive && right.state.tables[2usize].is_empty()
        &&& p::project(left.state,keys)==p::project(right.state,keys)
        &&& f::run(a::library(),a::programs()(1)(a::Stage::SpawnA),left.state,1,Some(3)).is_some()
        &&& f::run(a::library(),a::programs()(1)(a::Stage::SpawnA),right.state,1,Some(3)).is_none()
    },
{
    hide(g::well_formed);blocked_execution();reveal(blocked_trace);
    let left=blocked_trace()[3];let right=blocked_trace()[5];
    assert(g::well_formed(a::library(),a::programs(),left));assert(g::well_formed(a::library(),a::programs(),right));
    assert forall|key:Port,n:usize| !p::owns(left.state,key,n) && !p::owns(right.state,key,n) by { }
    assert(p::project(left.state,keys) =~= IMap::<Port,int>::empty());
    assert(p::project(right.state,keys) =~= IMap::<Port,int>::empty());
    assert(s::registered(right.state,2));assert(right.state.control.fibers[2usize].provisions.contains(a::key_a()));
    assert(a::keys(a::key_a()).contains(a::key_a()));
}

pub proof fn blocked_terminal()
    ensures !s::quiet(blocked_trace().last().state),s::total_active(blocked_trace().last().state),
        blocked_trace().last().state.control.fibers.dom()==ISet::empty().insert(0usize).insert(1usize).insert(2usize),
        blocked_trace().last().state.control.fibers[0usize].phase==Phase::Active,
        blocked_trace().last().state.control.fibers[1usize].phase==Phase::Loading,
        blocked_trace().last().state.control.fibers[2usize].phase==Phase::Active,
        blocked_trace().last().current[1usize]==Some(a::Stage::SpawnA),
        forall|id:usize| s::registered(blocked_trace().last().state,id) ==> s::coherent(blocked_trace().last().state,id),
        forall|choice:Option<usize>| #[trigger] f::run(a::library(),a::programs()(1)(a::Stage::SpawnA),blocked_trace().last().state,1,choice).is_none(),
{
    reveal(blocked_trace);let z=blocked_trace().last();
    assert(z.state.control.fibers.dom() =~= ISet::empty().insert(0usize).insert(1usize).insert(2usize));
    assert forall|id:usize| s::registered(z.state,id) implies s::coherent(z.state,id) by {
        if id==0 {} else if id==1 {} else {assert(id==2);}
    }
    assert(!s::quiet(z.state)) by {assert(s::registered(z.state,1));}
    assert(s::total_active(z.state)) by {
        assert forall|id:usize| s::registered(z.state,id) && z.state.control.fibers[id].phase==Phase::Active implies
            z.state.tables[id].dom()==z.state.control.fibers[id].provisions by {
            if id==0 {assert(z.state.tables[id].dom() =~= ISet::<Port>::empty());}
            else {assert(id==2);assert(z.state.tables[id].dom() =~= a::keys(a::key_a()));}
        }
    }
    assert forall|choice:Option<usize>| #[trigger] f::run(a::library(),a::programs()(1)(a::Stage::SpawnA),z.state,1,choice).is_none() by {
        match choice {None=>{},Some(child)=>{
            if child==0 {} else if child==1 {} else if child==2 {} else {
                assert(z.state.control.fibers[2usize].provisions.contains(a::key_a()));
            }
        }}
    }
}

pub proof fn no_lifecycle_step(next:g::Configuration<int,a::Stage>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires global::lifecycle_rule(rule),
    ensures !g::step(a::library(),a::programs(),blocked_trace().last(),next,actor,rule,choice),
{
    blocked_terminal();let z=blocked_trace().last();
    if s::registered(z.state,actor) {
        if actor==0 {} else if actor==2 {} else {
            assert(actor==1);
            assert(f::run(a::library(),a::programs()(actor)(z.current[actor].unwrap()),z.state,actor,choice).is_none());
        }
    }
    match rule {r::Rule::Begin=>{},r::Rule::Iter=>{},r::Rule::Finish=>{},r::Rule::Divert=>{},r::Rule::Leave=>{},r::Rule::Unload=>{},_=>{}}
}

/// A finite successful core lifecycle suffix can be maximal without being
/// quiet in this strict partial interpretation. This is not a claim about the
/// separate Failure extension or about an assumed total iterator semantics.
#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn strict_progress_boundary()
    ensures g::execution(a::library(),a::programs(),blocked_trace(),blocked_labels()),
        blocked_trace().first()==g::empty::<int,a::Stage>(),
        forall|i:int| 0<=i<blocked_trace().len() ==> g::well_formed(a::library(),a::programs(),blocked_trace()[i]),
        a::bounded_catalogue(blocked_trace(),blocked_labels()),
        g::execution(a::library(),a::programs(),blocked_trace().subrange(2,8),blocked_labels().subrange(2,7)),
        forall|i:int| 2<=i<blocked_labels().len() ==> global::lifecycle_rule(blocked_labels()[i].1),
        !s::quiet(blocked_trace().last().state),s::total_active(blocked_trace().last().state),
        forall|next:g::Configuration<int,a::Stage>,actor:usize,rule:r::Rule,choice:Option<usize>|
            global::lifecycle_rule(rule) ==> !g::step(a::library(),a::programs(),blocked_trace().last(),next,actor,rule,choice),
{
    hide(g::execution);hide(g::well_formed);hide(a::bounded_catalogue);hide(g::step);
    blocked_execution();blocked_catalogue();blocked_terminal();
    assert forall|next:g::Configuration<int,a::Stage>,actor:usize,rule:r::Rule,choice:Option<usize>|
        global::lifecycle_rule(rule) implies !g::step(a::library(),a::programs(),blocked_trace().last(),next,actor,rule,choice) by {
        no_lifecycle_step(next,actor,rule,choice);
    }
}

} // verus!
