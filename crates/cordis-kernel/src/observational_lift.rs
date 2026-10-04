//! The existing mixed interpreter under observational primitive recovery.
//!
//! These proofs reuse every actual state, step, receipt and inverse from
//! `mixed_grammar`; only the primitive recovery hypothesis is weakened from
//! raw equality to keywise observation, preserving strict inverse domains.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, contexts as c, dependent_grammar as d, dependent_lift as dep,
    grammar_lift as lift, mixed_grammar::*, mixed_syntax as syntax, observation,
    observational_grammar as og, preservation as inv, projection as p, refinement as r,
    semantics as s, Phase, Port,
};
use vstd::prelude::*;

verus! {
pub proof fn dependent_run_admissible<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires og::primitive_theory(eq,lib),inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),
        d::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,node),dep::run(lib,node,a,actor).is_some(),
    ensures {
        let out=dep::run(lib,node,a,actor).unwrap();
        &&& out.receipt.actor==actor && s::registered(a,actor)
        &&& inv::well_formed(out.state) && inv::table_map(a,out.state,actor) && dep::typed(lib,out.state) && dep::finite_context(out.state)
        &&& out.state.control==a.control && out.state.effects==a.effects
        &&& out.state.iterators==a.iterators && out.state.accumulators==a.accumulators
        &&& dep::receipt_typed(lib,out.receipt) && lift::undo(out.receipt,out.state).is_some()
        &&& observation::context_equal(eq,ISet::full(),p::project(lift::undo(out.receipt,out.state).unwrap(),ISet::full()),p::project(a,ISet::full()))
    },
{
    dep::stage_projection(lib,node,a,actor);lift::run_preservation(dep::stage(lib,node),a,actor);
    match node {
        d::Node::Unit=>{},
        d::Node::Operation {operation:op,argument:x,select}=>{
            let k=(lib.key)(op);let provider=lift::resolve(a,actor,k).unwrap();let operation=(lib.apply)(op,x);
            let y=operation(a.tables[provider][k]).unwrap();
            assert(d::operation_typed(lib,op,x));assert(og::operation_admissible(|u:U,v:U|eq(k,u,v),operation));
            assert((y.undo)(y.value).is_some());
            lift::resolution_sound(a,actor,k);dep::update_typed(lib,a,provider,k,Some(y.value));dep::update_finite(a,provider,k,Some(y.value));

        },
        d::Node::Provision {key,value,next}=>{
            dep::update_typed(lib,a,actor,key,Some(value));dep::update_finite(a,actor,key,Some(value));p::provision_stage_lift::<U,B>(a,actor,key,value,dep::marker(next));
        },
    }
    let out=dep::run(lib,node,a,actor).unwrap();
    assert(lift::undo(out.receipt,out.state).is_some());
    dep::run_projects(lib,node,a,actor);
    dep::inverse_projects(lib,node,a,actor,out.state);
    og::stage_admissible(arbitrary::<I>(),eq,lib,node,dep::declarations(a,actor),a.control.fibers[actor].provisions,ISet::full());
    let local=d::run(lib,node,dep::context(a)).unwrap();
    assert(d::context_equal(eq,ISet::full(),(local.undo)(local.state).unwrap(),dep::context(a)));
    assert(c::embed(dep::context(a))==p::project(a,ISet::full()));
    let restored=lift::undo(out.receipt,out.state).unwrap();
    assert(c::embed(dep::context(restored))==p::project(restored,ISet::full()));

}
pub proof fn run_admissible<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires og::primitive_theory(eq,lib),inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),
        syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,node),run(lib,node,a,actor).is_some(),
    ensures {
        let out=run(lib,node,a,actor).unwrap();
        &&& owner(out.receipt)==actor && s::registered(a,actor)
        &&& inv::forward_map(a,out.state,actor) && inv::well_formed(out.state)
        &&& dep::typed(lib,out.state) && dep::finite_context(out.state) && receipt_typed(lib,out.receipt)
        &&& undo(out.receipt,out.state).is_some()
        &&& (out.spawn.is_none() ==> out.state.control==a.control && out.state.effects==a.effects
            && out.state.iterators==a.iterators && out.state.accumulators==a.accumulators)
        &&& (out.spawn.is_some() ==> {
            let child=out.spawn.unwrap().0;
            &&& captured_child(out.receipt)==Some(child) && child!=actor && !s::registered(a,child)
            &&& inv::child_map(a,out.state,actor,child) && out.state.effects[child]==0
        })
        &&& observation::context_equal(eq,ISet::full(),p::project(undo(out.receipt,out.state).unwrap(),ISet::full()),p::project(a,ISet::full()))
    },
{
    match node {
        Node::Dependent {node}=>{dependent_run_admissible(eq,lib,node,a,actor);},
        Node::Child {child,dependencies,provisions,..}=>{
            let z=create(a,actor,child,dependencies,provisions);
            assert(inv::child_map(a,z,actor,child));inv::child_preservation(a,z,actor,child);
            assert(dep::typed(lib,z)) by {assert forall|n:usize,k:Port| s::registered(z,n) && z.tables[n].dom().contains(k)
                implies #[trigger] (lib.values)(k,z.tables[n][k]) by {if n!=child {assert(s::registered(a,n));}}}
            p::unique_owner(a);p::empty_insertion(a,z,child,ISet::full());
            let table=dep::context(a);assert(c::embed(table)==p::project(z,ISet::full()));
            ch::concrete_child_retirement(z,child);
            let retired=undo(Receipt::Child {actor,child},z).unwrap();
            s::child_inverse_observation(a,z,retired,actor,child);
            inv::retire_preservation(z,retired,child);p::unique_owner(z);p::unique_owner(retired);
            assert(p::bindings_equal(z,retired)) by {assert forall|key:Port,n:usize| p::owns(z,key,n)==p::owns(retired,key,n)
                && (p::owns(z,key,n) ==> z.tables[n][key]==retired.tables[n][key]) by { }}
            p::projection_equal(z,retired,ISet::full());
            assert forall|k:Port,u:U| #[trigger] eq(k,u,u) by {assert(crate::mediated::key_equivalence(eq,k));let local=|x:U,y:U|eq(k,x,y);assert(crate::calculus::equivalence(local));assert(local(u,u));}
        },
    }
}

pub proof fn run_members<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:s::State<U>,actor:usize,id:I)
    requires og::primitive_theory(eq,lib),component_member(lib,programs,a,actor,id),run(lib,programs(actor)(id),a,actor).is_some(),
    ensures {
        let out=run(lib,programs(actor)(id),a,actor).unwrap();
        &&& syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,programs(actor)(id))
        &&& (out.next.is_some() ==> component_member(lib,programs,a,actor,out.next.unwrap()))
        &&& (out.spawn.is_some() ==> component_member(lib,programs,out.state,out.spawn.unwrap().0,out.spawn.unwrap().1))
    },
{
    syntax::member_unfolding(lib,programs,actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,id);
    match programs(actor)(id) {
        Node::Dependent {node}=>{
            match node {
                d::Node::Operation {operation:op,argument:x,select}=>{
                    let k=(lib.key)(op);let provider=lift::resolve(a,actor,k).unwrap();
                    let y=(lib.apply)(op,x)(a.tables[provider][k]).unwrap();
                    assert(d::operation_typed(lib,op,x));assert((lib.outcomes)(op,y.outcome));
                    if select(y.outcome).is_some() {
                        assert(syntax::local(syntax::members(lib,programs),actor,dep::declarations(a,actor),a.control.fibers[actor].provisions).contains(select(y.outcome).unwrap()));
                    }
                },_=>{},
            }
        },
        Node::Child {child,dependencies,provisions,root,next}=>{
            assert(syntax::members(lib,programs).contains((child,dependencies.union(provisions),provisions,root)));
            if next.is_some() {assert(syntax::members(lib,programs).contains((actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,next.unwrap())));}
        },
    }
}
/// Every mixed transition has an admissible nine-rule full-state step. Local
/// admissibility is derived from actual syntax and receipts, not postulated.
pub proof fn step_refines<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures s::step(local_model(lib,programs,a),a.state,z.state,actor,rule),
        inv::admissible_step(local_model(lib,programs,a),a.state,z.state,actor,rule),inv::well_formed(z.state),
{
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();run_members(eq,lib,programs,a.state,actor,id);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor);
    }
    match rule {
        r::Rule::Insert=>{inv::insert_preservation(a.state,z.state,actor);},
        r::Rule::Unload=>{restore_refines(lib,programs,a,a.state.accumulators[actor],a.state,actor);},
        _=>{},
    }
    let model=local_model(lib,programs,a);
    assert(s::step(model,a.state,z.state,actor,rule));
    assert(inv::admissible_step(model,a.state,z.state,actor,rule));
    inv::full_preservation(model,a.state,z.state,actor,rule);
}

pub proof fn frame<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures {
        &&& forall|n:usize| s::registered(a.state,n) && s::registered(z.state,n) ==> r::interface_same(a.state.control.fibers[n],z.state.control.fibers[n])
            && a.state.effects[n]==z.state.effects[n] && a.roots[n]==z.roots[n]
        &&& forall|n:usize| n!=actor && s::registered(a.state,n) ==> s::registered(z.state,n)
            && a.current[n]==z.current[n] && a.state.accumulators[n]==z.state.accumulators[n]
        &&& forall|n:usize| s::registered(z.state,n) && !s::registered(a.state,n) ==> {
            &&& z.current[n].is_none() && z.state.accumulators[n].len()==0
            &&& (n==actor && rule==r::Rule::Insert || landing(a,z,rule) && entry(lib,programs,a,actor).landed.spawn.is_some()
                && n==entry(lib,programs,a,actor).landed.spawn.unwrap().0)
        }
        &&& (landing(a,z,rule) ==> {
            let e=entry(lib,programs,a,actor);
            &&& s::registered(a.state,actor) && a.current[actor].is_some()
            &&& run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor).is_some()
            &&& owner(e.landed.receipt)==actor && z.history==a.history.push(e)
            &&& z.state.accumulators[actor]==a.state.accumulators[actor].push(a.history.len())
            &&& z.current[actor]==if rule==r::Rule::Iter {e.landed.next} else {None}
            &&& (e.landed.spawn.is_some() ==> {
                let child=e.landed.spawn.unwrap().0;
                &&& !s::registered(a.state,child) && s::registered(z.state,child) && child!=actor
                &&& z.roots[child]==e.landed.spawn.unwrap().1
                &&& r::interface_same(e.landed.state.control.fibers[child],z.state.control.fibers[child])
            })
        })
        &&& (!landing(a,z,rule) ==> z.history==a.history)
    },
{
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();run_members(eq,lib,programs,a.state,actor,id);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor);
        inv::forward_preservation(a.state,entry(lib,programs,a,actor).landed.state,actor);
    }
    if rule==r::Rule::Unload {restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|n:usize| s::registered(a.state,n) && s::registered(z.state,n) implies r::interface_same(a.state.control.fibers[n],z.state.control.fibers[n])
        && a.state.effects[n]==z.state.effects[n] && a.roots[n]==z.roots[n] by {
        match rule {r::Rule::Insert | r::Rule::Remove=>{assert(n!=actor);},_=>{},}
    }
    assert forall|n:usize| n!=actor && s::registered(a.state,n) implies s::registered(z.state,n)
        && a.current[n]==z.current[n] && a.state.accumulators[n]==z.state.accumulators[n] by { }
    assert forall|n:usize| s::registered(z.state,n) && !s::registered(a.state,n) implies {
        &&& z.current[n].is_none() && z.state.accumulators[n].len()==0
        &&& (n==actor && rule==r::Rule::Insert || landing(a,z,rule) && entry(lib,programs,a,actor).landed.spawn.is_some()
            && n==entry(lib,programs,a,actor).landed.spawn.unwrap().0)
    } by { }
}

pub proof fn state_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures inv::well_formed(z.state),dep::typed(lib,z.state),metadata(z),dep::finite_context(z.state),
{
    step_refines(eq,lib,programs,a,z,actor,rule);frame(eq,lib,programs,a,z,actor,rule);
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();run_members(eq,lib,programs,a.state,actor,id);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor);
    }
    if rule==r::Rule::Unload {restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|n:usize,k:Port| s::registered(z.state,n) && z.state.tables[n].dom().contains(k)
        implies #[trigger] (lib.values)(k,z.state.tables[n][k]) by {
        match rule {
            r::Rule::Insert | r::Rule::Remove=>{assert(n!=actor);assert(a.state.tables[n]==z.state.tables[n]);},
            r::Rule::Iter | r::Rule::Finish=>{assert(dep::typed(lib,entry(lib,programs,a,actor).landed.state));},
            r::Rule::Divert=>{if landing(a,z,rule) {assert(dep::typed(lib,entry(lib,programs,a,actor).landed.state));}},
            r::Rule::Unload=>{assert(dep::typed(lib,restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap()));},
            _=>{},
        }
    }
    p::unique_owner(a.state);
    match rule {
        r::Rule::Insert=>{p::empty_insertion(a.state,z.state,actor,ISet::full());},
        r::Rule::Remove=>{p::empty_erasure(a.state,actor,ISet::full());},
        r::Rule::Retire=>{
            p::unique_owner(z.state);
            assert(p::bindings_equal(a.state,z.state)) by {assert forall|key:Port,n:usize| p::owns(a.state,key,n)==p::owns(z.state,key,n)
                && (p::owns(a.state,key,n) ==> a.state.tables[n][key]==z.state.tables[n][key]) by { }}
            p::projection_equal(a.state,z.state,ISet::full());
        },
        r::Rule::Iter | r::Rule::Finish | r::Rule::Divert=>{
            if landing(a,z,rule) {
                let out=entry(lib,programs,a,actor).landed;p::unique_owner(out.state);
                p::lifecycle_edit(out.state,actor,z.state.control.fibers[actor].phase,a.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
                let table=dep::context(out.state);assert(c::embed(table)==p::project(z.state,ISet::full()));
            } else {p::lifecycle_edit(a.state,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor],ISet::full());}
        },
        r::Rule::Unload=>{
            let restored=restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();p::unique_owner(restored);
            p::lifecycle_edit(restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
            let table=dep::context(restored);assert(c::embed(table)==p::project(z.state,ISet::full()));
        },
        r::Rule::Begin | r::Rule::Leave=>{p::lifecycle_edit(a.state,actor,z.state.control.fibers[actor].phase,z.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());},
        _=>{},
    }
    if p::project(a.state,ISet::full())==p::project(z.state,ISet::full()) {
        let table=dep::context(a.state);assert(c::embed(table)==p::project(z.state,ISet::full()));
    }
    assert forall|n:usize| s::registered(z.state,n) implies z.state.effects[n]==0 && z.state.iterators[n]==#[trigger] dep::marker(z.current[n]) by {
        if s::registered(a.state,n) {assert(a.state.effects[n]==0);}
        else if landing(a,z,rule) {assert(entry(lib,programs,a,actor).landed.spawn==Some((n,z.roots[n])));}
    }
    assert(z.roots.dom() =~= z.state.control.fibers.dom());
    assert(z.current.dom() =~= z.roots.dom());
}

#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
pub proof fn configuration_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures well_formed(lib,programs,z),
{
    frame(eq,lib,programs,a,z,actor,rule);state_preservation(eq,lib,programs,a,z,actor,rule);
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();let e=entry(lib,programs,a,actor);
        run_members(eq,lib,programs,a.state,actor,id);run_admissible(eq,lib,programs(actor)(id),a.state,actor);
        assert(history_sound(lib,programs,z.history)) by {
            assert forall|i:int| #![trigger z.history[i]] 0<=i<z.history.len() implies {
                let h=z.history[i];let n=owner(h.landed.receipt);
                &&& run(lib,programs(n)(h.iterator),h.input,n)==Some(h.landed)
                &&& receipt_typed(lib,h.landed.receipt) && undo(h.landed.receipt,h.landed.state).is_some()
            } by {if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());assert(z.history[i]==e);}}
        }
    }
    assert(tokens_valid(z)) by {
        assert forall|n:usize,i:int| #![trigger z.state.accumulators[n][i]] s::registered(z.state,n) && 0<=i<z.state.accumulators[n].len() implies {
            let token=z.state.accumulators[n][i];
            &&& token<z.history.len() && owner(z.history[token as int].landed.receipt)==n
        } by {
            assert(s::registered(a.state,n));
            if n==actor && landing(a,z,rule) && i==a.state.accumulators[n].len() {
                assert(z.state.accumulators[n][i]==a.history.len());assert(z.history[a.history.len() as int]==entry(lib,programs,a,actor));
            } else {
                assert(i<a.state.accumulators[n].len());assert(z.state.accumulators[n][i]==a.state.accumulators[n][i]);
                let token=a.state.accumulators[n][i];assert(token<a.history.len());assert(z.history[token as int]==a.history[token as int]);
            }
        }
    }
    assert(members(lib,programs,z)) by {
        assert forall|n:usize| s::registered(z.state,n) implies component_member(lib,programs,z.state,n,z.roots[n])
            && (z.current[n].is_some() ==> component_member(lib,programs,z.state,n,z.current[n].unwrap())) by {
            if !s::registered(a.state,n) {
                if rule!=r::Rule::Insert {
                    let e=entry(lib,programs,a,actor);assert(e.landed.spawn==Some((n,z.roots[n])));
                    assert(component_member(lib,programs,e.landed.state,n,z.roots[n]));
                }
            } else {
                assert(a.roots[n]==z.roots[n]);assert(component_member(lib,programs,a.state,n,a.roots[n]));
                if z.current[n].is_some() {
                    if n!=actor {assert(a.current[n]==z.current[n]);}
                    else if rule==r::Rule::Begin {assert(z.current[n]==Some(a.roots[n]));}
                    else if rule==r::Rule::Iter {
                        let e=entry(lib,programs,a,actor);assert(z.current[n]==e.landed.next);
                        assert(component_member(lib,programs,a.state,n,e.landed.next.unwrap()));
                    } else {assert(a.current[n]==z.current[n]);}
                }
            }
        }
    }
    assert(ch::retained(kind(z.history),z.state)) by {
        assert forall|n:usize,token:nat,child:usize| s::registered(z.state,n) && z.state.accumulators[n].contains(token)
            && kind(z.history)(token)==Some(child) implies s::registered(z.state,child) by {
            let i=choose|i:int| 0<=i<z.state.accumulators[n].len() && z.state.accumulators[n][i]==token;
            assert(s::registered(a.state,n));
            if landing(a,z,rule) && token==a.history.len() {
                let e=entry(lib,programs,a,actor);assert(z.history[token as int]==e);
                assert(e.landed.spawn.is_some());assert(e.landed.spawn.unwrap().0==child);
            } else {
                assert(token<a.history.len());assert(z.history[token as int]==a.history[token as int]);
                assert(a.state.accumulators[n].contains(token));assert(kind(a.history)(token)==Some(child));
                assert(s::registered(a.state,child));
                if rule==r::Rule::Remove {assert(child!=actor);}
                assert(s::registered(z.state,child));
            }
        }
    }
}

pub proof fn execution_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,states:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),execution(lib,programs,states,labels),well_formed(lib,programs,states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> well_formed(lib,programs,states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let previous=states.drop_last();let prefix=labels.drop_last();
        assert(execution(lib,programs,previous,prefix)) by {
            assert forall|i:int| 0<=i<prefix.len() implies step(lib,programs,previous[i],previous[i+1],prefix[i].0,prefix[i].1) by { }
        }
        execution_preservation(eq,lib,programs,previous,prefix);
        configuration_preservation(eq,lib,programs,previous.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies well_formed(lib,programs,states[i]) by {
            if i<previous.len() {assert(states[i]==previous[i]);} else {assert(i==states.len()-1);}
        }
    }
}
pub proof fn from_empty_safe<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,states:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),execution(lib,programs,states,labels),states.first()==empty::<U,I>(),
    ensures forall|i:int| 0<=i<states.len() ==> well_formed(lib,programs,states[i]) && inv::resource_safe(states[i].state),
{
    empty_well_formed(lib,programs);execution_preservation(eq,lib,programs,states,labels);
    assert forall|i:int| 0<=i<states.len() implies well_formed(lib,programs,states[i]) && inv::resource_safe(states[i].state) by {
        assert(well_formed(lib,programs,states[i]));
        assert forall|key:Port,left:usize,right:usize| s::publishes(states[i].state,key,left) && s::publishes(states[i].state,key,right) implies left==right by {
            assert(states[i].state.control.fibers[left].provisions.contains(key));assert(states[i].state.control.fibers[right].provisions.contains(key));
        }
    }
}

pub proof fn execution_ordering<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,trace:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),execution(lib,programs,trace,labels),well_formed(lib,programs,trace.first()),
    ensures crate::indexed_ordering::trace(states(trace),labels),
{
    execution_preservation(eq,lib,programs,trace,labels);
    assert forall|i:int| 0<=i<labels.len() implies crate::indexed_ordering::step(states(trace)[i],states(trace)[i+1],labels[i].0,labels[i].1) by {
        step_refines(eq,lib,programs,trace[i],trace[i+1],labels[i].0,labels[i].1);
        assert(s::step(local_model(lib,programs,trace[i]),states(trace)[i],states(trace)[i+1],labels[i].0,labels[i].1)
            && inv::admissible_step(local_model(lib,programs,trace[i]),states(trace)[i],states(trace)[i+1],labels[i].0,labels[i].1));
    }
}

}
