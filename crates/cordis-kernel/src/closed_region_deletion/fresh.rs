//! Preserve actual Fresh choices, binders and continuations during deletion.
//! The source chooses each name; no global fixed-name Mixed encoding is used.
#[cfg(verus_keep_ghost)]
use super::execution::{config_edit, numbered};
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use crate::{fresh_grammar as fg, fresh_semantics as fs};
use vstd::prelude::*;
verus! {
pub proof fn orchestration<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>,region:Region,rho:spec_fn(nat)->nat)
    requires fs::step(lib,programs,a,z,actor,rule,choice),region.wf(),closed(z.state,region),numbered(a,region,rho),g::tokens_valid(a),
        rule==r::Rule::Insert || rule==r::Rule::Retire || rule==r::Rule::Remove,
    ensures region.keep(actor,rule) ==> fs::step(lib,programs,configuration(a,region,rho),configuration(z,region,rho),actor,rule,choice),
        !region.keep(actor,rule) ==> configuration(a,region,rho)==configuration(z,region,rho),
{
    // Registry transport is independent of the installed program. A Unit
    // witness discharges only Mixed's syntactic Insert obligation; the actual
    // Fresh component obligation is transported unchanged below.
    let units:g::Programs<A,X,U,B,I>=|_:usize| |_:I|g::Node::Dependent {node:d::Node::Unit};
    if rule==r::Rule::Insert {syntax::constructor_member(lib,units,actor,dep::declarations(z.state,actor),z.state.control.fibers[actor].provisions,z.roots[actor]);}
    assert(g::step(lib,units,a,z,actor,rule));
    execution::orchestration(lib,units,a,z,actor,rule,region,rho);
    if region.keep(actor,rule) && rule==r::Rule::Insert {
        let out=configuration(z,region,rho);
        assert(dep::declarations(z.state,actor)==dep::declarations(out.state,actor));
        assert(fs::component_member(lib,programs,out.state,actor,out.roots[actor]));
    }
}
pub proof fn landing<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,actor:usize,phase:Phase,choice:Option<usize>,region:Region,rho:spec_fn(nat)->nat)
    requires region.wf(),g::metadata(a),s::registered(a.state,actor),fs::run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,choice).is_some(),
        local(fs::entry(lib,programs,a,actor,choice).landed.receipt,region),numbered(a,region,rho),
    ensures region.episodes.contains(actor) ==> configuration(fs::land(lib,programs,a,actor,phase,choice),region,rho)==configuration(a,region,rho),
        !region.episodes.contains(actor) ==> configuration(fs::land(lib,programs,a,actor,phase,choice),region,rho)==fs::land(lib,programs,configuration(a,region,rho),actor,phase,choice),
{
    let node=fg::instantiate(programs(actor)(a.current[actor].unwrap()),choice).unwrap();
    let concrete:g::Programs<A,X,U,B,I>=|_:usize| |_:I|node;
    assert(fs::land(lib,programs,a,actor,phase,choice)==g::land(lib,concrete,a,actor,phase));
    execution::landing(lib,concrete,a,actor,phase,region,rho);
    if !region.episodes.contains(actor) {
        let target=configuration(a,region,rho);
        assert(target.current[actor]==a.current[actor]);
        assert(fs::land(lib,programs,target,actor,phase,choice)==g::land(lib,concrete,target,actor,phase));
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(15)]
pub proof fn step<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>,region:Region,rho:spec_fn(nat)->nat)
    requires fs::well_formed(lib,programs,a),fs::step(lib,programs,a,z,actor,rule,choice),closed(a.state,region),closed(z.state,region),
        local_history(z.history,region),numbered(a,region,rho),
    ensures region.keep(actor,rule) ==> fs::step(lib,programs,configuration(a,region,rho),configuration(z,region,rho),actor,rule,choice),
        !region.keep(actor,rule) ==> configuration(a,region,rho)==configuration(z,region,rho),
{
    hide(fs::history_sound);hide(fs::members);hide(fg::member);
    let left=configuration(a,region,rho);let right=configuration(z,region,rho);
    if g::landing(a,z,rule) {
        let phase=if rule==r::Rule::Iter {Phase::Loading} else if rule==r::Rule::Finish {Phase::Active} else {Phase::Unloading};
        assert(z==fs::land(lib,programs,a,actor,phase,choice));
        assert(local(fs::entry(lib,programs,a,actor,choice).landed.receipt,region));
        landing(lib,programs,a,actor,phase,choice,region,rho);
        if !region.episodes.contains(actor) {
            targets(a.state,region,rho,actor,a.state.control.fibers[actor].committed);
            run(lib,fg::instantiate(programs(actor)(a.current[actor].unwrap()),choice).unwrap(),a.state,actor,region,rho);
            assert(fs::step(lib,programs,left,right,actor,rule,choice));
        }
    } else {match rule {
        r::Rule::Insert | r::Rule::Retire | r::Rule::Remove=>{orchestration(lib,programs,a,z,actor,rule,choice,region,rho);},
        r::Rule::Begin | r::Rule::Divert | r::Rule::Leave=>{
            let f=z.state.control.fibers[actor];
            let next=if rule==r::Rule::Begin {Some(a.roots[actor])} else {None};
            let stack=if rule==r::Rule::Begin {Seq::empty()} else {a.state.accumulators[actor]};
            assert(z==g::edit(a,actor,f.phase,f.committed,next,stack));
            config_edit(a,region,rho,actor,f.phase,f.committed,next,stack);
            if !region.episodes.contains(actor) {targets(a.state,region,rho,actor,f.committed);assert(tokens(Seq::<nat>::empty(),rho) =~= Seq::<nat>::empty());}
        },
        r::Rule::Unload=>{
            let restored=g::restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();
            restore(a.history,a.state.accumulators[actor],a.state,actor,region,rho);
            fs::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
            edit(restored,region,rho,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
            if region.episodes.contains(actor) {assert(left.current =~= right.current);assert(left==right);}
            else {
                assert(tokens(Seq::<nat>::empty(),rho) =~= Seq::<nat>::empty());
                assert(!r::relied(left.state.control,actor)) by {
                    if r::relied(left.state.control,actor) {
                        let (n,b)=choose|n:usize,b:Binding|r::registered(left.state.control,n) && n!=actor && left.state.control.fibers[n].phase!=Phase::Inactive
                            && left.state.control.fibers[n].committed.contains(b) && b.provider==actor;
                        assert(!region.episodes.contains(n));assert(r::relied(a.state.control,actor));
                    }
                }
                assert(right.current =~= left.current.insert(actor,None));assert(right==g::unload(left,actor));
            }
        },
        _=>{},
    }}
}
}
