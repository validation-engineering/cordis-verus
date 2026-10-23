//! Compose concrete primitive transport into a legal retained execution.
#[cfg(verus_keep_ghost)]
use super::*;
use vstd::prelude::*;
verus! {
pub open spec fn numbered<U,I>(a:g::Configuration<U,I>,region:Region,rho:spec_fn(nat)->nat)->bool {
    forall|t:nat|t<=a.history.len() ==> rho(t)==index(a.history,region,t)
}
pub proof fn config_edit<U,I>(a:g::Configuration<U,I>,region:Region,rho:spec_fn(nat)->nat,actor:usize,phase:Phase,view:ISet<Binding>,next:Option<I>,stack:Seq<nat>)
    requires region.wf(),s::registered(a.state,actor),a.current.dom().contains(actor),
    ensures region.episodes.contains(actor) ==> configuration(g::edit(a,actor,phase,view,next,stack),region,rho)==configuration(a,region,rho),
        !region.episodes.contains(actor) ==> configuration(g::edit(a,actor,phase,view,next,stack),region,rho)==g::edit(configuration(a,region,rho),actor,phase,view,next,tokens(stack,rho)),
{
    edit(a.state,region,rho,actor,phase,view,dep::marker(next),stack);
    let left=configuration(g::edit(a,actor,phase,view,next,stack),region,rho);
    let right=if region.episodes.contains(actor) {configuration(a,region,rho)} else {g::edit(configuration(a,region,rho),actor,phase,view,next,tokens(stack,rho))};
    assert(left.current =~= right.current);
}
pub proof fn insertion<U>(a:s::State<U>,z:s::State<U>,region:Region,rho:spec_fn(nat)->nat,actor:usize)
    requires region.wf(),inv::insert_map(a,z,actor),closed(z,region),
    ensures region.born.contains(actor) ==> state(a,region,rho)==state(z,region,rho),
        !region.born.contains(actor) ==> inv::insert_map(state(a,region,rho),state(z,region,rho),actor),
{
    let left=state(a,region,rho);let right=state(z,region,rho);
    if region.born.contains(actor) {
        assert(left.control.fibers =~= right.control.fibers);assert(left.tables =~= right.tables);
        assert(left.effects =~= right.effects);assert(left.iterators =~= right.iterators);assert(left.accumulators =~= right.accumulators);
    } else {
        assert(r::frame(left.control,right.control,actor)) by {
            assert forall|n:usize|n!=actor implies r::registered(left.control,n)==r::registered(right.control,n)
                && (r::registered(left.control,n) ==> left.control.fibers[n]==right.control.fibers[n]) by {
                assert(r::registered(a.control,n)==r::registered(z.control,n));
            }
        }
        assert(s::registered(z,actor));
        assert(!region.born.contains(actor));
        if z.control.fibers[actor].parent.is_some() {let parent=z.control.fibers[actor].parent.unwrap();assert(!region.born.contains(parent));}
        assert(r::step(left.control,right.control,actor,r::Rule::Insert));
        assert(right.tables =~= left.tables.insert(actor,IMap::empty()));
        assert(right.effects =~= left.effects.insert(actor,right.effects[actor]));
        assert(right.iterators =~= left.iterators.insert(actor,None));
        assert(tokens(Seq::<nat>::empty(),rho) =~= Seq::<nat>::empty());
        assert(right.accumulators =~= left.accumulators.insert(actor,Seq::empty()));
    }
}
pub proof fn retirement<U>(a:s::State<U>,z:s::State<U>,region:Region,rho:spec_fn(nat)->nat,actor:usize)
    requires region.wf(),s::child_retire(a,z,actor),
    ensures region.born.contains(actor) ==> state(a,region,rho)==state(z,region,rho),
        !region.born.contains(actor) ==> s::child_retire(state(a,region,rho),state(z,region,rho),actor),
{
    let left=state(a,region,rho);let right=state(z,region,rho);
    if region.born.contains(actor) {assert(left.control.fibers =~= right.control.fibers);}
    else {assert(r::frame(left.control,right.control,actor));assert(r::step(left.control,right.control,actor,r::Rule::Retire));}
    assert(left.tables =~= right.tables);assert(left.iterators =~= right.iterators);assert(left.accumulators =~= right.accumulators);
}
pub proof fn erasure<U>(a:s::State<U>,region:Region,rho:spec_fn(nat)->nat,actor:usize)
    ensures region.born.contains(actor) ==> state(s::erase(a,actor),region,rho)==state(a,region,rho),
        !region.born.contains(actor) ==> state(s::erase(a,actor),region,rho)==s::erase(state(a,region,rho),actor),
{
    let left=state(s::erase(a,actor),region,rho);
    let right=if region.born.contains(actor) {state(a,region,rho)} else {s::erase(state(a,region,rho),actor)};
    assert(left.control.fibers =~= right.control.fibers);assert(left.tables =~= right.tables);
    assert(left.effects =~= right.effects);assert(left.iterators =~= right.iterators);assert(left.accumulators =~= right.accumulators);
}
pub proof fn unreferenced<U,I>(a:g::Configuration<U,I>,region:Region,rho:spec_fn(nat)->nat,child:usize)
    requires region.wf(),numbered(a,region,rho),g::tokens_valid(a),ch::remove_unreferenced(g::kind(a.history),a.state,child),
    ensures ch::remove_unreferenced(g::kind(history(a.history,region,rho)),state(a.state,region,rho),child),
{
    history_indices(a.history,region,rho);
    let target=state(a.state,region,rho);
    assert forall|owner:usize,t:nat|s::registered(target,owner) && target.accumulators[owner].contains(t)
        implies g::kind(history(a.history,region,rho))(t)!=Some(child) by {
        assert(!region.episodes.contains(owner));
        let i=choose|i:int|0<=i<target.accumulators[owner].len() && target.accumulators[owner][i]==t;
        let old=a.state.accumulators[owner][i];assert(old<a.history.len());
        assert(g::owner(a.history[old as int].landed.receipt)==owner);
        assert(t==rho(old));assert(history(a.history,region,rho)[t as int].landed.receipt==a.history[old as int].landed.receipt);
        assert(a.state.accumulators[owner].contains(old));assert(g::kind(a.history)(old)!=Some(child));
    }
}
#[verifier::spinoff_prover]
pub proof fn orchestration<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,region:Region,rho:spec_fn(nat)->nat)
    requires g::step(lib,programs,a,z,actor,rule),region.wf(),closed(z.state,region),numbered(a,region,rho),g::tokens_valid(a),
        rule==r::Rule::Insert || rule==r::Rule::Retire || rule==r::Rule::Remove,
    ensures region.keep(actor,rule) ==> g::step(lib,programs,configuration(a,region,rho),configuration(z,region,rho),actor,rule),
        !region.keep(actor,rule) ==> configuration(a,region,rho)==configuration(z,region,rho),
{
    let left=configuration(a,region,rho);let right=configuration(z,region,rho);
    match rule {
        r::Rule::Insert=>{
            insertion(a.state,z.state,region,rho,actor);
            if region.born.contains(actor) {assert(left.roots =~= right.roots);assert(left.current =~= right.current);}
            else {
                assert(right.roots =~= left.roots.insert(actor,right.roots[actor]));assert(right.current =~= left.current.insert(actor,None));
                assert(dep::declarations(z.state,actor)==dep::declarations(right.state,actor));
                assert(g::component_member(lib,programs,right.state,actor,right.roots[actor]));
            }
        },
        r::Rule::Retire=>{retirement(a.state,z.state,region,rho,actor);},
        r::Rule::Remove=>{
            erasure(a.state,region,rho,actor);
            if region.born.contains(actor) {assert(left.roots =~= right.roots);assert(left.current =~= right.current);}
            else {
                unreferenced(a,region,rho,actor);
                assert(r::frame(left.state.control,right.state.control,actor));
                assert forall|n:usize|s::registered(left.state,n) implies left.state.control.fibers[n].parent!=Some(actor) by {assert(s::registered(a.state,n));}
                assert(r::step(left.state.control,right.state.control,actor,r::Rule::Remove));
                assert(right.roots =~= left.roots.remove(actor));assert(right.current =~= left.current.remove(actor));
            }
        },
        _=>{},
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn landing<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,actor:usize,phase:Phase,region:Region,rho:spec_fn(nat)->nat)
    requires region.wf(),g::metadata(a),s::registered(a.state,actor),g::run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor).is_some(),
        local(g::entry(lib,programs,a,actor).landed.receipt,region),numbered(a,region,rho),
    ensures region.episodes.contains(actor) ==> configuration(g::land(lib,programs,a,actor,phase),region,rho)==configuration(a,region,rho),
        !region.episodes.contains(actor) ==> configuration(g::land(lib,programs,a,actor,phase),region,rho)==g::land(lib,programs,configuration(a,region,rho),actor,phase),
{
    let node=programs(actor)(a.current[actor].unwrap());let old=g::entry(lib,programs,a,actor);let landed=old.landed;
    let next=if phase==Phase::Loading {landed.next} else {None};
    run(lib,node,a.state,actor,region,rho);
    history_push(a.history,old,region,rho);
    edit(landed.state,region,rho,actor,phase,a.state.control.fibers[actor].committed,dep::marker(next),a.state.accumulators[actor].push(a.history.len()));
    let left=configuration(g::land(lib,programs,a,actor,phase),region,rho);
    let start=configuration(a,region,rho);
    if region.episodes.contains(actor) {
        if landed.spawn.is_some() {assert(region.born.contains(landed.spawn.unwrap().0));}
        assert(left.roots =~= start.roots);assert(left.current =~= start.current);
        assert(left.history==start.history);
    } else {
        history_indices(a.history,region,rho);
        let right=g::land(lib,programs,start,actor,phase);
        assert(g::entry(lib,programs,start,actor)==entry(old,region,rho));
        assert(tokens(a.state.accumulators[actor].push(a.history.len()),rho) =~= tokens(a.state.accumulators[actor],rho).push(start.history.len()));
        assert(left.state==right.state);assert(left.roots =~= right.roots);assert(left.current =~= right.current);
        assert(left.history==right.history);
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(15)]
pub proof fn step<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,region:Region,rho:spec_fn(nat)->nat)
    requires g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),closed(a.state,region),closed(z.state,region),
        local_history(z.history,region),numbered(a,region,rho),
    ensures region.keep(actor,rule) ==> g::step(lib,programs,configuration(a,region,rho),configuration(z,region,rho),actor,rule),
        !region.keep(actor,rule) ==> configuration(a,region,rho)==configuration(z,region,rho),
{
    hide(g::history_sound);hide(g::members);hide(syntax::member);
    let left=configuration(a,region,rho);let right=configuration(z,region,rho);
    if g::landing(a,z,rule) {
        let phase=if rule==r::Rule::Iter {Phase::Loading} else if rule==r::Rule::Finish {Phase::Active} else {Phase::Unloading};
        assert(z==g::land(lib,programs,a,actor,phase));
        assert(local(g::entry(lib,programs,a,actor).landed.receipt,region));
        landing(lib,programs,a,actor,phase,region,rho);
        if !region.episodes.contains(actor) {
            targets(a.state,region,rho,actor,a.state.control.fibers[actor].committed);
            run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,region,rho);
            assert(g::step(lib,programs,left,right,actor,rule));
        }
    } else {match rule {
        r::Rule::Insert | r::Rule::Retire | r::Rule::Remove=>{orchestration(lib,programs,a,z,actor,rule,region,rho);},
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
            g::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
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
