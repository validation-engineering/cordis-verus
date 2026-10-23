//! Nonempty proof client using the executable Mixed driver's actual library.
//! An owner publishes, creates a consumer Child, and admits an external consumer.
//! A foreign provider interleaves, retains its real receipt, then unloads through
//! the compressed target journal. No target legality is supplied as a premise.
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use crate::{
    mixed_driver as driver, mixed_orchestration as orchestration, mixed_transposition as insert,
    shared_execution as shared,
};
use vstd::prelude::*;
verus! {
pub open spec fn key(n:u64)->Port {Port {key:n,realm:0}}
pub open spec fn provided(n:u64)->ISet<Port> {ISet::empty().insert(key(n))}
pub open spec fn view()->ISet<Binding> {ISet::empty().insert(Binding {key:0,realm:0,provider:0})}
pub open spec fn programs()->g::Programs<Port,u64,u64,(),nat> {
    |actor:usize| |pc:nat|if actor==0 && pc==0 {g::Node::Dependent {node:d::Node::Provision {key:key(0),value:10,next:Some(1nat)}}}
    else if actor==0 {g::Node::Child {child:2,dependencies:provided(0),provisions:ISet::empty(),root:0nat,next:None}}
    else if actor==1 {g::Node::Dependent {node:d::Node::Provision {key:key(1),value:23,next:None}}}
    else if actor==2 {g::Node::Dependent {node:d::Node::Operation {operation:key(0),argument:3,select:|_:()|None}}}
    else {g::Node::Dependent {node:d::Node::Unit}}
}
pub open spec fn region()->Region {Region {episodes:ISet::empty().insert(0usize).insert(2usize).insert(3usize),born:ISet::empty().insert(2usize)}}
#[verifier::opaque]
pub open spec fn setup()->Seq<g::Configuration<u64,nat>> {
    let a0=g::empty::<u64,nat>();let a1=insert::insert(a0,0,None,ISet::empty(),provided(0),0nat);
    let a2=insert::insert(a1,1,None,ISet::empty(),provided(1),0nat);
    let a3=g::edit(a2,0,Phase::Loading,ISet::empty(),Some(0nat),Seq::empty());let a4=g::land(driver::library(),programs(),a3,0,Phase::Loading);
    let a5=g::edit(a4,1,Phase::Loading,ISet::empty(),Some(0nat),Seq::empty());let a6=g::land(driver::library(),programs(),a5,1,Phase::Active);
    let a7=g::land(driver::library(),programs(),a6,0,Phase::Active);
    seq![a0,a1,a2,a3,a4,a5,a6,a7]
}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Iter),(1usize,r::Rule::Begin),(1usize,r::Rule::Finish),(0usize,r::Rule::Finish)]}
#[verifier::opaque]
pub open spec fn consumers()->Seq<g::Configuration<u64,nat>> {
    let a0=setup().last();let a1=g::edit(a0,2,Phase::Loading,view(),Some(0nat),Seq::empty());let a2=g::land(driver::library(),programs(),a1,2,Phase::Active);
    let a3=insert::insert(a2,3,None,provided(0),ISet::empty(),0nat);
    let a4=g::edit(a3,3,Phase::Loading,view(),Some(0nat),Seq::empty());let a5=g::land(driver::library(),programs(),a4,3,Phase::Active);
    let a6=shared::retire(a5,0);let a7=g::edit(a6,0,Phase::Unloading,ISet::empty(),None,a6.state.accumulators[0usize]);
    seq![a0,a1,a2,a3,a4,a5,a6,a7]
}
pub open spec fn consumer_labels()->Seq<(usize,r::Rule)> {seq![(2usize,r::Rule::Begin),(2usize,r::Rule::Finish),(3usize,r::Rule::Insert),(3usize,r::Rule::Begin),(3usize,r::Rule::Finish),(0usize,r::Rule::Retire),(0usize,r::Rule::Leave)]}
#[verifier::opaque]
pub open spec fn cleanup()->Seq<g::Configuration<u64,nat>> {
    let a0=consumers().last();let a1=g::edit(a0,2,Phase::Unloading,view(),None,a0.state.accumulators[2usize]);let a2=g::unload(a1,2);
    let a3=g::edit(a2,3,Phase::Unloading,view(),None,a2.state.accumulators[3usize]);let a4=g::unload(a3,3);let a5=g::unload(a4,0);
    let a6=shared::retire(a5,1);let a7=g::edit(a6,1,Phase::Unloading,ISet::empty(),None,a6.state.accumulators[1usize]);let a8=g::unload(a7,1);
    let a9=orchestration::remove(a8,2);
    seq![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9]
}
pub open spec fn cleanup_labels()->Seq<(usize,r::Rule)> {seq![(2usize,r::Rule::Leave),(2usize,r::Rule::Unload),(3usize,r::Rule::Leave),(3usize,r::Rule::Unload),(0usize,r::Rule::Unload),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave),(1usize,r::Rule::Unload),(2usize,r::Rule::Remove)]}
pub open spec fn source()->Seq<g::Configuration<u64,nat>> {setup().drop_last()+consumers().drop_last()+cleanup()}
pub open spec fn labels()->Seq<(usize,r::Rule)> {setup_labels()+consumer_labels()+cleanup_labels()}
pub proof fn members()
    ensures syntax::member(driver::library(),programs(),0,provided(0),provided(0),0nat),
        syntax::member(driver::library(),programs(),1,provided(1),provided(1),0nat),
        syntax::member(driver::library(),programs(),3,provided(0),ISet::empty(),0nat),
{
    syntax::constructor_member(driver::library(),programs(),2,provided(0),ISet::empty(),0nat);
    assert(provided(0).union(ISet::empty()) =~= provided(0));
    syntax::constructor_member(driver::library(),programs(),0,provided(0),provided(0),1nat);
    syntax::constructor_member(driver::library(),programs(),0,provided(0),provided(0),0nat);
    syntax::constructor_member(driver::library(),programs(),1,provided(1),provided(1),0nat);
    syntax::constructor_member(driver::library(),programs(),3,provided(0),ISet::empty(),0nat);
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_setup()
    ensures g::execution(driver::library(),programs(),setup(),setup_labels()),setup().first()==g::empty::<u64,nat>(),
        setup().last().history.len()==3,setup().last().state.accumulators[1usize]==seq![1nat],
        setup().last().state.tables[0usize][key(0)]==10,setup().last().state.tables[1usize][key(1)]==23,
        setup().last().history[2].landed.receipt==(g::Receipt::Child {actor:0,child:2}),
{
    reveal(setup);members();let xs=setup();let ls=setup_labels();let lib=driver::library();
    assert(ISet::<Port>::empty().union(provided(0)) =~= provided(0));assert(ISet::<Port>::empty().union(provided(1)) =~= provided(1));
    insert::insertion_step(lib,programs(),xs[0],0,None,ISet::empty(),provided(0),0nat);
    insert::insertion_step(lib,programs(),xs[1],1,None,ISet::empty(),provided(1),0nat);
    assert(g::step(lib,programs(),xs[2],xs[3],0,r::Rule::Begin));assert(g::step(lib,programs(),xs[3],xs[4],0,r::Rule::Iter));
    assert(g::step(lib,programs(),xs[4],xs[5],1,r::Rule::Begin));assert(g::step(lib,programs(),xs[5],xs[6],1,r::Rule::Finish));
    assert(g::step(lib,programs(),xs[6],xs[7],0,r::Rule::Finish));
    assert forall|i:int|0<=i<ls.len() implies g::step(lib,programs(),xs[i],xs[i+1],ls[i].0,ls[i].1) by {if i==0{}else if i==1{}else if i==2{}else if i==3{}else if i==4{}else if i==5{}else{assert(i==6);}}
    assert(xs.last().state.accumulators[1usize] =~= seq![1nat]);
}
pub proof fn admitted(a:s::State<u64>,actor:usize)
    requires s::registered(a,actor),!a.control.fibers[actor].retired,a.control.fibers[actor].dependencies==provided(0),s::publishes(a,key(0),0),
    ensures s::target(a,actor,view()),
{
    assert forall|k:Port|a.control.fibers[actor].dependencies.contains(k) implies exists|b:Binding|view().contains(b) && b.key==k.key && b.realm==k.realm by {
        assert(k==key(0));assert(view().contains(Binding {key:0,realm:0,provider:0}));
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_consumers()
    ensures g::execution(driver::library(),programs(),consumers(),consumer_labels()),consumers().first()==setup().last(),
        consumers().last().history.len()==5,consumers().last().state.tables[0usize][key(0)]==10u64^3u64,
        lift::resolve(consumers()[1].state,2,key(0))==Some(0usize),
        consumers().last().state.control.fibers[2usize].committed==view(),
        consumers().last().state.control.fibers[3usize].committed==view(),r::relied(consumers().last().state.control,0),
        !g::step(driver::library(),programs(),consumers().last(),g::unload(consumers().last(),0),0,r::Rule::Unload),
{
    actual_setup();reveal(setup);reveal(consumers);members();let xs=consumers();let ls=consumer_labels();let lib=driver::library();
    admitted(xs[0].state,2);assert(s::target(xs[0].state,2,view()));assert(g::step(lib,programs(),xs[0],xs[1],2,r::Rule::Begin));
    assert(xs[1].state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},key(0)));
    assert(lift::resolve(xs[1].state,2,key(0))==Some(0usize));
    assert(g::step(lib,programs(),xs[1],xs[2],2,r::Rule::Finish));
    assert(provided(0).union(ISet::empty()) =~= provided(0));
    insert::insertion_step(lib,programs(),xs[2],3,None,provided(0),ISet::empty(),0nat);
    admitted(xs[3].state,3);assert(s::target(xs[3].state,3,view()));assert(g::step(lib,programs(),xs[3],xs[4],3,r::Rule::Begin));
    assert(g::step(lib,programs(),xs[4],xs[5],3,r::Rule::Finish));assert(g::step(lib,programs(),xs[5],xs[6],0,r::Rule::Retire));
    assert(g::step(lib,programs(),xs[6],xs[7],0,r::Rule::Leave));
    assert forall|i:int|0<=i<ls.len() implies g::step(lib,programs(),xs[i],xs[i+1],ls[i].0,ls[i].1) by {if i==0{}else if i==1{}else if i==2{}else if i==3{}else if i==4{}else if i==5{}else{assert(i==6);}}
    assert(xs.last().state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(r::relied(xs.last().state.control,0));
}
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_cleanup()
    ensures g::execution(driver::library(),programs(),cleanup(),cleanup_labels()),cleanup().first()==consumers().last(),
        trace::settled(cleanup().last(),region()),cleanup().last().history.len()==5,
        forall|i:int|0<=i<5 ==> g::owner(cleanup().last().history[i].landed.receipt)==if i==0 || i==2 {0usize} else if i==1 {1usize} else if i==3 {2usize} else {3usize},
{
    actual_consumers();reveal(setup);reveal(consumers);reveal(cleanup);let xs=cleanup();let ls=cleanup_labels();let lib=driver::library();
    assert(g::step(lib,programs(),xs[0],xs[1],2,r::Rule::Leave));
    reveal_with_fuel(g::restore,4);driver::xor_inverse(10,3);
    assert(g::step(lib,programs(),xs[1],xs[2],2,r::Rule::Unload));
    assert(g::step(lib,programs(),xs[2],xs[3],3,r::Rule::Leave));assert(g::step(lib,programs(),xs[3],xs[4],3,r::Rule::Unload));
    assert(xs[4].state.accumulators[0usize] =~= seq![0nat,2nat]);
    assert(g::step(lib,programs(),xs[4],xs[5],0,r::Rule::Unload));assert(g::step(lib,programs(),xs[5],xs[6],1,r::Rule::Retire));
    assert(g::step(lib,programs(),xs[6],xs[7],1,r::Rule::Leave));assert(g::step(lib,programs(),xs[7],xs[8],1,r::Rule::Unload));
    assert(g::step(lib,programs(),xs[8],xs[9],2,r::Rule::Remove));
    assert forall|i:int|0<=i<ls.len() implies g::step(lib,programs(),xs[i],xs[i+1],ls[i].0,ls[i].1) by {if i==0{}else if i==1{}else if i==2{}else if i==3{}else if i==4{}else if i==5{}else if i==6{}else if i==7{}else{assert(i==8);}}
    assert forall|i:int|0<=i<5 implies g::owner(xs.last().history[i].landed.receipt)==if i==0 || i==2 {0usize} else if i==1 {1usize} else if i==3 {2usize} else {3usize} by { }
    assert forall|n:usize|s::registered(xs.last().state,n) && region().episodes.contains(n) implies xs.last().state.control.fibers[n].phase==Phase::Inactive
        && (region().born.contains(n) ==> xs.last().state.control.fibers[n].retired) by { }
}
/// Closure admits internal consumers but rejects retaining either consumer's
/// activation after deleting its provider's publication.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn source_guards()
    ensures trace::admissible(source(),region()),
        !closed(consumers().last().state,Region {episodes:ISet::empty().insert(0usize).insert(2usize),born:ISet::empty().insert(2usize)}),
        !closed(consumers().last().state,Region {episodes:ISet::empty().insert(0usize).insert(3usize),born:ISet::empty()}),
        !trace::admissible(source(),Region {episodes:region().episodes,born:ISet::empty()}),
{
    actual_consumers();actual_cleanup();reveal(setup);reveal(consumers);reveal(cleanup);reveal_with_fuel(g::restore,4);
    assert forall|i:int|0<=i<source().len() implies closed(source()[i].state,region()) by {
        let a=source()[i].state;
        assert forall|n:usize|s::registered(a,n) implies n==0 || n==1 || n==2 || n==3 by { }
        assert forall|n:usize|s::registered(a,n) && !region().born.contains(n) && a.control.fibers[n].parent.is_some()
            implies !region().born.contains(a.control.fibers[n].parent.unwrap()) by { }
        assert forall|n:usize,m:usize|s::registered(a,n) && s::registered(a,m) && !region().episodes.contains(n) && region().episodes.contains(m)
            implies a.control.fibers[n].dependencies.disjoint(a.control.fibers[m].provisions) by {assert(n==1);}
    }
    assert forall|i:int|0<=i<source().last().history.len() implies local(source().last().history[i].landed.receipt,region()) by { }
    let bad=Region {episodes:ISet::empty().insert(0usize).insert(2usize),born:ISet::empty().insert(2usize)};
    assert(consumers().last().state.control.fibers[3usize].dependencies.contains(key(0)));
    assert(!consumers().last().state.control.fibers[3usize].dependencies.disjoint(consumers().last().state.control.fibers[0usize].provisions));
    assert(!closed(consumers().last().state,bad));
    let other=Region {episodes:ISet::empty().insert(0usize).insert(3usize),born:ISet::empty()};
    assert(!consumers().last().state.control.fibers[2usize].dependencies.disjoint(consumers().last().state.control.fibers[0usize].provisions));
    assert(!closed(consumers().last().state,other));
    let missing_birth=Region {episodes:region().episodes,born:ISet::empty()};
    assert(!local(source().last().history[2].landed.receipt,missing_birth));
    assert(!trace::admissible(source(),missing_birth));
}
pub proof fn append<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:Seq<g::Configuration<U,I>>,b:Seq<g::Configuration<U,I>>,x:Seq<(usize,r::Rule)>,y:Seq<(usize,r::Rule)>)
    requires g::execution(lib,programs,a,x),g::execution(lib,programs,b,y),a.last()==b.first(),
    ensures g::execution(lib,programs,a.drop_last()+b,x+y),
{
    assert forall|i:int|0<=i<(x+y).len() implies g::step(lib,programs,(a.drop_last()+b)[i],(a.drop_last()+b)[i+1],(x+y)[i].0,(x+y)[i].1) by {
        if i<x.len() {assert(g::step(lib,programs,a[i],a[i+1],x[i].0,x[i].1));}
        else {assert(g::step(lib,programs,b[i-x.len()],b[i-x.len()+1],y[i-x.len()].0,y[i-x.len()].1));}
    }
}
pub proof fn filtered_history(h:Seq<g::Entry<u64,nat>>,rho:spec_fn(nat)->nat)
    requires h.len()==5,forall|i:int|0<=i<5 ==> g::owner(h[i].landed.receipt)==if i==0 || i==2 {0usize} else if i==1 {1usize} else if i==3 {2usize} else {3usize},
    ensures history(h,region(),rho).len()==1,history(h,region(),rho)[0].landed.receipt==h[1].landed.receipt,
{
    reveal_with_fuel(history,7);
}
proof fn filtered_setup()
    ensures trace::kept(setup_labels(),region()).len()==4,
{reveal_with_fuel(trace::kept,9);}
proof fn filtered_consumers()
    ensures trace::kept(consumer_labels(),region()).len()==2,
{reveal_with_fuel(trace::kept,9);}
proof fn filtered_cleanup()
    ensures trace::kept(cleanup_labels(),region()).len()==3,
{reveal_with_fuel(trace::kept,11);}
pub proof fn filtered_labels()
    ensures trace::kept(labels(),region()).len()==9,
{
    hide(trace::kept);filtered_setup();filtered_consumers();filtered_cleanup();
    trace::kept_concat(setup_labels(),consumer_labels(),region());
    trace::kept_concat(setup_labels()+consumer_labels(),cleanup_labels(),region());
}
#[verifier::spinoff_prover]
pub proof fn nonempty()
    ensures g::execution(driver::library(),programs(),source(),labels()),source().first()==g::empty::<u64,nat>(),
        g::execution(driver::library(),programs(),trace::target(source(),labels(),region()),trace::kept(labels(),region())),
        p::project(source().last().state,ISet::full())==p::project(trace::target(source(),labels(),region()).last().state,ISet::full()),
        trace::kept(labels(),region()).len()==9,trace::target(source(),labels(),region()).last().history.len()==1,
        trace::target(source(),labels(),region()).last().history[0].landed.receipt==source().last().history[1].landed.receipt,
{
    actual_setup();actual_consumers();actual_cleanup();source_guards();driver::library_theory();
    append(driver::library(),programs(),setup(),consumers(),setup_labels(),consumer_labels());
    let first=setup().drop_last()+consumers();
    append(driver::library(),programs(),first,cleanup(),setup_labels()+consumer_labels(),cleanup_labels());
    assert(first.drop_last()+cleanup() =~= source());
    trace::from_source(|_:Port,a:u64,b:u64|a==b,driver::library(),programs(),source(),labels(),region());
    let rho=|t:nat|index(source().last().history,region(),t);
    g::from_empty_safe(|_:Port,a:u64,b:u64|a==b,driver::library(),programs(),source(),labels());
    trace::closing_observation(source().last(),region(),rho);
    filtered_labels();filtered_history(source().last().history,rho);
}
}
