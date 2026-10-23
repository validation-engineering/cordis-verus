//! Inhabited native episode-splice profile: repeated owner episodes, an actual
//! consumer, an owned Child, a failed-cleanup stutter and an independent provider.
//! Typed payloads are arbitrary; no successful target execution is supplied.
#[cfg(verus_keep_ghost)]
use super::super::{History, Observation};
#[cfg(verus_keep_ghost)]
use super::{boundary, closed, trace::Window, Region};
#[cfg(verus_keep_ghost)]
use crate::{
    lifecycle_state::{native::runtime::owner::EpisodeOwner, services::NativePublication},
    refinement as r, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {
pub open spec fn port(n:usize)->Port {Port {key:n as u64,realm:0}}
pub open spec fn ports(n:usize)->ISet<Port> {ISet::empty().insert(port(n))}
pub open spec fn view(n:usize)->ISet<Binding> {
    if n==2 || n==3 {ISet::empty().insert(Binding {key:0,realm:0,provider:0})} else {ISet::empty()}
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(2usize,r::Rule::Insert),
        (0usize,r::Rule::Begin),(0usize,r::Rule::Finish),(0usize,r::Rule::Restart),(0usize,r::Rule::Unload),
        (0usize,r::Rule::Begin),(0usize,r::Rule::Finish),(3usize,r::Rule::Insert),
        (3usize,r::Rule::Begin),(3usize,r::Rule::Finish),(2usize,r::Rule::Begin),(2usize,r::Rule::Finish),
        (1usize,r::Rule::Begin),(1usize,r::Rule::Finish),(0usize,r::Rule::Restart),
        (2usize,r::Rule::Leave),(2usize,r::Rule::Stutter),(2usize,r::Rule::Unload),
        (3usize,r::Rule::Leave),(3usize,r::Rule::Unload),(3usize,r::Rule::Retire),(3usize,r::Rule::Remove),
        (0usize,r::Rule::Unload),(0usize,r::Rule::Begin),(0usize,r::Rule::Finish)]
}
pub open spec fn present(n:usize,at:nat)->bool {
    if n<3 {n<at} else {n==3 && 10<=at<=23}
}
pub open spec fn phase(n:usize,at:nat)->Phase {
    if n==0 {
        if at==4 || at==8 || at==26 {Phase::Loading}
        else if at==5 || 9<=at<=16 || at==27 {Phase::Active}
        else if at==6 || 17<=at<=24 {Phase::Unloading} else {Phase::Inactive}
    } else if n==1 {
        if at==15 {Phase::Loading} else if 16<=at {Phase::Active} else {Phase::Inactive}
    } else if n==2 {
        if at==13 {Phase::Loading} else if 14<=at<=17 {Phase::Active} else if 18<=at<=19 {Phase::Unloading} else {Phase::Inactive}
    } else {
        if at==11 {Phase::Loading} else if 12<=at<=20 {Phase::Active} else if at==21 {Phase::Unloading} else {Phase::Inactive}
    }
}
pub open spec fn owner_epoch(n:usize,at:nat)->int {
    if n==0 {if at<=6 {0} else if at<=24 {1} else {5}}
    else if n==1 {4} else if n==2 {3} else {2}
}
pub open spec fn state<V>(p:Seq<NativePublication<V>>,owners:Seq<EpisodeOwner>,at:nat)->Observation<V> {
    Observation {
        control:r::State {fibers:IMap::new(|n:usize|present(n,at),|n:usize|r::Fiber {
            parent:if n==3 {Some(0usize)} else {None},retired:n==3 && at>=23,phase:phase(n,at),
            dependencies:if n==2 || n==3 {ports(0)} else {ISet::empty()},provisions:ports(n),
            committed:if phase(n,at)==Phase::Inactive {ISet::empty()} else {view(n)}})},
        publications:Map::new(set![0usize,1usize,2usize,3usize].filter(|n:usize|present(n,at) && (phase(n,at)==Phase::Active || phase(n,at)==Phase::Unloading)),|n:usize|p[owner_epoch(n,at)]),
        owners:Map::new(set![0usize,1usize,2usize,3usize].filter(|n:usize|present(n,at) && phase(n,at)!=Phase::Inactive),|n:usize|owners[owner_epoch(n,at)]),
    }
}
pub open spec fn source<V>(p:Seq<NativePublication<V>>,owners:Seq<EpisodeOwner>)->History<V> {
    History {states:Seq::new(28,|i:int|state(p,owners,i as nat)),labels:labels()}
}
pub open spec fn window()->Window {Window {start:7,end:25,region:Region {episodes:ISet::empty().insert(0usize).insert(2usize).insert(3usize),born:ISet::empty().insert(3usize)}}}
pub proof fn admitted(a:r::State,n:usize)
    requires n==2 || n==3,r::registered(a,n),!a.fibers[n].retired,a.fibers[n].dependencies==ports(0),r::publishes(a,port(0),0),
    ensures r::target(a,n,view(n)),
{
    let b=Binding {key:0,realm:0,provider:0};assert(view(n).contains(b));
    assert forall|p:Port|a.fibers[n].dependencies.contains(p) implies
        exists|b:Binding|view(n).contains(b) && b.key==p.key && b.realm==p.realm by {
        assert(p==port(0));assert(view(n).contains(b) && b.key==p.key && b.realm==p.realm);
    }
}
/// Source transitions themselves establish reachability of the finite profile.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn source_steps<V>(p:Seq<NativePublication<V>>,owners:Seq<EpisodeOwner>)
    requires p.len()==6,owners.len()==6,
    ensures source(p,owners).valid(),
{
    let h=source(p,owners);
    assert forall|i:int|0<=i<h.labels.len() implies #[trigger] super::super::step(h.states[i],h.states[i+1],h.labels[i].0,h.labels[i].1) by {
        let a=h.states[i];let z=h.states[i+1];let actor=h.labels[i].0;let rule=h.labels[i].1;
        assert(r::frame(a.control,z.control,actor));
        if (rule==r::Rule::Begin || rule==r::Rule::Finish) && (actor==2 || actor==3) {admitted(a.control,actor);}

        match rule {
            r::Rule::Begin=>{assert(z.owners =~= a.owners.insert(actor,z.owners[actor]));},
            r::Rule::Finish=>{assert(z.publications =~= a.publications.insert(actor,z.publications[actor]));},
            r::Rule::Unload=>{assert(z.owners =~= a.owners.remove(actor));assert(z.publications =~= a.publications.remove(actor));},
            _=>{},
        }
        if rule!=r::Rule::Begin && rule!=r::Rule::Unload {assert(z.owners =~= a.owners);}
        if rule!=r::Rule::Finish && rule!=r::Rule::Unload {assert(z.publications =~= a.publications);}
        if rule==r::Rule::Leave {
            let b=Binding {key:0,realm:0,provider:0};assert(a.control.fibers[actor].committed.contains(b));
            assert(!r::publishes(a.control,port(0),0));assert(!r::coherent(a.control,actor));
        }
        if rule==r::Rule::Stutter {assert(a.control.fibers =~= z.control.fibers);}
        if i==0 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==1 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==2 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==3 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==4 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==5 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==6 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==7 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==8 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==9 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==10 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==11 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==12 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==13 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==14 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==15 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==16 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==17 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==18 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==19 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==20 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==21 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==22 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==23 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==24 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==25 {assert(r::step(a.control,z.control,actor,rule));}
        else if i==26 {assert(r::step(a.control,z.control,actor,rule));}

    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn source_guards<V>(p:Seq<NativePublication<V>>,owners:Seq<EpisodeOwner>)
    requires p.len()==6,owners.len()==6,
    ensures window().admissible(source(p,owners)),
        !window().region.keep(0,r::Rule::Begin),!window().region.keep(3,r::Rule::Insert),
        !window().region.keep(2,r::Rule::Unload),window().region.keep(1,r::Rule::Finish),
{
    let h=source(p,owners);let region=window().region;
    assert(boundary(h.states[7],region));assert(boundary(h.states[25],region));
    assert forall|i:int|7<=i<=25 implies closed(h.states[i].control,region) by {
        assert forall|n:usize|r::registered(h.states[i].control,n) implies n==0 || n==1 || n==2 || n==3 by { }
        assert forall|n:usize,m:usize|r::registered(h.states[i].control,n) && r::registered(h.states[i].control,m)
            && !region.episodes.contains(n) && region.episodes.contains(m) implies h.states[i].control.fibers[n].dependencies.disjoint(h.states[i].control.fibers[m].provisions) by {assert(n==1);}
    }
    assert(window().births_closed(h));
}
pub proof fn kept_steps<V>(p:Seq<NativePublication<V>>,owners:Seq<EpisodeOwner>)
    ensures window().positions(source(p,owners),27)==seq![0int,1,2,3,4,5,6,14,15,25,26],
{reveal_with_fuel(Window::positions,29);}
/// 27 source lifecycle steps become 11 legal surviving steps. The earlier
/// and later owner episodes retain their exact typed values and owner identity.
pub proof fn nonempty<V>(p:Seq<NativePublication<V>>,owners:Seq<EpisodeOwner>)->(out:History<V>)
    requires p.len()==6,owners.len()==6,
    ensures out.valid(),out==window().target(source(p,owners)),out.labels.len()==11,
        out.states.last()==source(p,owners).states.last(),
        out.labels[3]==(0usize,r::Rule::Begin),out.labels[4]==(0usize,r::Rule::Finish),
        out.labels[7]==(1usize,r::Rule::Begin),out.labels[8]==(1usize,r::Rule::Finish),
        out.labels[9]==(0usize,r::Rule::Begin),out.labels[10]==(0usize,r::Rule::Finish),
        out.states[4].owners.contains_pair(0usize,owners[0]),out.states[5].publications.contains_pair(0usize,p[0]),
        out.states[10].owners.contains_pair(0usize,owners[5]),out.states[11].publications.contains_pair(0usize,p[5]),
{
    source_steps(p,owners);source_guards(p,owners);kept_steps(p,owners);let h=source(p,owners);let w=window();
    let out=w.delete(h);w.construct(h,27);w.unchanged_outside(h,3);w.unchanged_outside(h,4);w.unchanged_outside(h,25);w.unchanged_outside(h,26);
    out
}
/// Omitted consumers/births and premature closing cuts are genuine source
/// obstructions. Parent Unload cannot substitute for its Child's Remove.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn rejected_profiles<V>(p:Seq<NativePublication<V>>,owners:Seq<EpisodeOwner>)
    requires p.len()==6,owners.len()==6,
    ensures !((Window {region:Region {episodes:ISet::empty().insert(0usize).insert(3usize),born:window().region.born},..window()}).admissible(source(p,owners))),
        !((Window {region:Region {episodes:window().region.episodes,born:ISet::empty()},..window()}).admissible(source(p,owners))),
        !((Window {end:23,..window()}).admissible(source(p,owners))),
        !((Window {end:24,..window()}).admissible(source(p,owners))),
        !r::step(source(p,owners).states[17].control,source(p,owners).states[25].control,0,r::Rule::Unload),
{
    let h=source(p,owners);
    let consumer=Window {region:Region {episodes:ISet::empty().insert(0usize).insert(3usize),born:window().region.born},..window()};
    assert(h.states[7].control.fibers[2usize].dependencies.contains(port(0)));
    assert(h.states[7].control.fibers[0usize].provisions.contains(port(0)));
    assert(!h.states[7].control.fibers[2usize].dependencies.disjoint(h.states[7].control.fibers[0usize].provisions));
    assert(!closed(h.states[7].control,consumer.region));
    let birth=Window {region:Region {episodes:window().region.episodes,born:ISet::empty()},..window()};
    assert(!birth.births_closed(h));
    assert(!boundary(h.states[23],window().region));assert(!boundary(h.states[24],window().region));
    assert(h.states[17].control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));assert(r::relied(h.states[17].control,0));
}
}
