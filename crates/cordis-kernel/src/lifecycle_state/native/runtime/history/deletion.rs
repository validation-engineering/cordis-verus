//! Source-closed deletion of native lifecycle episodes in a selected window.
//! This preserves the exact typed publications and Episode owners of survivors.
//! The `joint` module extends this projection to source-admitted Journal
//! transport. Physical allocator and arbitrary callback replay remain separate.
pub mod client;
pub mod joint;
pub mod replay;
pub mod trace;
#[cfg(verus_keep_ghost)]
use super::Observation;
pub use crate::closed_region_deletion::Region;
#[cfg(verus_keep_ghost)]
use crate::{refinement as r, Binding, Phase, Port};
use vstd::prelude::*;

verus! {
pub open spec fn control(a:r::State,region:Region)->r::State {
    r::State {fibers:IMap::new(|n:usize|r::registered(a,n) && !region.born.contains(n),
        |n:usize|crate::closed_region_deletion::fiber(a.fibers[n],n,region))}
}
pub open spec fn retain<T>(a:Map<usize,T>,region:Region)->Map<usize,T> {
    Map::new(a.dom().filter(|n:usize|!region.episodes.contains(n)),|n:usize|a[n])
}
pub open spec fn project<V>(a:Observation<V>,region:Region)->Observation<V> {
    Observation {control:control(a.control,region),publications:retain(a.publications,region),owners:retain(a.owners,region)}
}
/// Every guard examines the actual source declarations and parent identities.
/// Consumers of a selected publication must join the selected region.
pub open spec fn closed(a:r::State,region:Region)->bool {
    &&& forall|n:usize|r::registered(a,n) && !region.born.contains(n) && a.fibers[n].parent.is_some()
        ==> !region.born.contains(a.fibers[n].parent.unwrap())
    &&& forall|n:usize,m:usize|r::registered(a,n) && r::registered(a,m) && !region.episodes.contains(n) && region.episodes.contains(m)
        ==> a.fibers[n].dependencies.disjoint(a.fibers[m].provisions)
}
/// A splice rejoins the exact source, rather than treating a retired registry
/// entry as absent. Born names therefore need their actual Remove before end.
pub open spec fn boundary<V>(a:Observation<V>,region:Region)->bool {
    &&& forall|n:usize|region.born.contains(n) ==> !r::registered(a.control,n)
    &&& forall|n:usize|region.episodes.contains(n) ==> !a.publications.contains_key(n) && !a.owners.contains_key(n)
        && (r::registered(a.control,n) ==> a.control.fibers[n].phase==Phase::Inactive && a.control.fibers[n].committed.is_empty())
}
pub proof fn boundary_identity<V>(a:Observation<V>,region:Region)
    requires region.wf(),boundary(a,region),ensures project(a,region)==a,
{
    assert(control(a.control,region).fibers =~= a.control.fibers);
    assert(retain(a.publications,region) =~= a.publications);assert(retain(a.owners,region) =~= a.owners);
}
pub proof fn retained_target(a:r::State,region:Region,actor:usize,view:ISet<Binding>)
    requires region.wf(),closed(a,region),r::registered(a,actor),!region.episodes.contains(actor),
    ensures r::target(a,actor,view)==r::target(control(a,region),actor,view),
        r::coherent(a,actor)==r::coherent(control(a,region),actor),
{
    assert forall|p:Port,n:usize|a.fibers[actor].dependencies.contains(p) implies
        r::publishes(a,p,n)==r::publishes(control(a,region),p,n) by {
        if r::registered(a,n) && region.episodes.contains(n) {
            assert(a.fibers[actor].dependencies.disjoint(a.fibers[n].provisions));
        }
    }
}
#[verifier::spinoff_prover]
pub proof fn control_step(a:r::State,z:r::State,actor:usize,rule:r::Rule,region:Region)
    requires region.wf(),r::step(a,z,actor,rule),closed(a,region),closed(z,region),
    ensures region.keep(actor,rule) ==> r::step(control(a,region),control(z,region),actor,rule),
        !region.keep(actor,rule) ==> control(a,region)==control(z,region),
{
    let x=control(a,region);let y=control(z,region);
    if region.keep(actor,rule) {
        assert(r::frame(x,y,actor));
        if r::registered(a,actor) && !region.episodes.contains(actor) {retained_target(a,region,actor,z.fibers[actor].committed);}
        match rule {
            r::Rule::Insert=>{
                assert forall|m:usize,p:Port|r::registered(x,m) && x.fibers[m].provisions.contains(p) implies !y.fibers[actor].provisions.contains(p) by { }
            },
            r::Rule::Remove=>{assert forall|m:usize|r::registered(x,m) implies x.fibers[m].parent!=Some(actor) by { }},
            r::Rule::Unload=>{
                assert(!r::relied(x,actor)) by {
                    assert forall|m:usize,b:Binding|r::registered(x,m) && m!=actor && x.fibers[m].phase!=Phase::Inactive
                        && x.fibers[m].committed.contains(b) implies b.provider!=actor by { }
                }
            },
            r::Rule::Stutter|r::Rule::Iter=>{assert(x.fibers =~= y.fibers);},
            _=>{},
        }
    } else {assert(x.fibers =~= y.fibers);}
}
pub proof fn retain_insert<T>(a:Map<usize,T>,n:usize,value:T,region:Region)
    ensures retain(a.insert(n,value),region)==if region.episodes.contains(n) {retain(a,region)} else {retain(a,region).insert(n,value)},
{
    if region.episodes.contains(n) {assert(retain(a.insert(n,value),region) =~= retain(a,region));}
    else {assert(retain(a.insert(n,value),region) =~= retain(a,region).insert(n,value));}
}
pub proof fn retain_remove<T>(a:Map<usize,T>,n:usize,region:Region)
    ensures retain(a.remove(n),region)==if region.episodes.contains(n) {retain(a,region)} else {retain(a,region).remove(n)},
{
    if region.episodes.contains(n) {assert(retain(a.remove(n),region) =~= retain(a,region));}
    else {assert(retain(a.remove(n),region) =~= retain(a,region).remove(n));}
}
/// Kept steps retain their actual typed table/owner payload. Omitted steps
/// stutter after projection; successful target admission is a conclusion.
#[verifier::spinoff_prover]
pub proof fn transport<V>(a:Observation<V>,z:Observation<V>,actor:usize,rule:r::Rule,region:Region)
    requires region.wf(),super::step(a,z,actor,rule),closed(a.control,region),closed(z.control,region),
    ensures region.keep(actor,rule) ==> super::step(project(a,region),project(z,region),actor,rule),
        !region.keep(actor,rule) ==> project(a,region)==project(z,region),
{
    control_step(a.control,z.control,actor,rule,region);
    match rule {
        r::Rule::Begin=>{retain_insert(a.owners,actor,z.owners[actor],region);},
        r::Rule::Finish=>{retain_insert(a.publications,actor,z.publications[actor],region);},
        r::Rule::Unload=>{retain_remove(a.owners,actor,region);retain_remove(a.publications,actor,region);},
        _=>{},
    }
}
}
