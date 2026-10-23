//! Source-only admission facts for executable command compaction.
#[cfg(verus_keep_ghost)]
use super::{a, available, names, renamed, selected};
#[cfg(verus_keep_ghost)]
use crate::{alpha, mixed_driver::Transition};
use vstd::prelude::*;
verus! {
pub open spec fn references(t:Transition,n:usize)->bool {
    match t {Transition::Insert {parent,..}=>parent==Some(n),_=>t.actor()==n}
}
pub open spec fn closed(ts:Seq<Transition>,keep:Seq<bool>)->bool {
    ts.len()==keep.len() && forall|i:int,n:usize|0<=i<ts.len() && keep[i] && references(ts[i],n)
        ==> exists|j:int|0<=j<i && keep[j] && a::birth_spec(ts[j])==Some(n)
}
pub proof fn monotone(ts:Seq<Transition>,i:int,j:int)
    requires 0<=i<=j<=ts.len(),
    ensures a::count(ts.take(i))<=a::count(ts.take(j)),
        i<j && a::birth_spec(ts[i]).is_some() ==> a::count(ts.take(i))<a::count(ts.take(j)),
    decreases j-i,
{
    if i<j {
        monotone(ts,i,j-1);
        assert(ts.take(j).drop_last()==ts.take(j-1));assert(ts.take(j).last()==ts[j-1]);
    }
}
pub proof fn selected_monotone(ts:Seq<Transition>,keep:Seq<bool>,i:int,j:int)
    requires ts.len()==keep.len(),0<=i<=j<=ts.len(),
    ensures a::count(selected(ts.take(i),keep.take(i)))<=a::count(selected(ts.take(j),keep.take(j))),
        i<j && keep[i] && a::birth_spec(ts[i]).is_some() ==> a::count(selected(ts.take(i),keep.take(i)))<a::count(selected(ts.take(j),keep.take(j))),
    decreases j-i,
{
    if i<j {
        selected_monotone(ts,keep,i,j-1);super::prefix(ts,keep,j-1);
        if keep[j-1] {assert(selected(ts.take(j),keep.take(j)).drop_last()==selected(ts.take(j-1),keep.take(j-1)));}
    }
}
pub proof fn selected_bound(ts:Seq<Transition>,keep:Seq<bool>)
    requires ts.len()==keep.len(),
    ensures a::count(selected(ts,keep))<=a::count(ts),
    decreases ts.len(),
{
    if ts.len()>0 {
        selected_bound(ts.drop_last(),keep.drop_last());
        if keep.last() {assert(selected(ts,keep).drop_last()==selected(ts.drop_last(),keep.drop_last()));}
    }
}
pub proof fn birth_bound(ts:Seq<Transition>,bound:nat,i:int)
    requires a::history(ts,bound),0<=i<ts.len(),a::birth_spec(ts[i]).is_some(),
    ensures a::birth_spec(ts[i]).unwrap()==a::count(ts.take(i)),a::count(ts.take(i))<bound,
{
    monotone(ts,i,ts.len() as int);assert(ts.take(ts.len() as int)==ts);
}
pub open spec fn origin_bound(map:&names::Names,next:nat,source:nat)->bool {
    forall|n:usize|map.name_spec(n)<next ==> n<source
}
pub proof fn extend_origin(before:&names::Names,after:&names::Names,born:usize,next:usize,source:nat)
    requires before.wf(),born==source,origin_bound(before,next as nat,source),
        forall|n:usize|after.name_spec(n)==alpha::swap(before.name_spec(born),next,before.name_spec(n)),
    ensures origin_bound(after,next as nat+1,source+1),
{
    before.bijection();let rho=before.renaming();
    assert(before.name_spec(born)>=next);
    assert forall|n:usize|after.name_spec(n)<next as nat+1 implies n<source+1 by {
        if before.name_spec(n)==before.name_spec(born) {
            assert((rho.backward)((rho.forward)(n))==n);
            assert((rho.backward)((rho.forward)(born))==born);assert(n==born);
        } else {assert(before.name_spec(n)<next);assert(n<source);}
    }
}
pub proof fn renamed_count(r:alpha::Renaming,ts:Seq<Transition>)
    ensures a::count(renamed(r,ts))==a::count(ts),
    decreases ts.len(),
{
    if ts.len()>0 {
        renamed_count(r,ts.drop_last());names::label(r,ts.last());
        assert(renamed(r,ts).drop_last()==renamed(r,ts.drop_last()));
    }
}
pub open spec fn paired(map:&names::Names,ts:Seq<Transition>,keep:Seq<bool>)->bool {
    forall|j:int|0<=j<ts.len() && keep[j] && a::birth_spec(ts[j]).is_some() ==>
        map.name_spec(a::birth_spec(ts[j]).unwrap())==a::count(selected(ts.take(j),keep.take(j)))
}
pub proof fn earlier(map:&names::Names,ts:Seq<Transition>,keep:Seq<bool>,i:int,n:usize)
    requires closed(ts,keep),paired(map,ts,keep),0<=i<ts.len(),keep[i],references(ts[i],n),
    ensures map.name_spec(n)<a::count(selected(ts.take(i),keep.take(i))),
{
    let j=choose|j:int|0<=j<i && keep[j] && a::birth_spec(ts[j])==Some(n);
    selected_monotone(ts,keep,j,i);
}
pub proof fn enabled(map:&names::Names,ts:Seq<Transition>,keep:Seq<bool>,i:int)
    requires closed(ts,keep),paired(map,ts,keep),0<=i<ts.len(),keep[i],
    ensures available(a::count(selected(ts.take(i),keep.take(i))),names::renamed(map.renaming(),ts[i])),
{
    let t=ts[i];names::label(map.renaming(),t);
    match t {
        Transition::Insert {parent,..}=>{if parent.is_some() {earlier(map,ts,keep,i,parent.unwrap());}},
        _=>{earlier(map,ts,keep,i,t.actor());},
    }
}
}
