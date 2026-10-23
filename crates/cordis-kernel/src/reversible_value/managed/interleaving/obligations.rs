//! Remaining strict inverses for interleaved real managed effects.
//! Depth makes an enabled inverse last on its allocation, without imposing
//! global LIFO on independent allocations or assuming every attempt succeeds.
use crate::reversible_value::{managed::semantics::Value, service_composition::Address};
use vstd::prelude::*;

verus! {
pub ghost struct Inverse<T:?Sized> {
    pub address:Address,pub before:Value<T>,pub after:Value<T>,pub origin:nat,
}
pub open spec fn depth<T:?Sized>(value:Value<T>)->nat {
    match value {Value::Scalar(s)=>s.depth as nat,Value::Payload(s)=>s.depth as nat}
}
impl<T:?Sized> Inverse<T> {
    pub open spec fn valid(&self)->bool {depth(self.after)==depth(self.before)+1}
    pub open spec fn undo(&self,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>> {
        if heap.contains_pair(self.address,self.after) {Some(heap.insert(self.address,self.before))} else {None}
    }
    pub open spec fn forward(&self,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>> {
        if heap.contains_pair(self.address,self.before) {Some(heap.insert(self.address,self.after))} else {None}
    }
}
pub open spec fn valid<T:?Sized>(slots:Seq<Option<Inverse<T>>>)->bool {
    forall|i:int|0<=i<slots.len() && (#[trigger] slots[i]).is_some() ==> slots[i].unwrap().valid()
}
pub open spec fn recover<T:?Sized>(slots:Seq<Option<Inverse<T>>>,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>>
    decreases slots.len(),
{
    if slots.len()==0 {Some(heap)} else {match slots.last() {
        None=>recover(slots.drop_last(),heap),
        Some(inv)=>match inv.undo(heap) {None=>None,Some(previous)=>recover(slots.drop_last(),previous)},
    }}
}
pub proof fn forward<T:?Sized>(slots:Seq<Option<Inverse<T>>>,inverse:Inverse<T>,heap:Map<Address,Value<T>>)
    requires inverse.forward(heap).is_some(),
    ensures recover(slots.push(Some(inverse)),inverse.forward(heap).unwrap())==recover(slots,heap),
{
    assert(slots.push(Some(inverse)).drop_last() =~= slots);
    assert(heap.insert(inverse.address,inverse.after).insert(inverse.address,inverse.before) =~= heap);
}
/// Every remaining inverse's expected depth is bounded by the actual current
/// depth. Undoing a later same-allocation inverse decreases that bound strictly.
pub proof fn depth_bound<T:?Sized>(slots:Seq<Option<Inverse<T>>>,heap:Map<Address,Value<T>>,i:int)
    requires valid(slots),recover(slots,heap).is_some(),0<=i<slots.len(),slots[i].is_some(),
    ensures heap.contains_key(slots[i].unwrap().address),depth(slots[i].unwrap().after)<=depth(heap[slots[i].unwrap().address]),
    decreases slots.len(),
{
    if i<slots.len()-1 {
        let prefix=slots.drop_last();
        match slots.last() {
            None=>depth_bound(prefix,heap,i),
            Some(last)=>{
                depth_bound(prefix,last.undo(heap).unwrap(),i);
                assert(last.valid());
            },
        }
    }
}
pub proof fn enabled_is_last<T:?Sized>(slots:Seq<Option<Inverse<T>>>,heap:Map<Address,Value<T>>,i:int)
    requires valid(slots),recover(slots,heap).is_some(),0<=i<slots.len(),slots[i].is_some(),slots[i].unwrap().undo(heap).is_some(),
    ensures forall|j:int|i<j<slots.len() && (#[trigger] slots[j]).is_some() ==> slots[j].unwrap().address!=slots[i].unwrap().address,
    decreases slots.len(),
{
    if i<slots.len()-1 {
        let prefix=slots.drop_last();
        match slots.last() {
            None=>enabled_is_last(prefix,heap,i),
            Some(last)=>{
                let previous=last.undo(heap).unwrap();
                depth_bound(prefix,previous,i);assert(last.valid());
                assert(last.address!=slots[i].unwrap().address);
                enabled_is_last(prefix,previous,i);
            },
        }
        assert forall|j:int|i<j<slots.len() && (#[trigger] slots[j]).is_some() implies slots[j].unwrap().address!=slots[i].unwrap().address by {
            if j<prefix.len() {assert(prefix[j]==slots[j]);}
        }
    }
}
proof fn exchange<T:?Sized>(first:Inverse<T>,second:Inverse<T>,heap:Map<Address,Value<T>>)
    requires first.address!=second.address,first.undo(heap).is_some(),second.undo(heap).is_some(),
    ensures first.undo(second.undo(heap).unwrap()).is_some(),second.undo(first.undo(heap).unwrap()).is_some(),
        first.undo(second.undo(heap).unwrap())==second.undo(first.undo(heap).unwrap()),
{
    assert(heap.insert(first.address,first.before).insert(second.address,second.before)
        =~= heap.insert(second.address,second.before).insert(first.address,first.before));
}
proof fn remove_independent<T:?Sized>(slots:Seq<Option<Inverse<T>>>,heap:Map<Address,Value<T>>,i:int)
    requires recover(slots,heap).is_some(),0<=i<slots.len(),slots[i].is_some(),slots[i].unwrap().undo(heap).is_some(),
        forall|j:int|i<j<slots.len() && (#[trigger] slots[j]).is_some() ==> slots[j].unwrap().address!=slots[i].unwrap().address,
    ensures recover(slots.update(i,None),slots[i].unwrap().undo(heap).unwrap())==recover(slots,heap),
    decreases slots.len(),
{
    if i<slots.len()-1 {
        let prefix=slots.drop_last();let selected=slots[i].unwrap();
        match slots.last() {
            None=>remove_independent(prefix,heap,i),
            Some(last)=>{
                exchange(last,selected,heap);remove_independent(prefix,last.undo(heap).unwrap(),i);
            },
        }
        assert(slots.update(i,None).drop_last() =~= prefix.update(i,None));
    } else {assert(slots.update(i,None).drop_last() =~= slots.drop_last());}
}
/// An actually enabled inverse may be removed anywhere in the word. Its
/// source depth law derives the required per-allocation ordering automatically.
pub proof fn consume<T:?Sized>(slots:Seq<Option<Inverse<T>>>,heap:Map<Address,Value<T>>,i:int)
    requires valid(slots),recover(slots,heap).is_some(),0<=i<slots.len(),slots[i].is_some(),slots[i].unwrap().undo(heap).is_some(),
    ensures recover(slots.update(i,None),slots[i].unwrap().undo(heap).unwrap())==recover(slots,heap),valid(slots.update(i,None)),
        forall|j:int|0<=j<slots.len() ==> (#[trigger] slots.update(i,None)[j])!=slots[i],
{
    enabled_is_last(slots,heap,i);remove_independent(slots,heap,i);
    assert forall|j:int|0<=j<slots.len() && (#[trigger] slots.update(i,None)[j]).is_some() implies slots.update(i,None)[j].unwrap().valid() by {assert(j!=i);}
    let inverse=slots[i].unwrap();let remaining=slots.update(i,None);let restored=inverse.undo(heap).unwrap();
    assert forall|j:int|0<=j<slots.len() implies (#[trigger] remaining[j])!=slots[i] by {
        if remaining[j]==slots[i] {depth_bound(remaining,restored,j);assert(inverse.valid());}
    }
}
pub proof fn empty<T:?Sized>(slots:Seq<Option<Inverse<T>>>,heap:Map<Address,Value<T>>)
    requires forall|i:int|0<=i<slots.len() ==> (#[trigger] slots[i]).is_none(),
    ensures recover(slots,heap)==Some(heap),
    decreases slots.len(),
{if slots.len()>0 {empty(slots.drop_last(),heap);}}
}
