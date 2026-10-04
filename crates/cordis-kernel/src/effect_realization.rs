//! Definition 23's two realizations in one location-based abstract heap.
//!
//! Aliases are locations, not copied values. Derived cleanup is a separate
//! scope operation: its returned value inverse is identity, whereas discarding
//! the child returns the retained parent. No arbitrary Rust callback or memory
//! allocator implementation is assumed verified by this mathematical model.
use crate::contexts as c;
use vstd::prelude::*;

verus! {

pub type Effect<S> = spec_fn(S)->Option<c::PartialYield<S>>;
pub type Heap<S> = Map<nat,S>;

#[verifier::reject_recursive_types(S)]
pub enum Receipt<S> {
    InPlace {location:nat, inverse:spec_fn(S)->Option<S>},
    Derived {parent:nat, child:nat},
}
#[verifier::reject_recursive_types(S)]
pub struct Landing<S> {
    pub heap:Heap<S>,
    pub context:nat,
    pub receipt:Receipt<S>,
}

pub open spec fn read<S>(heap:Heap<S>,location:nat)->Option<S> {
    if heap.dom().contains(location) {Some(heap[location])} else {None}
}
pub open spec fn witnessed<S>(effect:Effect<S>)->bool {
    forall|input:S| #[trigger] effect(input).is_some() ==>
        (effect(input).unwrap().undo)(effect(input).unwrap().state)==Some(input)
}
pub open spec fn in_place<S>(effect:Effect<S>,heap:Heap<S>,location:nat)->Option<Landing<S>> {
    if !heap.dom().contains(location) || effect(heap[location]).is_none() {None} else {
        let y=effect(heap[location]).unwrap();
        Some(Landing {heap:heap.insert(location,y.state),context:location,
            receipt:Receipt::InPlace {location,inverse:y.undo}})
    }
}
pub open spec fn derived<S>(effect:Effect<S>,heap:Heap<S>,parent:nat,child:nat)->Option<Landing<S>> {
    if !heap.dom().contains(parent) || heap.dom().contains(child) || effect(heap[parent]).is_none() {None} else {
        let y=effect(heap[parent]).unwrap();
        Some(Landing {heap:heap.insert(child,y.state),context:child,
            receipt:Receipt::Derived {parent,child}})
    }
}

/// The inverse returned by the value-level operation, excluding scope cleanup.
pub open spec fn returned_inverse<S>(receipt:Receipt<S>)->spec_fn(S)->Option<S> {
    match receipt {Receipt::InPlace {inverse,..}=>inverse,Receipt::Derived {..}=>|s:S|Some(s)}
}

/// Actual realization recovery also returns the context to use afterwards.
/// The derived branch removes only the child. It never invokes the original
/// effect's value inverse on the retained parent or silently changes that value.
pub open spec fn recover<S>(heap:Heap<S>,receipt:Receipt<S>)->Option<(Heap<S>,nat)> {
    match receipt {
        Receipt::InPlace {location,inverse}=>{
            if !heap.dom().contains(location) || inverse(heap[location]).is_none() {None} else {
                Some((heap.insert(location,inverse(heap[location]).unwrap()),location))
            }
        },
        Receipt::Derived {parent,child}=>{
            if parent==child || !heap.dom().contains(parent) || !heap.dom().contains(child) {None} else {
                Some((heap.remove(child),parent))
            }
        },
    }
}

pub proof fn in_place_realizes<S>(effect:Effect<S>,heap:Heap<S>,location:nat)
    requires heap.dom().contains(location),witnessed(effect),effect(heap[location]).is_some(),
    ensures {
        let result=in_place(effect,heap,location);let landed=result.unwrap();let y=effect(heap[location]).unwrap();
        &&& result.is_some() && landed.context==location
        &&& read(landed.heap,landed.context)==Some(y.state)
        &&& returned_inverse(landed.receipt)==y.undo
        &&& recover(landed.heap,landed.receipt)==Some((heap,location))
        &&& landed.heap.dom()==heap.dom()
        &&& forall|other:nat| other!=location ==> read(landed.heap,other)==read(heap,other)
    },
{
    let y=effect(heap[location]).unwrap();assert((y.undo)(y.state)==Some(heap[location]));
    assert(heap.insert(location,y.state).insert(location,heap[location]) =~= heap);
    assert(heap.insert(location,y.state).dom() =~= heap.dom());
}

pub proof fn derived_realizes<S>(effect:Effect<S>,heap:Heap<S>,parent:nat,child:nat)
    requires heap.dom().contains(parent),!heap.dom().contains(child),effect(heap[parent]).is_some(),
    ensures {
        let result=derived(effect,heap,parent,child);let landed=result.unwrap();let y=effect(heap[parent]).unwrap();
        &&& result.is_some() && landed.context==child && child!=parent
        &&& read(landed.heap,landed.context)==Some(y.state)
        &&& landed.receipt==Receipt::<S>::Derived {parent,child}
        &&& forall|value:S| #[trigger] returned_inverse(landed.receipt)(value)==Some(value)
        &&& recover(landed.heap,landed.receipt)==Some((heap,parent))
        &&& forall|existing:nat| heap.dom().contains(existing) ==> read(landed.heap,existing)==read(heap,existing)
    },
{
    assert(parent!=child);assert(heap.insert(child,effect(heap[parent]).unwrap().state).remove(child) =~= heap);
}

/// Both realizations implement the same forward value and return to the same
/// input observation. This is not an equation between their inverse functions.
pub proof fn same_denotation<S>(effect:Effect<S>,heap:Heap<S>,parent:nat,child:nat)
    requires heap.dom().contains(parent),!heap.dom().contains(child),witnessed(effect),effect(heap[parent]).is_some(),
    ensures {
        let inplace=in_place(effect,heap,parent).unwrap();let fresh=derived(effect,heap,parent,child).unwrap();
        &&& read(inplace.heap,inplace.context)==read(fresh.heap,fresh.context)
        &&& recover(inplace.heap,inplace.receipt)==recover(fresh.heap,fresh.receipt)
        &&& inplace.context==parent && fresh.context!=parent
        &&& read(fresh.heap,parent)==read(heap,parent)
    },
{
    in_place_realizes(effect,heap,parent);derived_realizes(effect,heap,parent,child);
}

/// A scope's later private changes do not turn identity into an undo map.
/// Discard removes them; every pre-existing alias still names its old cell.
pub proof fn derived_discard_after_edit<S>(effect:Effect<S>,heap:Heap<S>,parent:nat,child:nat,edited:S)
    requires heap.dom().contains(parent),!heap.dom().contains(child),effect(heap[parent]).is_some(),
    ensures {
        let landed=derived(effect,heap,parent,child).unwrap();let changed=landed.heap.insert(child,edited);
        &&& returned_inverse(landed.receipt)(edited)==Some(edited)
        &&& recover(changed,landed.receipt)==Some((heap,parent))
        &&& forall|existing:nat| heap.dom().contains(existing) ==> read(changed,existing)==read(heap,existing)
    },
{
    derived_realizes(effect,heap,parent,child);assert(heap.insert(child,effect(heap[parent]).unwrap().state).insert(child,edited).remove(child) =~= heap);
}

/// Freshness is required by the abstract allocation operation itself, not by
/// an assumed success of a subsequent recovery.
pub proof fn existing_child_rejected<S>(effect:Effect<S>,heap:Heap<S>,parent:nat,child:nat)
    requires heap.dom().contains(child),
    ensures derived(effect,heap,parent,child).is_none(),
{}

pub open spec fn increment()->Effect<int> {
    |value:int|Some(c::PartialYield {state:value+1,undo:|after:int|Some(after-1)})
}
pub proof fn nontrivial_alias_example()
    ensures {
        let effect=increment();let heap=Map::empty().insert(0nat,10int);
        let inplace=in_place(effect,heap,0).unwrap();let fresh=derived(effect,heap,0,1).unwrap();
        &&& witnessed(effect)
        &&& read(inplace.heap,0)==Some(11int) && read(fresh.heap,0)==Some(10int)
        &&& read(inplace.heap,inplace.context)==Some(11int) && read(fresh.heap,fresh.context)==Some(11int)
        &&& returned_inverse(inplace.receipt)(11int)==Some(10int)
        &&& returned_inverse(fresh.receipt)(11int)==Some(11int)
        &&& returned_inverse(inplace.receipt)!=returned_inverse(fresh.receipt)
        &&& recover(inplace.heap,inplace.receipt)==Some((heap,0nat))
        &&& recover(fresh.heap.insert(1nat,99int),fresh.receipt)==Some((heap,0nat))
    },
{
    let effect=increment();let heap=Map::empty().insert(0nat,10int);
    assert(witnessed(effect));same_denotation(effect,heap,0,1);derived_discard_after_edit(effect,heap,0,1,99);
}

} // verus!
