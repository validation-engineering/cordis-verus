//! Definedness of the real mixed inverse word from its recorded source inputs.
use super::Report;
#[cfg(verus_keep_ghost)]
use super::{gap, Step};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    managed::{semantics as s, semantics::Value, trace, Owner},
    service_composition::Address,
};
use vstd::prelude::*;

verus! {
pub open spec fn adjacent<T:?Sized>(steps:Seq<Step<T>>,i:int,j:int)->bool {
    0<=i<j<steps.len() && steps[i].address()==steps[j].address()
        && forall|k:int| i<k<j ==> (#[trigger] steps[k]).address()!=steps[i].address()
}
pub open spec fn admissible<T:?Sized>(steps:Seq<Step<T>>)->bool {
    forall|i:int,j:int| #[trigger] adjacent(steps,i,j) ==> gap(steps[i],steps[j])
}
pub open spec fn composing<T:?Sized>(steps:Seq<Step<T>>)->bool {
    forall|i:int,j:int| #[trigger] adjacent(steps,i,j) ==> steps[i].after()==steps[j].before()
}
pub open spec fn first<T:?Sized>(steps:Seq<Step<T>>,i:int)->bool {
    0<=i<steps.len() && forall|j:int|0<=j<i ==> (#[trigger] steps[j]).address()!=steps[i].address()
}
pub open spec fn inputs<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>)->bool {
    forall|i:int| #[trigger] first(steps,i) ==> heap.contains_pair(steps[i].address(),steps[i].before())
}
/// Per-allocation first observations, captured by actual successful calls.
/// They are not claimed to be one simultaneous cross-Journal snapshot.
pub open spec fn initial<T:?Sized>(steps:Seq<Step<T>>)->Map<Address,Value<T>>
    decreases steps.len(),
{
    if steps.len()==0 {Map::empty()} else {
        let prefix=initial(steps.drop_last());let step=steps.last();
        if prefix.contains_key(step.address()) {prefix} else {prefix.insert(step.address(),step.before())}
    }
}
pub open spec fn landed<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>)->Map<Address,Value<T>>
    decreases steps.len(),
{
    if steps.len()==0 {heap} else {landed(steps.drop_last(),heap).insert(steps.last().address(),steps.last().after())}
}
pub proof fn initial_inputs<T:?Sized>(steps:Seq<Step<T>>)
    ensures inputs(steps,initial(steps)),
        forall|key:Address| #[trigger] initial(steps).contains_key(key) <==> exists|i:int|0<=i<steps.len() && (#[trigger] steps[i]).address()==key,
    decreases steps.len(),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    if steps.len()>0 {
        let prefix=steps.drop_last();initial_inputs(prefix);
        assert forall|key:Address| #[trigger] initial(steps).contains_key(key) <==> exists|i:int|0<=i<steps.len() && (#[trigger] steps[i]).address()==key by {
            if exists|i:int|0<=i<steps.len() && (#[trigger] steps[i]).address()==key {
                let i=choose|i:int|0<=i<steps.len() && (#[trigger] steps[i]).address()==key;
                if i<prefix.len() {assert(prefix[i].address()==key);}else {assert(steps.last().address()==key);}
            }
        }
        assert forall|i:int| #[trigger] first(steps,i) implies initial(steps).contains_pair(steps[i].address(),steps[i].before()) by {
            if i<prefix.len() {assert(forall|j:int|0<=j<i ==> (#[trigger] prefix[j]).address()!=prefix[i].address());assert(first(prefix,i));assert(inputs(prefix,initial(prefix)));assert(initial(prefix).contains_pair(steps[i].address(),steps[i].before()));}
            else {assert(!initial(prefix).contains_key(steps[i].address()));}
        }
    }
}
pub proof fn untouched<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>,key:Address)
    requires forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).address()!=key,
    ensures landed(steps,heap).contains_key(key)==heap.contains_key(key),heap.contains_key(key) ==> landed(steps,heap)[key]==heap[key],
    decreases steps.len(),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    if steps.len()>0 {assert(steps.last().address()!=key);untouched(steps.drop_last(),heap,key);}
}
pub(crate) proof fn last_writer<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>,key:Address)->(i:int)
    requires exists|i:int|0<=i<steps.len() && (#[trigger] steps[i]).address()==key,
    ensures 0<=i<steps.len(),steps[i].address()==key,
        forall|j:int|i<j<steps.len() ==> (#[trigger] steps[j]).address()!=key,
        landed(steps,heap).contains_pair(key,steps[i].after()),
    decreases steps.len(),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    if steps.last().address()==key {steps.len()-1} else {
        let prior=steps.drop_last();
        let found=choose|i:int|0<=i<steps.len() && (#[trigger] steps[i]).address()==key;
        assert(found<prior.len());assert(prior[found].address()==key);
        let i=last_writer(prior,heap,key);
        assert forall|j:int|i<j<steps.len() implies (#[trigger] steps[j]).address()!=key by {
            if j<prior.len() {assert(prior[j].address()!=key);}
        }
        i
    }
}
/// No inverse success or replay success is a premise. They follow from the
/// actual first inputs and the established adjacent same-allocation links.
proof fn prefix_conditions<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>)
    requires steps.len()>0,composing(steps),inputs(steps,heap),
    ensures composing(steps.drop_last()),inputs(steps.drop_last(),heap),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    let prefix=steps.drop_last();
    assert forall|i:int,j:int| #[trigger] adjacent(prefix,i,j) implies prefix[i].after()==prefix[j].before() by {
        assert(0<=i<j<prefix.len());
        assert forall|k:int|i<k<j implies (#[trigger] steps[k]).address()!=steps[i].address() by {assert(prefix[k].address()!=prefix[i].address());}
        assert(adjacent(steps,i,j));
    }
    assert forall|i:int| #[trigger] first(prefix,i) implies heap.contains_pair(prefix[i].address(),prefix[i].before()) by {
        assert forall|j:int|0<=j<i implies (#[trigger] steps[j]).address()!=steps[i].address() by {assert(prefix[j].address()!=prefix[i].address());}
        assert(first(steps,i));
    }
}
proof fn next_domain<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>)
    requires steps.len()>0,composing(steps),inputs(steps,heap),
    ensures landed(steps.drop_last(),heap).contains_pair(steps.last().address(),steps.last().before()),
{
    hide(Step::address);hide(Step::before);hide(Step::after);
    let prefix=steps.drop_last();let step=steps.last();let last=steps.len()-1;
    if exists|i:int|0<=i<prefix.len() && (#[trigger] prefix[i]).address()==step.address() {
        let i=last_writer(prefix,heap,step.address());assert(0<=i<prefix.len());
        assert forall|k:int| i<k<last implies (#[trigger] steps[k]).address()!=steps[i].address() by {
            assert(prefix[k].address()!=step.address());
        }
        assert(adjacent(steps,i,last));
    } else {
        untouched(prefix,heap,step.address());
        assert forall|j:int|0<=j<last implies (#[trigger] steps[j]).address()!=steps[last].address() by {
            assert(prefix[j]==steps[j]);
            assert(prefix[j].address()!=step.address());
        }
        assert(first(steps,last));assert(heap.contains_pair(step.address(),step.before()));
    }
}
proof fn replay_defined<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>)
    requires composing(steps),inputs(steps,heap),
    ensures s::replay(steps,heap)==Some(landed(steps,heap)),
    decreases steps.len(),
{
    hide(composing);hide(inputs);hide(Step::address);hide(Step::before);hide(Step::after);
    if steps.len()>0 {
        prefix_conditions(steps,heap);replay_defined(steps.drop_last(),heap);next_domain(steps,heap);
    }
}
pub proof fn defined<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>)
    requires composing(steps),inputs(steps,heap),
    ensures s::replay(steps,heap)==Some(landed(steps,heap)),s::undo(steps,landed(steps,heap))==Some(heap),
{replay_defined(steps,heap);s::roundtrip(steps,heap);}
impl<T:?Sized> Report<T> {
    /// The condition is inspected on authentic frame gaps, never supplied as
    /// a commutation law or an assertion that this inverse word is defined.
    pub proof fn recovery_word(&self)
        requires self.recovery_history(),admissible(self.steps@),
        ensures s::replay(self.steps@,initial(self.steps@))==Some(landed(self.steps@,initial(self.steps@))),
            s::undo(self.steps@,landed(self.steps@,initial(self.steps@)))==Some(initial(self.steps@)),
    {
        reveal(Report::recovery_history);
        assert(composing(self.steps@)) by {
            assert forall|i:int,j:int| #[trigger] adjacent(self.steps@,i,j) implies self.steps@[i].after()==self.steps@[j].before() by {
                assert(gap(self.steps@[i],self.steps@[j]));
            }
        }
        initial_inputs(self.steps@);defined(self.steps@,initial(self.steps@));
    }
    /// The suffix belongs to this actual execution owner, including a failed
    /// function's retained prefix. Aliases share one restored allocation.
    pub proof fn recover_retained<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat)
        requires self.recovery_history(),admissible(self.steps@),self.queue_semantics(owner,id,offset),
        ensures trace::queued_undo(owner.cleanup_state().queues()[id].slots().subrange(offset as int,owner.cleanup_state().queues()[id].slots().len() as int),landed(self.steps@,initial(self.steps@)))==Some(initial(self.steps@)),
    {self.recovery_word();}
    pub proof fn recovered_aliases<K>(&self,targets:Map<K,Address>)
        requires self.recovery_history(),admissible(self.steps@),
        ensures s::undo(self.steps@,landed(self.steps@,initial(self.steps@))).is_some(),
            s::view(targets,s::undo(self.steps@,landed(self.steps@,initial(self.steps@))).unwrap())==s::view(targets,initial(self.steps@)),
    {self.recovery_word();}
}
}
