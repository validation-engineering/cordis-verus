//! Capture the entire original inverse word from a production recorded owner.
use crate::lifecycle_state::registration::shared_child::SharedChild;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed;
use crate::reversible_value::managed::{replay::session::CallOwner, Step};
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
/// This real read accepts only a complete, still-retained root group. There is
/// no supplied success word, callback law or invented expected heap.
pub(crate) fn root<T:?Sized>(owner:&CallOwner<T>,len:usize,Ghost(steps):Ghost<Seq<Step<T>>>,Ghost(offset):Ghost<nat>)->(out:bool)
    requires owner.wf(),len==steps.len(),managed::retained(steps,owner.baseline(),0,offset),
    ensures out ==> owner.conserved() && owner.histories().dom()==set![0usize]
        && super::word(owner.histories()[0].initial(),steps,Seq::empty()),
{
    proof {owner.facts();}
    let groups=owner.execution().groups();
    if groups.allocated_groups()!=1 {return false;}
    let queue=match groups.get(0) {Some(q)=>q,None=>return false};
    if queue.retained_len()!=len {return false;}
    let mut i=0;
    while i<len
        invariant i<=len,queue.slots().len()==len,forall|j:int|0<=j<i ==> queue.slots()[j].is_some(),
        decreases len-i,
    {if queue.retained(i).is_none() {return false;}i+=1;}
    proof {
        let baseline=owner.baseline().cleanup_state().queues()[0];
        assert(owner.histories().contains_key(0));assert(owner.entry(0));assert(owner.origins()[0]==baseline);
        assert(owner.histories()[0].starts_with(baseline.slots()));
        assert(owner.histories()[0].initial().len()==queue.slots().len());assert(baseline.slots().len()==offset+steps.len());
        assert(offset==0);assert(owner.histories()[0].initial() =~= baseline.slots());assert(owner.histories().dom() =~= set![0usize]);
        assert(super::word(owner.histories()[0].initial(),steps,Seq::empty()));
        assert forall|id:usize,j:int|owner.histories().contains_key(id)
            && 0<=j<owner.histories()[id].current().len() && (#[trigger] owner.histories()[id].current()[j]).is_some() implies
                j<owner.histories()[id].initial().len() && owner.histories()[id].current()[j]==owner.histories()[id].initial()[j] by {
            assert(id==0);assert(steps[j].in_slot(owner.histories()[0].initial()[j]));
            assert(crate::cleanup_groups::payload::recovery::managed(owner.histories()[0].initial()[j].unwrap()));
            owner.histories()[0].conservation(j);
        }
    }true
}
#[allow(dead_code)]
pub struct Word<T:?Sized> {children:Vec<SharedChild>,root:Ghost<Seq<Step<T>>>,owner:Ghost<CallOwner<T>>}
impl<T:?Sized> Word<T> {
    pub closed spec fn root(&self)->Seq<Step<T>> {self.root@}
    pub closed spec fn children(&self)->Seq<SharedChild> {self.children@}
    pub closed spec fn owner(&self)->CallOwner<T> {self.owner@}
    pub open spec fn wf(&self)->bool {
        self.owner().wf() && self.owner().histories().dom()==set![0usize]
            && super::word(self.owner().histories()[0].initial(),self.root(),self.children())
            && forall|i:int|0<=i<self.children().len() ==> (#[trigger] self.children()[i]).wf()
                && self.owner().baseline().origin().is_some()
                && self.children()[i].domain_id()==self.owner().baseline().origin().unwrap().domain
                && self.children()[i].owner()==self.owner().baseline().origin().unwrap().id
                && self.children()[i].episode()==Some(self.owner().baseline().origin().unwrap().generation)
    }
    pub(crate) fn capture(_owner:&CallOwner<T>,children:&[SharedChild],Ghost(root):Ghost<Seq<Step<T>>>)->(out:Self)
        requires _owner.wf(),_owner.histories().dom()==set![0usize],super::word(_owner.histories()[0].initial(),root,children@),
            forall|i:int|0<=i<children.len() ==> (#[trigger] children@[i]).wf()
                && _owner.baseline().origin().is_some()
                && children@[i].domain_id()==_owner.baseline().origin().unwrap().domain
                && children@[i].owner()==_owner.baseline().origin().unwrap().id
                && children@[i].episode()==Some(_owner.baseline().origin().unwrap().generation),
        ensures out.wf(),out.root()==root,out.children()==children@,out.owner()==*_owner,
    {
        let mut saved=Vec::new();let mut i=0;
        while i<children.len() invariant i<=children.len(),saved@==children@.take(i as int),decreases children.len()-i,
        {saved.push(children[i].clone());i+=1;}
        proof {assert(saved@ =~= children@);}
        Self {children:saved,root:Ghost(root),owner:Ghost(*_owner)}
    }
}
}
