//! Persistent source-to-target registration identities. Episode restart changes
//! tickets, not fiber identity. Admission of a conflicting binding is explicit.
use crate::reversible_value::joint;
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[allow(dead_code)] // Actual source/target call receipts erase with the proof.
struct Entry {source:usize,target:usize,source_cut:Ghost<joint::Receipt>,target_cut:Ghost<joint::Receipt>}
pub(crate) open spec fn call(cut:joint::Receipt,id:usize)->bool {
    cut.wf() && cut.event().change is Recipes && cut.event().change->Recipes_event is Call
        && cut.event().change->Recipes_event.actor()==id
}
pub(crate) struct Fibers {entries:Vec<Entry>}
impl Fibers {
    pub(crate) closed spec fn mapping(&self)->Map<usize,usize> {
        Map::new(self.entries@.map(|_:int,e:Entry|e.source).to_set(),
            |id:usize|self.entries@[choose|i:int|0<=i<self.entries.len() && (#[trigger] self.entries@[i]).source==id].target)
    }
    pub(crate) closed spec fn wf(&self)->bool {
        (forall|i:int|0<=i<self.entries.len() ==> call((#[trigger] self.entries@[i]).source_cut@,self.entries@[i].source) && call(self.entries@[i].target_cut@,self.entries@[i].target))
            && (forall|i:int,j:int|0<=i<j<self.entries.len() ==> (#[trigger] self.entries@[i]).source!=(#[trigger] self.entries@[j]).source
            && self.entries@[i].target!=self.entries@[j].target)
    }
    pub(crate) fn new()->(out:Self) ensures out.wf(),out.mapping()==Map::empty(), {Self {entries:Vec::new()}}
    proof fn at(&self,i:int)
        requires self.wf(),0<=i<self.entries.len(),
        ensures self.mapping().contains_pair(self.entries@[i].source,self.entries@[i].target),
    {
        let id=self.entries@[i].source;
        let keys=self.entries@.map(|_:int,e:Entry|e.source);
        assert(keys[i]==id);assert(keys.contains(id));keys.to_set_ensures();
        assert(self.mapping().contains_key(id));
        let j=choose|j:int|0<=j<self.entries.len() && (#[trigger] self.entries@[j]).source==id;
        if i<j {assert(self.entries@[i].source!=self.entries@[j].source);}
        if j<i {assert(self.entries@[j].source!=self.entries@[i].source);}
    }
    pub(crate) proof fn injective(&self)
        requires self.wf(),
        ensures forall|a:usize,b:usize|self.mapping().contains_key(a) && self.mapping().contains_key(b) && #[trigger] self.mapping()[a]==#[trigger] self.mapping()[b] ==> a==b,
    {
        assert forall|a:usize,b:usize|self.mapping().contains_key(a) && self.mapping().contains_key(b) && #[trigger] self.mapping()[a]==#[trigger] self.mapping()[b] implies a==b by {
            let i=choose|i:int|0<=i<self.entries.len() && (#[trigger] self.entries@[i]).source==a;
            let j=choose|j:int|0<=j<self.entries.len() && (#[trigger] self.entries@[j]).source==b;
            self.at(i);self.at(j);
            if i<j {assert(self.entries@[i].target!=self.entries@[j].target);}
            if j<i {assert(self.entries@[j].target!=self.entries@[i].target);}
        }
    }
    pub(crate) fn get(&self,source:usize)->(out:Option<usize>)
        requires self.wf(),ensures out.is_some()==self.mapping().contains_key(source),out.is_some() ==> self.mapping().contains_pair(source,out.unwrap()),
    {
        let mut i=0;
        while i<self.entries.len()
            invariant self.wf(),i<=self.entries.len(),forall|j:int|0<=j<i ==> self.entries@[j].source!=source,
            decreases self.entries.len()-i,
        {if self.entries[i].source==source {proof {self.at(i as int);}return Some(self.entries[i].target);}i+=1;}None
    }
    pub(crate) fn bind(&mut self,source:usize,target:usize,Ghost(source_cut):Ghost<joint::Receipt>,Ghost(target_cut):Ghost<joint::Receipt>)->(out:bool)
        requires old(self).wf(),call(source_cut,source),call(target_cut,target),
        ensures final(self).wf(),old(self).mapping().submap_of(final(self).mapping()),
            out ==> final(self).mapping().contains_pair(source,target),!out ==> *final(self)==*old(self),
    {
        let mut i=0;
        while i<self.entries.len()
            invariant *self==*old(self),self.wf(),i<=self.entries.len(),
                forall|j:int|0<=j<i ==> self.entries@[j].source!=source && self.entries@[j].target!=target,
            decreases self.entries.len()-i,
        {
            if self.entries[i].source==source {proof {self.at(i as int);}return self.entries[i].target==target;}
            if self.entries[i].target==target {return false;}i+=1;
        }
        let ghost prior=*self;self.entries.push(Entry {source,target,source_cut:Ghost(source_cut),target_cut:Ghost(target_cut)});
        proof {
            assert(self.wf());self.at(i as int);
            assert forall|id:usize|prior.mapping().contains_key(id) implies self.mapping().contains_pair(id,prior.mapping()[id]) by {
                let j=choose|j:int|0<=j<prior.entries.len() && (#[trigger] prior.entries@[j]).source==id;
                prior.at(j);self.at(j);
            }
            reveal(Map::submap_of);
        }true
    }
}
}
