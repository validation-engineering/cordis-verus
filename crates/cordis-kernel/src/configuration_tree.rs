//! Production configuration nodes: immutable recipes, ordered parents and
//! actual mount results. String-index caches are validated against these nodes.
//! Only the actual mounting callback can replace a stored runtime identity.
use crate::configuration_runtime::Allocation;
use std::ops::Deref;
use std::sync::Arc;
use vstd::prelude::*;
#[path = "configuration_identity.rs"]
pub mod identity;
use identity::Origin;
#[path = "configuration_reconstruction.rs"]
pub mod reconstruction;
#[path = "configuration_selection.rs"]
pub mod selection;

verus! {
#[verifier::opaque]
pub open spec fn invoked<T,E,F:FnOnce(&T,Option<usize>)->Result<Allocation,E>>(callback:F,data:T,parent:Option<usize>,result:Result<Allocation,E>)->bool {
    exists|input:&T| *input==data && callback.ensures((input,parent),result)
}
fn invoke<T,E,F:FnOnce(&T,Option<usize>)->Result<Allocation,E>>(data:&T,parent:Option<usize>,callback:F)->(out:Result<Allocation,E>)
    requires callback.requires((data,parent)),ensures invoked::<T,E,F>(callback,*data,parent,out),
{let result=callback(data,parent);proof {reveal(invoked);}result}
#[allow(dead_code)]
pub struct Node<T> {origin:Ghost<Option<Origin>>,key:String,parent:Option<usize>,enabled:bool,allocation:Option<Allocation>,data:Arc<T>}
impl<T> Node<T> {
    pub closed spec fn source(&self)->Option<Origin> {self.origin@}
    pub closed spec fn name(&self)->Seq<char> {self.key@}
    pub closed spec fn parent_index(&self)->Option<usize> {self.parent}
    pub closed spec fn enabled_spec(&self)->bool {self.enabled}
    pub closed spec fn allocation_spec(&self)->Option<Allocation> {self.allocation}
    pub closed spec fn identity(&self)->Option<usize> {match self.allocation_spec() {Some(a)=>Some(a.owner()),None=>None}}
    pub closed spec fn payload(&self)->T {*self.data}
    pub fn key(&self)->(out:&String) ensures out@==self.name(), {&self.key}
    pub fn id(&self)->(out:Option<usize>) ensures out==self.identity(), {self.allocation.as_ref().map(|a:&Allocation| -> (out:usize) ensures out==a.owner(), {a.id()})}
    pub fn allocation(&self)->(out:Option<Allocation>) ensures out==self.allocation_spec(), {self.allocation.clone()}
    pub fn enabled(&self)->(out:bool) ensures out==self.enabled_spec(), {self.enabled}
}
impl<T> Deref for Node<T> {
    type Target=T;
    fn deref(&self)->(out:&T) ensures *out==self.payload(), {&self.data}
}
impl<T> Clone for Node<T> {
    fn clone(&self)->(out:Self) ensures out==*self,
    {Self {origin:Ghost(self.origin@),key:self.key.clone(),parent:self.parent,enabled:self.enabled,allocation:self.allocation.clone(),data:self.data.clone()}}
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum TreeError {DuplicateIdentity,InvalidId,StaleEntry,Duplicate,MissingParent,DisabledParent,DisabledIdentity,Unknown,Disabled}
pub enum MountError<E> {Tree(TreeError),Callback(E),Mismatch(Allocation)}
pub struct Tree<T> {domain:u64,root:Option<usize>,nodes:Vec<Node<T>>}
impl<T> Tree<T> {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn root_id(&self)->Option<usize> {self.root}
    pub closed spec fn view(&self)->Seq<Node<T>> {self.nodes@}
    pub open spec fn wf(&self)->bool {
        &&& forall|i:int,j:int| 0<=i<j<self@.len() ==> (#[trigger] self@[i]).name()!=(#[trigger] self@[j]).name()
        &&& forall|i:int,j:int|0<=i<j<self@.len() && self@[i].identity().is_some() ==> self@[i].identity()!=self@[j].identity()
        &&& forall|i:int| 0<=i<self@.len() ==> {
            let node=#[trigger] self@[i];
            &&& node.source().is_some() ==> identity::valid_local(node.source().unwrap().local)
                && node.name()==identity::qualify(self.parent_name(node.parent_index()),node.source().unwrap().local)
                && node.enabled_spec()==self.effective(node.parent_index(),node.source().unwrap().enabled)
            &&& !node.enabled_spec() ==> node.identity().is_none()
            &&& node.allocation_spec().is_some() ==> node.allocation_spec().unwrap().wf()
                && node.allocation_spec().unwrap().domain_id()==self.domain_id()
            &&& node.parent_index().is_some() ==> node.parent_index().unwrap()<i
                && (node.enabled_spec() ==> self@[node.parent_index().unwrap() as int].enabled_spec())
        }
    }
    pub fn new(domain:u64,root:Option<usize>)->(out:Self)
        ensures out.wf(),out@==Seq::<Node<T>>::empty(),out.domain_id()==domain,out.root_id()==root,
    {Self {domain,root,nodes:Vec::new()}}
    pub fn nodes(&self)->(out:&Vec<Node<T>>) ensures out@==self@, {&self.nodes}
    /// A corrupt or stale external index cannot select another named entry.
    pub fn get(&self,index:usize,key:&str)->(out:Option<&Node<T>>)
        ensures out.is_some()==(index<self@.len() && self@[index as int].name()==key@),
            out.is_some() ==> *out.unwrap()==self@[index as int],
    {
        match self.nodes.get(index) {Some(node)=>if node.key.as_str()==key {Some(node)} else {None},None=>None}
    }
    pub fn insert(&mut self,key:String,parent:Option<usize>,enabled:bool,allocation:Option<Allocation>,data:T)->(out:Result<usize,TreeError>)
        requires old(self).wf(),allocation.is_some() ==> allocation.unwrap().wf(),
        ensures final(self).wf(),final(self).domain_id()==old(self).domain_id(),final(self).root_id()==old(self).root_id(),out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> out->Ok_0==old(self)@.len() && final(self)@.len()==old(self)@.len()+1
                && final(self)@.take(old(self)@.len() as int)==old(self)@
                && final(self)@.last().name()==key@ && final(self)@.last().parent_index()==parent
                && final(self)@.last().allocation_spec()==allocation && final(self)@.last().enabled_spec()==enabled
                && final(self)@.last().payload()==data,
    {
        let mut n=0;
        while n<self.nodes.len()
            invariant *self==*old(self),self.wf(),n<=self.nodes.len(),forall|i:int| 0<=i<n ==> (#[trigger] self@[i]).name()!=key@,
            decreases self.nodes.len()-n,
        {if self.nodes[n].key==key {return Err(TreeError::Duplicate);} n+=1;}
        if !enabled && allocation.is_some() {return Err(TreeError::DisabledIdentity);}
        if let Some(p)=parent {
            if p>=self.nodes.len() {return Err(TreeError::MissingParent);}
            if enabled && !self.nodes[p].enabled {return Err(TreeError::DisabledParent);}
        }
        if let Some(a)=&allocation {
            let mut j=0;
            while j<self.nodes.len()
                invariant self.wf(),j<=self.nodes.len(),forall|i:int|0<=i<j ==> self@[i].identity()!=Some(a.owner()),
                decreases self.nodes.len()-j,
            {if self.nodes[j].id()==Some(a.id()) {return Err(TreeError::DuplicateIdentity);}j+=1;}
        }
        let parent_id=match parent {Some(p)=>self.nodes[p].id(),None=>self.root};
        if let Some(a)=&allocation {
            if a.domain()!=self.domain || a.parent()!=parent_id || (parent.is_some() && parent_id.is_none()) {return Err(TreeError::MissingParent);}
        }
        let ghost before=self@;
        let index=self.nodes.len();
        self.nodes.push(Node {origin:Ghost(None),key,parent,enabled,allocation,data:Arc::new(data)});
        assert(self@.take(before.len() as int)==before);
        Ok(index)
    }
    pub open spec fn parent_for(&self,index:usize,root:Option<usize>)->Option<usize> {
        let parent=self@[index as int].parent_index();
        if parent.is_none() {root} else {self@[parent.unwrap() as int].identity()}
    }
    /// Missing parents are rejected, never replaced by the supplied root.
    pub fn mount<E,F:FnOnce(&T,Option<usize>)->Result<Allocation,E>>(&mut self,index:usize,key:&str,callback:F)
        ->(out:Result<usize,MountError<E>>)
        requires old(self).wf(),forall|data:&T,parent:Option<usize>| callback.requires((data,parent)),
            forall|data:&T,parent:Option<usize>,result:Result<Allocation,E>| callback.ensures((data,parent),result) && result.is_ok() ==> result->Ok_0.wf(),
        ensures final(self).wf(),final(self).domain_id()==old(self).domain_id(),final(self).root_id()==old(self).root_id(),final(self)@.len()==old(self)@.len(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> index<old(self)@.len() && old(self)@[index as int].name()==key@,
            out.is_ok() ==> final(self)@==old(self)@.update(index as int,final(self)@[index as int]),
            out.is_ok() ==> final(self)@[index as int].identity()==Some(out->Ok_0),
            out.is_ok() ==> final(self)@[index as int].source()==old(self)@[index as int].source(),
            out.is_ok() ==> final(self)@[index as int].payload()==old(self)@[index as int].payload(),
            out.is_ok() ==> final(self)@[index as int].name()==old(self)@[index as int].name(),
            out.is_ok() ==> final(self)@[index as int].parent_index()==old(self)@[index as int].parent_index(),
            out.is_ok() ==> final(self)@[index as int].enabled_spec()==old(self)@[index as int].enabled_spec(),
            out.is_ok() ==> final(self)@[index as int].allocation_spec().is_some()
                && final(self)@[index as int].allocation_spec().unwrap().parent_id()==old(self).parent_for(index,old(self).root_id())
                && invoked::<T,E,F>(callback,old(self)@[index as int].payload(),old(self).parent_for(index,old(self).root_id()),Ok(final(self)@[index as int].allocation_spec().unwrap())),
    {
        let node=match self.get(index,key) {None=>return Err(MountError::Tree(TreeError::Unknown)),Some(node)=>node};
        if !node.enabled {return Err(MountError::Tree(TreeError::Disabled));}
        let parent=match node.parent {
            None=>self.root,
            Some(p)=>{let parent=self.nodes[p].id();
                if parent.is_none() {return Err(MountError::Tree(TreeError::MissingParent));} parent},
        };
        let data:&T=&node.data;
        let allocation=match invoke(data,parent,callback) {Ok(a)=>a,Err(error)=>return Err(MountError::Callback(error))};
        proof {reveal(invoked);}
        self.install(index,allocation)
    }
    fn parent_id_at(&self,index:usize)->(out:Option<usize>)
        requires index<self@.len(),self.wf(),
        ensures out==self.parent_for(index,self.root_id()),
    {match self.nodes[index].parent {Some(p)=>self.nodes[p].id(),None=>self.root}}
    pub open spec fn accepts_allocation(&self,index:usize,allocation:Allocation)->bool {
        allocation.domain_id()==self.domain_id() && allocation.parent_id()==self.parent_for(index,self.root_id())
            && forall|j:int|0<=j<self@.len() && j!=index ==> self@[j].identity()!=Some(allocation.owner())
    }
    fn install<E>(&mut self,index:usize,allocation:Allocation)->(out:Result<usize,MountError<E>>)
        requires old(self).wf(),index<old(self)@.len(),old(self)@[index as int].enabled_spec(),allocation.wf(),
        ensures final(self).wf(),final(self).domain_id()==old(self).domain_id(),final(self).root_id()==old(self).root_id(),
            out.is_ok()==old(self).accepts_allocation(index,allocation),
            out.is_err() ==> *final(self)==*old(self) && out==Err(MountError::Mismatch(allocation)),
            out.is_ok() ==> out->Ok_0==allocation.owner()
                && final(self)@==old(self)@.update(index as int,final(self)@[index as int])
                && final(self)@[index as int].allocation_spec()==Some(allocation)
                && final(self)@[index as int].source()==old(self)@[index as int].source()
                && final(self)@[index as int].payload()==old(self)@[index as int].payload()
                && final(self)@[index as int].name()==old(self)@[index as int].name()
                && final(self)@[index as int].parent_index()==old(self)@[index as int].parent_index()
                && final(self)@[index as int].enabled_spec()==old(self)@[index as int].enabled_spec(),
    {
        if allocation.domain()!=self.domain || allocation.parent()!=self.parent_id_at(index) {
            return Err(MountError::Mismatch(allocation));
        }
        let id=allocation.id();let mut j=0;
        while j<self.nodes.len()
            invariant *self==*old(self),self.wf(),j<=self.nodes.len(),id==allocation.owner(),
                allocation.domain_id()==self.domain_id(),allocation.parent_id()==self.parent_for(index,self.root_id()),
                forall|i:int|0<=i<j && i!=index ==> self@[i].identity()!=Some(id),
            decreases self.nodes.len()-j,
        {if j!=index && self.nodes[j].id()==Some(id) {
            assert(self@[j as int].identity()==Some(allocation.owner()));
            assert(!self.accepts_allocation(index,allocation));
            return Err(MountError::Mismatch(allocation));
        }j+=1;}
        let ghost before=self@;
        self.nodes[index].allocation=Some(allocation);
        assert(self@==before.update(index as int,self@[index as int]));
        Ok(id)
    }
    pub open spec fn complete(&self)->bool {
        forall|i:int| 0<=i<self@.len() && (#[trigger] self@[i]).enabled_spec() ==> self@[i].allocation_spec().is_some()
            && self@[i].allocation_spec().unwrap().parent_id()==self.parent_for(i as usize,self.root_id())
            && (self@[i].parent_index().is_some() ==> self.parent_for(i as usize,self.root_id()).is_some())
    }
    /// The actual group/child tree elaborates to distinct native Insert events,
    /// preserving each enabled entry's owner and current parent. This is an
    /// administrative extension, not an invented atomic callback/effect step.
    pub open spec fn elaborated(&self)->bool {
        forall|i:int|0<=i<self@.len() && (#[trigger] self@[i]).enabled_spec() ==> {
            let allocation=self@[i].allocation_spec().unwrap();
            &&& self@[i].allocation_spec().is_some() && allocation.wf()
            &&& allocation.parent_id()==self.parent_for(i as usize,self.root_id())
            &&& allocation.snapshot().events()[allocation.insertion() as int].event.change==
                (crate::reversible_value::joint::Change::Native {actor:allocation.owner(),rule:crate::refinement::Rule::Insert})
            &&& forall|j:int|0<=j<self@.len() && j!=i && self@[j].enabled_spec() ==> self@[j].identity()!=Some(allocation.owner())
        }
    }
    pub proof fn elaboration(&self)
        requires self.wf(),self.complete(),ensures self.elaborated(),
    {}
    pub fn ready(&self)->(out:bool) requires self.wf(), ensures out==self.complete(),out ==> self.elaborated(),
    {
        let mut i=0;
        while i<self.nodes.len()
            invariant self.wf(),i<=self.nodes.len(),forall|j:int| 0<=j<i && (#[trigger] self@[j]).enabled_spec() ==>
                self@[j].allocation_spec().is_some()
                && self@[j].allocation_spec().unwrap().parent_id()==self.parent_for(j as usize,self.root_id())
                && (self@[j].parent_index().is_some() ==> self.parent_for(j as usize,self.root_id()).is_some()),
            decreases self.nodes.len()-i,
        {
            let node=&self.nodes[i];
            if node.enabled {
                let allocation=match &node.allocation {Some(a)=>a,None=>return false};
                let parent=match node.parent {Some(p)=>self.nodes[p].id(),None=>self.root};
                if (node.parent.is_some() && parent.is_none()) || allocation.parent()!=parent {return false;}
            }
            i+=1;
        }
        proof {self.elaboration();}true
    }
}
impl<T> Default for Tree<T> {
    fn default()->(out:Self) ensures out.wf(),out@==Seq::<Node<T>>::empty(), {Self::new(0,None)}
}
impl<T> Clone for Tree<T> {
    fn clone(&self)->(out:Self) ensures out@==self@,out.domain_id()==self.domain_id(),out.root_id()==self.root_id(),
    {
        let mut nodes=Vec::new();let mut i=0;
        while i<self.nodes.len()
            invariant i<=self.nodes.len(),nodes@==self@.take(i as int),decreases self.nodes.len()-i,
        {nodes.push(self.nodes[i].clone());i+=1;}
        assert(nodes@==self@);Self {domain:self.domain,root:self.root,nodes}
    }
}
}
