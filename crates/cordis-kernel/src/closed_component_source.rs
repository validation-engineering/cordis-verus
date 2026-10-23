//! Source-side sealed component. Its child word is captured from the same
//! recorded owner that ran the root and created the real native requests.
use super::accumulator;
#[cfg(verus_keep_ghost)]
use super::word;
use crate::lifecycle_state::registration::shared_child::SharedChild;
use crate::reversible_value::closed::{Reference, Value};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::Step;
use crate::reversible_value::{
    effect::ScalarEffect,
    function::Body,
    managed::{
        self,
        replay::{session::CallOwner, ManagedRuntime, Source},
    },
};
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
// Failure retains the original owners without allocating or dropping their cleanup state.
#[allow(clippy::large_enum_variant)]
pub enum Error<E> {Before(crate::Error),After {owner:CallOwner<Value>,source:Option<Source<E,Value>>}}
pub struct Component<E> {source:Source<E,Value>,owner:CallOwner<Value>,children:Vec<SharedChild>}
impl<E:ScalarEffect+Copy> Component<E> {
    pub closed spec fn source(&self)->Source<E,Value> {self.source}
    pub closed spec fn owner(&self)->CallOwner<Value> {self.owner}
    pub closed spec fn children(&self)->Seq<SharedChild> {self.children@}
    pub open spec fn root(&self)->Seq<Step<Value>> {self.source().original().result->Ok_0.steps@}
    pub closed spec fn wf(&self)->bool {
        self.source.wf() && self.source.original().result.is_ok() && self.owner.wf() && self.owner.conserved()
            && self.owner.baseline().origin()==Some(self.source.original().origin)
            && self.owner.histories().dom()==set![0usize] && word(self.owner.histories()[0].initial(),self.root(),self.children@)
            && (forall|i:int|0<=i<self.children.len() ==> (#[trigger] self.children@[i]).wf()
                && self.children@[i].domain_id()==self.source.original().origin.domain
                && self.children@[i].owner()==self.source.original().origin.id
                && self.children@[i].episode()==Some(self.source.original().origin.generation))
    }
    /// Reject callbacks before Begin. Actual captured values are then checked
    /// against the complete schema; every failure retains its native owner.
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub fn begin<P>(runtime:&mut ManagedRuntime<P,(),E,Value,()>,id:usize,work_domain:u64,schema:&[Reference])->(out:Result<Self,Error<E>>)
        requires old(runtime).wf(),ensures final(runtime).wf(),out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.source().closed_data(schema@),
    {
        let recipe=match runtime.registration(id) {Some(r)=>r,None=>return Err(Error::Before(crate::Error::Unknown))};
        match recipe.payload_ref() {Body::Managed(f)=>{if !f.check_closed_data(schema) {return Err(Error::Before(crate::Error::InvalidState));}},_=>return Err(Error::Before(crate::Error::InvalidState))}
        let execution:managed::Owner<managed::replay::session::ChildWork,(),(),(),Value,(),()>=match runtime.begin_managed_execution(id,work_domain) {Ok(o)=>o,Err(e)=>return Err(Error::Before(e))};
        let ghost offset=execution.cleanup_state().queues()[0].slots().len();
        let (owner,captured)=runtime.run_replayable_root(id,execution);
        let source=match captured {Ok(c)=>c.source,Err(_)=>return Err(Error::After {owner,source:None})};
        if !source.succeeded() || !source.check_closed_data(schema) {return Err(Error::After {owner,source:Some(source)});}
        let count=source.inputs().len();let ghost root=source.original().result->Ok_0.steps@;
        if !accumulator::root(&owner,count,Ghost(root),Ghost(offset)) {return Err(Error::After {owner,source:Some(source)});}
        Ok(Self {source,owner,children:Vec::new()})
    }
    pub fn id(&self)->(out:usize) requires self.wf(),ensures out==self.source().original().origin.id, {self.source.source_origin().id}
    // Native admission is binary; rejection preserves this entire owner unchanged.
    #[allow(clippy::result_unit_err)]
    pub fn enqueue_child(&mut self)->(out:Result<usize,()>)
        requires old(self).wf(),ensures final(self).wf(),final(self).source()==old(self).source(),
            out.is_err() ==> *final(self)==*old(self),out.is_ok() ==> out->Ok_0==old(self).children().len()
                && final(self).children().len()==old(self).children().len()+1,
    {
        let ghost prior=*self;proof {self.owner.facts();}
        let (child,_token)=self.owner.enqueue_native_child(0,())?;
        let index=self.children.len();self.children.push(child);
        proof {
            let a=prior.owner().histories()[0].initial();let b=self.owner().histories()[0].initial();
            assert forall|i:int|0<=i<self.root().len() implies (#[trigger] self.root()[i]).in_slot(b[i]) by {assert(b[i]==a[i]);}
            assert forall|i:int|0<=i<self.children().len() implies b[self.root().len()+i]==Some(crate::lifecycle_state::registration::shared_child::ChildCleanup::Native(#[trigger] self.children()[i])) by {
                if i<prior.children().len() {assert(self.children()[i]==prior.children()[i]);}else {assert(i==prior.children().len());}
            }
            assert forall|i:int|0<=i<self.children().len() implies (#[trigger] self.children()[i]).wf()
                && self.children()[i].domain_id()==self.source.original().origin.domain && self.children()[i].owner()==self.source.original().origin.id
                && self.children()[i].episode()==Some(self.source.original().origin.generation) by {
                if i<prior.children().len() {assert(self.children()[i]==prior.children()[i]);}
            }
        }Ok(index)
    }
    pub fn finish<P>(&mut self,runtime:&mut ManagedRuntime<P,(),E,Value,()>)->(out:Result<(),crate::Error>)
        requires old(self).wf(),old(runtime).wf(),old(runtime).journal_spec()==old(self).source().original().completion().journal(),
        ensures final(self).wf(),final(runtime).wf(),
    {
        let ghost prior=*self;
        let out=self.source.finish(runtime,&mut self.owner);
        proof {
            assert(prior.owner().histories().contains_key(0));
            assert(self.owner().histories()[0].initial()==prior.owner().histories()[0].initial());
            assert(self.root()==prior.root());
            assert(word(self.owner().histories()[0].initial(),self.root(),self.children()));
        }
        out
    }
    /// The source word is captured now, after every admitted Child request.
    /// Taking the ordinary owner explicitly ends this sealed source interface.
    pub fn into_parts(self)->(out:(Source<E,Value>,CallOwner<Value>))
        requires self.wf(),ensures out.0.wf(),out.1.wf(),out.0.original()==self.source().original(),out.1==self.owner(),
            out.0.component_word().is_some(),out.0.component_word().unwrap().owner()==out.1,
            out.0.component_word().unwrap().children()==self.children(),
    {
        let saved=accumulator::Word::capture(&self.owner,self.children.as_slice(),Ghost(self.root()));
        let mut source=self.source;
        source.attach_component_word(saved);
        (source,self.owner)
    }
}
}
