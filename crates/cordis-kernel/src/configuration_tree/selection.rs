//! Structural removals are selected from the two actual configuration trees.
//! The path cache cannot substitute a different allocation for an entry.
use super::*;
verus! {
#[allow(dead_code)]
pub struct Retirement {index:Ghost<usize>,allocation:Allocation}
impl Retirement {
    pub closed spec fn index(&self)->usize {self.index@}
    pub closed spec fn allocation_spec(&self)->Allocation {self.allocation}
    pub fn allocation(&self)->(out:&Allocation) ensures *out==self.allocation_spec(), {&self.allocation}
}
pub open spec fn retained<T>(next:Tree<T>,key:Seq<char>,id:usize)->bool {
    exists|j:int|0<=j<next@.len() && (#[trigger] next@[j]).name()==key && next@[j].identity()==Some(id)
}
pub open spec fn needed<T>(before:Tree<T>,next:Tree<T>,index:int)->bool {
    0<=index<before@.len() && before@[index].identity().is_some()
        && !retained(next,before@[index].name(),before@[index].identity().unwrap())
}
pub open spec fn plan<T>(before:Tree<T>,next:Tree<T>,out:Seq<Retirement>)->bool {
    (forall|i:int|0<=i<out.len() ==> needed(before,next,out[i].index() as int)
        && out[i].allocation_spec()==before@[out[i].index() as int].allocation_spec().unwrap())
        && (forall|i:int,j:int|0<=i<j<out.len() ==> out[i].index()<out[j].index())
        && (forall|index:int|needed(before,next,index) ==> exists|i:int|0<=i<out.len() && out[i].index()==index)
}
impl<T> Tree<T> {
    fn retains(&self,key:&str,id:usize)->(out:bool)
        ensures out==retained(*self,key@,id),
    {
        let mut i=0;
        while i<self.nodes.len()
            invariant i<=self.nodes.len(),forall|j:int|0<=j<i ==> self@[j].name()!=key@ || self@[j].identity()!=Some(id),
            decreases self.nodes.len()-i,
        {
            if self.nodes[i].key.as_str()==key && self.nodes[i].id()==Some(id) {return true;}
            i+=1;
        }
        false
    }
    /// Reconcile actual allocation identities at matching parent-local paths.
    /// Empty initial state can enter the runtime's domain on its first load.
    pub fn retirements(&self,next:&Self)->(out:Result<Vec<Retirement>,TreeError>)
        requires self.wf(),next.wf(),
        ensures out.is_ok()==(self@.len()==0 || (self.domain_id()==next.domain_id() && self.root_id()==next.root_id())),
            out.is_ok() ==> plan(*self,*next,out->Ok_0@),
            out.is_err() ==> out==Err(TreeError::StaleEntry),
    {
        if !self.nodes.is_empty() && (self.domain!=next.domain || self.root!=next.root) {return Err(TreeError::StaleEntry);}
        let mut out:Vec<Retirement>=Vec::new();let mut i=0;
        while i<self.nodes.len()
            invariant i<=self.nodes.len(),self.wf(),next.wf(),
                forall|j:int|0<=j<out.len() ==> out[j].index()<i && needed(*self,*next,out[j].index() as int)
                    && out[j].allocation_spec()==self@[out[j].index() as int].allocation_spec().unwrap(),
                forall|j:int,k:int|0<=j<k<out.len() ==> out[j].index()<out[k].index(),
                forall|index:int|0<=index<i && needed(*self,*next,index) ==> exists|j:int|0<=j<out.len() && out[j].index()==index,
            decreases self.nodes.len()-i,
        {
            let node=&self.nodes[i];let ghost prior=out@;
            if let Some(a)=node.allocation() {
                if !next.retains(node.key().as_str(),a.id()) {out.push(Retirement {index:Ghost(i),allocation:a});}
            }
            assert forall|index:int|0<=index<i+1 && needed(*self,*next,index) implies exists|j:int|0<=j<out.len() && out[j].index()==index by {
                if index<i {
                    let j=choose|j:int|0<=j<prior.len() && prior[j].index()==index;assert(out[j].index()==index);
                } else {assert(out@.last().index()==i);}
            }
            i+=1;
        }
        Ok(out)
    }
}
/// Each removal is the old entry's real captured allocation, not the candidate's
/// new ID. A different parent-local path cannot retain the same numeric ID.
pub proof fn exact_removal<T>(before:Tree<T>,next:Tree<T>,out:Seq<Retirement>,index:int)
    requires before.wf(),next.wf(),plan(before,next,out),0<=index<out.len(),
    ensures out[index].allocation_spec().wf(),out[index].allocation_spec().domain_id()==before.domain_id(),
        !retained(next,before@[out[index].index() as int].name(),out[index].allocation_spec().owner()),
{}
/// The actual retirement calls, including the first failed callback. Retry
/// policy belongs to the configuration transaction; this dispatch never calls
/// a later selected allocation after failure.
pub struct Removal<H,E> {pub allocation:Allocation,pub before:H,pub after:H,pub result:Result<(),E>}
pub enum RetireError<E> {Tree(TreeError),Callback {offset:usize,error:E}}
#[allow(dead_code)]
pub struct Retired<H,E> {pub result:Result<(),RetireError<E>>,selection:Ghost<Option<Seq<Retirement>>>,calls:Ghost<Seq<Removal<H,E>>>}
impl<H,E> Retired<H,E> {
    pub closed spec fn outcome(&self)->Result<(),RetireError<E>> {self.result}
    pub closed spec fn selection(&self)->Option<Seq<Retirement>> {self.selection@}
    pub closed spec fn calls(&self)->Seq<Removal<H,E>> {self.calls@}
}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn disposed<H,E,C:Fn(&mut H,&Allocation)->Result<(),E>>(
    callback:C,allocation:Allocation,before:H,after:H,result:Result<(),E>)->bool {
    exists|h:&mut H,a:&Allocation| *h==before && *final(h)==after && *a==allocation && callback.ensures((h,a),result)
}
fn dispose<H,E,C:Fn(&mut H,&Allocation)->Result<(),E>>(host:&mut H,allocation:&Allocation,callback:&C)->(out:Result<(),E>)
    requires forall|h:&mut H,a:&Allocation|callback.requires((h,a)),
    ensures disposed(*callback,*allocation,*old(host),*final(host),out),
{reveal(disposed);callback(host,allocation)}
#[verifier::prophetic]
pub open spec fn removal_prefix<H,E,C:Fn(&mut H,&Allocation)->Result<(),E>>(
    selection:Seq<Retirement>,calls:Seq<Removal<H,E>>,before:H,after:H,callback:C)->bool {
    calls.len()<=selection.len()
        && (if calls.len()==0 {before==after} else {calls.first().before==before && calls.last().after==after})
        && forall|i:int|0<=i<calls.len() ==> calls[i].allocation==selection[i].allocation_spec()
            && disposed(callback,calls[i].allocation,calls[i].before,calls[i].after,calls[i].result)
            && (i>0 ==> calls[i-1].after==calls[i].before)
}
impl<T> Tree<T> {
    pub fn retire_into<H,E,C:Fn(&mut H,&Allocation)->Result<(),E>>(&self,next:&Self,host:&mut H,callback:C)->(out:Retired<H,E>)
        requires self.wf(),next.wf(),forall|h:&mut H,a:&Allocation|callback.requires((h,a)),
        ensures out.selection().is_some()==(self@.len()==0 || (self.domain_id()==next.domain_id() && self.root_id()==next.root_id())),
            out.selection().is_none() ==> out.outcome()==Err(RetireError::Tree(TreeError::StaleEntry)) && out.calls().len()==0 && *final(host)==*old(host),
            out.selection().is_some() ==> plan(*self,*next,out.selection().unwrap())
                && removal_prefix(out.selection().unwrap(),out.calls(),*old(host),*final(host),callback)
                && match out.outcome() {
                    Ok(())=>out.calls().len()==out.selection().unwrap().len() && forall|i:int|0<=i<out.calls().len() ==> out.calls()[i].result.is_ok(),
                    Err(RetireError::Callback {offset,error})=>out.calls().len()>0
                        && offset==out.calls().len()-1
                        && out.calls().last().result==Err(error)
                        && forall|i:int|0<=i<out.calls().len()-1 ==> out.calls()[i].result.is_ok(),
                    _=>false,
                },
    {
        let selection=match self.retirements(next) {
            Ok(selection)=>selection,
            Err(error)=>return Retired {result:Err(RetireError::Tree(error)),selection:Ghost(None),calls:Ghost(Seq::empty())},
        };
        let ghost mut calls:Seq<Removal<H,E>>=Seq::empty();let mut i=0;
        while i<selection.len()
            invariant i<=selection.len(),calls.len()==i,plan(*self,*next,selection@),
                self@.len()==0 || (self.domain_id()==next.domain_id() && self.root_id()==next.root_id()),
                removal_prefix(selection@,calls,*old(host),*host,callback),
                forall|j:int|0<=j<calls.len() ==> calls[j].result.is_ok(),
                forall|h:&mut H,a:&Allocation|callback.requires((h,a)),
            decreases selection.len()-i,
        {
            let allocation=selection[i].allocation();let ghost before=*host;
            let result=dispose(host,allocation,&callback);
            proof {calls=calls.push(Removal {allocation:*allocation,before,after:*host,result});}
            if let Err(error)=result {
                // The runtime ordinal is sufficient to locate the real selected
                // allocation; original tree indices remain erased proof data.
                return Retired {result:Err(RetireError::Callback {offset:i,error}),selection:Ghost(Some(selection@)),calls:Ghost(calls)};
            }
            i+=1;
        }
        Retired {result:Ok(()),selection:Ghost(Some(selection@)),calls:Ghost(calls)}
    }
}
}
