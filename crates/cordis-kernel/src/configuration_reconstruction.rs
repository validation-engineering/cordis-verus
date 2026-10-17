//! The production mount/recovery traversal. The callback receives each enabled
//! saved node and its actual current parent, in authoritative tree order.
//! Ghost receipts connect partial failure to exactly the callbacks that ran.
use super::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub struct RebuildError<E> {pub index:usize,pub error:MountError<E>}
pub open spec fn same_recipe<T>(before:Node<T>,after:Node<T>)->bool {
    before.name()==after.name() && before.parent_index()==after.parent_index()
        && before.enabled_spec()==after.enabled_spec() && before.payload()==after.payload() && before.source()==after.source()
}
pub open spec fn same_layout<T>(before:Tree<T>,after:Tree<T>)->bool {
    before.domain_id()==after.domain_id() && before.root_id()==after.root_id() && before@.len()==after@.len()
        && forall|i:int|0<=i<before@.len() ==> same_recipe(before@[i],after@[i])
}
pub open spec fn complete_prefix<T>(tree:Tree<T>,count:nat)->bool {
    count<=tree@.len() && forall|i:int|0<=i<count && (#[trigger] tree@[i]).enabled_spec() ==>
        tree@[i].allocation_spec().is_some()
        && tree@[i].allocation_spec().unwrap().parent_id()==tree.parent_for(i as usize,tree.root_id())
        && (tree@[i].parent_index().is_some() ==> tree.parent_for(i as usize,tree.root_id()).is_some())
}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn called<T,H,E,C:Fn(&mut H,&Node<T>,Option<usize>)->Result<Allocation,E>>(
    callback:C,before:H,after:H,node:Node<T>,parent:Option<usize>,result:Result<Allocation,E>)->bool {
    exists|h:&mut H,n:&Node<T>|*h==before && *final(h)==after && *n==node && callback.ensures((h,n,parent),result)
}
fn invoke<T,H,E,C:Fn(&mut H,&Node<T>,Option<usize>)->Result<Allocation,E>>(
    host:&mut H,node:&Node<T>,parent:Option<usize>,callback:&C)->(out:Result<Allocation,E>)
    requires forall|h:&mut H,n:&Node<T>,p:Option<usize>| callback.requires((h,n,p)),
    ensures called(*callback,*old(host),*final(host),*node,parent,out),
{reveal(called);callback(host,node,parent)}
pub struct Visit<T,H,E> {pub before:Tree<T>,pub after:Tree<T>,pub host_before:H,pub host_after:H,pub result:Option<Result<Allocation,E>>}
impl<T,H,E> Visit<T,H,E> {
    pub open spec fn accepted(&self,index:nat)->bool {
        match self.result {None=>true,Some(result)=>result.is_ok() && self.before.accepts_allocation(index as usize,result->Ok_0)}
    }
    pub open spec fn matches_error(&self,error:MountError<E>)->bool {
        match self.result {None=>false,Some(result)=>match result {
            Err(e)=>error==MountError::Callback(e),Ok(a)=>error==MountError::Mismatch(a),
        }}
    }
    #[verifier::prophetic]
    pub open spec fn valid<C:Fn(&mut H,&Node<T>,Option<usize>)->Result<Allocation,E>>(&self,index:nat,callback:C)->bool {
        self.before.wf() && self.after.wf() && index<self.before@.len() && same_layout(self.before,self.after)
            && match self.result {
                None=>!self.before@[index as int].enabled_spec() && self.before==self.after && self.host_before==self.host_after,
                Some(result)=>self.before@[index as int].enabled_spec()
                    && called(callback,self.host_before,self.host_after,self.before@[index as int],self.before.parent_for(index as usize,self.before.root_id()),result)
                    && if self.accepted(index) {
                        self.after@==self.before@.update(index as int,self.after@[index as int])
                            && self.after@[index as int].allocation_spec()==Some(result->Ok_0)
                    } else {self.after==self.before},
            }
    }
}
#[verifier::prophetic]
pub open spec fn chain<T,H,E,C:Fn(&mut H,&Node<T>,Option<usize>)->Result<Allocation,E>>(
    before:Tree<T>,after:Tree<T>,host_before:H,host_after:H,visits:Seq<Visit<T,H,E>>,callback:C)->bool {
    visits.len()<=before@.len()
        && (if visits.len()==0 {before==after && host_before==host_after} else {
            visits.first().before==before && visits.first().host_before==host_before
                && visits.last().after==after && visits.last().host_after==host_after
        })
        && forall|i:int|0<=i<visits.len() ==> visits[i].valid(i as nat,callback)
            && (i>0 ==> visits[i-1].after==visits[i].before && visits[i-1].host_after==visits[i].host_before)
}
#[allow(dead_code)]
pub struct Rebuilt<T,H,E> {pub result:Result<(),RebuildError<E>>,evidence:Ghost<Seq<Visit<T,H,E>>>}
impl<T,H,E> Rebuilt<T,H,E> {pub closed spec fn outcome(&self)->Result<(),RebuildError<E>> {self.result}
pub closed spec fn visits(&self)->Seq<Visit<T,H,E>> {self.evidence@}}
impl<T> Tree<T> {
    /// Both initial application and recovery use this loop. Partial success is
    /// retained in the real tree; an error stops before every later callback.
    pub fn reconstruct<H,E,C:Fn(&mut H,&Node<T>,Option<usize>)->Result<Allocation,E>>(
        &mut self,host:&mut H,callback:C)->(out:Rebuilt<T,H,E>)
        requires old(self).wf(),
            forall|h:&mut H,n:&Node<T>,p:Option<usize>| callback.requires((h,n,p)),
            forall|h:&mut H,n:&Node<T>,p:Option<usize>,r:Result<Allocation,E>| callback.ensures((h,n,p),r) && r.is_ok() ==> r->Ok_0.wf(),
        ensures final(self).wf(),same_layout(*old(self),*final(self)),
            chain(*old(self),*final(self),*old(host),*final(host),out.visits(),callback),
            out.outcome().is_ok() ==> out.visits().len()==old(self)@.len() && final(self).complete()
                && forall|i:int|0<=i<out.visits().len() ==> out.visits()[i].accepted(i as nat),
            out.outcome().is_err() ==> out.visits().len()==out.outcome()->Err_0.index+1
                && out.visits().last().matches_error(out.outcome()->Err_0.error)
                && !out.visits().last().accepted(out.outcome()->Err_0.index as nat)
                && complete_prefix(*final(self),out.outcome()->Err_0.index as nat)
                && (forall|i:int|0<=i<out.outcome()->Err_0.index ==> out.visits()[i].accepted(i as nat))
                && (forall|i:int|out.outcome()->Err_0.index<=i<old(self)@.len() ==> final(self)@[i]==old(self)@[i]),
    {
        let mut i:usize=0;let ghost mut visits:Seq<Visit<T,H,E>>=Seq::empty();
        while i<self.nodes.len()
            invariant self.wf(),same_layout(*old(self),*self),i<=self.nodes.len(),visits.len()==i,
                complete_prefix(*self,i as nat),chain(*old(self),*self,*old(host),*host,visits,callback),
                forall|j:int|0<=j<i ==> visits[j].accepted(j as nat),
                forall|j:int|i<=j<self@.len() ==> self@[j]==old(self)@[j],
                forall|h:&mut H,n:&Node<T>,p:Option<usize>| callback.requires((h,n,p)),
                forall|h:&mut H,n:&Node<T>,p:Option<usize>,r:Result<Allocation,E>| callback.ensures((h,n,p),r) && r.is_ok() ==> r->Ok_0.wf(),
            decreases self.nodes.len()-i,
        {
            let ghost before=*self;let ghost host_before=*host;
            if !self.nodes[i].enabled {
                proof {visits=visits.push(Visit {before,after:*self,host_before,host_after:*host,result:None});}
            } else {
                let parent=self.parent_id_at(i);
                assert(self@[i as int].parent_index().is_some() ==> parent.is_some());
                let result=invoke(host,&self.nodes[i],parent,&callback);
                proof {reveal(called);}
                let ghost landed=result;
                let installed=match result {Ok(a)=>self.install(i,a),Err(e)=>Err(MountError::Callback(e))};
                proof {
                    visits=visits.push(Visit {before,after:*self,host_before,host_after:*host,result:Some(landed)});
                }
                if let Err(error)=installed {
                    return Rebuilt {result:Err(RebuildError {index:i,error}),evidence:Ghost(visits)};
                }
            }
            assert forall|j:int|0<=j<i+1 && self@[j].enabled_spec() implies
                self@[j].allocation_spec().is_some() && self@[j].allocation_spec().unwrap().parent_id()==self.parent_for(j as usize,self.root_id())
                    && (self@[j].parent_index().is_some() ==> self.parent_for(j as usize,self.root_id()).is_some()) by {
                if j<i {assert(before@[j]==self@[j]);
                    if self@[j].parent_index().is_some() {let p=self@[j].parent_index().unwrap() as int;assert(p<j);assert(before@[p]==self@[p]);}
                }
            }
            i+=1;
        }
        Rebuilt {result:Ok(()),evidence:Ghost(visits)}
    }
}
}
