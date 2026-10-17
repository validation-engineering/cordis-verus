//! Actual all-or-nothing preflight and complete recipe adoption. The batch owns
//! its payloads throughout preflight. Distinct targets stay current until their
//! own replacement; old recipes/metadata are returned after all swaps complete.
use super::{NativeRuntime, Target};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::native::NativeEntry;
use std::collections::BTreeSet;
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub struct Change<R,M> {pub target:Target,pub recipe:R,pub metadata:M}
pub struct Previous<R,P> {pub target:Target,pub recipe:R,pub metadata:P}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Cause {Target,Duplicate,Capacity}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Failure {pub index:usize,pub cause:Cause}
pub struct Rejected<R,M> {pub failure:Failure,pub changes:Vec<Change<R,M>>}
pub open spec fn owners<R,M>(changes:Seq<Change<R,M>>)->Seq<usize> {
    Seq::new(changes.len(),|i:int|changes[i].target.owner())
}
#[verifier::opaque]
pub open spec fn ready<R,H,V,M>(runtime:NativeRuntime<R,H,V>,changes:Seq<Change<R,M>>)->bool {
    owners(changes).no_duplicates() && forall|i:int|0<=i<changes.len() ==> {
        let target=#[trigger] changes[i].target;
        runtime.configuration_matches(target) && runtime.registry().entries()[target.owner()].recipe().version()<u64::MAX
    }
}
pub open spec fn rejected<R,H,V,M>(runtime:NativeRuntime<R,H,V>,changes:Seq<Change<R,M>>,failure:Failure)->bool {
    failure.index<changes.len() && match failure.cause {
        Cause::Target=>!runtime.configuration_matches(changes[failure.index as int].target),
        Cause::Duplicate=>exists|j:int|0<=j<failure.index && (#[trigger] changes[j]).target.owner()==changes[failure.index as int].target.owner(),
        Cause::Capacity=>runtime.configuration_matches(changes[failure.index as int].target)
            && runtime.registry().entries()[changes[failure.index as int].target.owner()].recipe().version()==u64::MAX,
    }
}
proof fn rejected_not_ready<R,H,V,M>(runtime:NativeRuntime<R,H,V>,changes:Seq<Change<R,M>>,failure:Failure)
    requires rejected(runtime,changes,failure),ensures !ready(runtime,changes),
{
    reveal(ready);
    if ready(runtime,changes) {
        let i=failure.index as int;let target=changes[i].target;
        assert(runtime.configuration_matches(target));
        assert(runtime.registry().entries()[target.owner()].recipe().version()<u64::MAX);
        if failure.cause==Cause::Duplicate {
            let j=choose|j:int|0<=j<i && (#[trigger] changes[j]).target.owner()==target.owner();
            assert(owners(changes)[j]==owners(changes)[i]);
        }
    }
}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn metadata_call<H,M,P,C:Fn(&mut H,M)->P>(callback:C,before:H,after:H,metadata:M,result:P)->bool {
    exists|h:&mut H|*h==before && *final(h)==after && callback.ensures((h,metadata),result)
}
fn update_metadata<H,M,P,C:Fn(&mut H,M)->P>(host:&mut H,metadata:M,callback:&C)->(out:P)
    requires forall|h:&mut H,m:M|(*callback).requires((h,m)),
    ensures metadata_call(*callback,*old(host),*final(host),metadata,out),
{reveal(metadata_call);(*callback)(host,metadata)}
/// Registration identity and the captured live episode remain unchanged. Only
/// the future setup recipe/version and the selected opaque host fields change.
pub open spec fn framed<R,H,V>(before:NativeRuntime<R,H,V>,after:NativeRuntime<R,H,V>)->bool {
    after.wf() && after.state()==before.state() && after.publications()==before.publications()
        && after.episode_owners()==before.episode_owners() && after.journal_spec()==before.journal_spec() && after.joint_key()==before.joint_key()
        && after.registry().entries().dom()==before.registry().entries().dom()
}
#[verifier::prophetic]
pub open spec fn adopted<R,H,M,P,C:Fn(&mut H,M)->P>(before:NativeEntry<R,H>,after:NativeEntry<R,H>,change:Change<R,M>,previous:Previous<R,P>,callback:C)->bool {
    after.recipe().same_identity(&before.recipe()) && after.recipe().payload()==change.recipe
        && after.recipe().version()==before.recipe().version()+1 && previous.target==change.target
        && previous.recipe==before.recipe().payload()
        && metadata_call(callback,before.bookkeeping(),after.bookkeeping(),change.metadata,previous.metadata)
}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn prefix<R,H,V,M,P,C:Fn(&mut H,M)->P>(before:NativeRuntime<R,H,V>,after:NativeRuntime<R,H,V>,changes:Seq<Change<R,M>>,previous:Seq<Previous<R,P>>,callback:C)->bool {
    &&& framed(before,after) && previous.len()<=changes.len()
    &&& forall|i:int|0<=i<previous.len() ==> adopted(before.registry().entries()[changes[i].target.owner()],after.registry().entries()[changes[i].target.owner()],changes[i],#[trigger] previous[i],callback)
    &&& forall|n:usize|before.registry().entries().contains_key(n) && !owners(changes.take(previous.len() as int)).contains(n)
        ==> #[trigger] after.registry().entries()[n]==before.registry().entries()[n]
}
impl<R,H,V> NativeRuntime<R,H,V> {
    /// Validate the whole owned batch before any recipe or host mutation.
    pub fn preflight_configurations<M>(&self,changes:&[Change<R,M>])->(out:Result<(),Failure>)
        requires self.wf(),
        ensures out.is_ok()==ready(*self,changes@),out.is_err() ==> rejected(*self,changes@,out->Err_0),
    {
        reveal(ready);
        let mut seen:BTreeSet<usize>=BTreeSet::new();let mut i:usize=0;
        while i<changes.len()
            invariant self.wf(),i<=changes.len(),seen@==owners(changes@.take(i as int)).to_set(),owners(changes@.take(i as int)).no_duplicates(),
                forall|j:int|0<=j<i ==> self.configuration_matches(changes@[j].target)
                    && self.registry().entries()[changes@[j].target.owner()].recipe().version()<u64::MAX,
            decreases changes.len()-i,
        {
            let target=changes[i].target;
            if !self.configuration_target_is_current(target) {
                let failure=Failure {index:i,cause:Cause::Target};proof {rejected_not_ready(*self,changes@,failure);}return Err(failure);
            }
            let id=target.id();
            if !seen.insert(id) {
                assert(exists|j:int|0<=j<i && (#[trigger] changes@[j]).target.owner()==id) by {
                    let j=choose|j:int|0<=j<i && owners(changes@.take(i as int))[j]==id;
                    assert(changes@[j].target.owner()==id);
                }
                let failure=Failure {index:i,cause:Cause::Duplicate};proof {rejected_not_ready(*self,changes@,failure);}return Err(failure);
            }
            let recipe=self.registration(id).unwrap();
            if !recipe.can_replace() {
                let failure=Failure {index:i,cause:Cause::Capacity};proof {rejected_not_ready(*self,changes@,failure);}return Err(failure);
            }
            assert(owners(changes@.take(i as int+1)) =~= owners(changes@.take(i as int)).push(id));
            i+=1;
        }
        assert(changes@.take(i as int)==changes@);
        Ok(())
    }
}
proof fn empty_prefix<R,H,V,M,P,C:Fn(&mut H,M)->P>(before:NativeRuntime<R,H,V>,changes:Seq<Change<R,M>>,callback:C)
    requires before.wf(),ensures prefix(before,before,changes,Seq::<Previous<R,P>>::empty(),callback),
{reveal(prefix);assert(owners(changes.take(0)).len()==0);}
proof fn unprocessed<R,H,V,M,P,C:Fn(&mut H,M)->P>(before:NativeRuntime<R,H,V>,current:NativeRuntime<R,H,V>,changes:Seq<Change<R,M>>,previous:Seq<Previous<R,P>>,callback:C)
    requires before.wf(),ready(before,changes),prefix(before,current,changes,previous,callback),previous.len()<changes.len(),
    ensures current.configuration_matches(changes[previous.len() as int].target),
        before.registry().entries().contains_key(changes[previous.len() as int].target.owner()),
        current.registry().entries().contains_key(changes[previous.len() as int].target.owner()),
        current.registry().entries()[changes[previous.len() as int].target.owner()]==before.registry().entries()[changes[previous.len() as int].target.owner()],
        current.registry().entries()[changes[previous.len() as int].target.owner()].recipe().version()<u64::MAX,
{
    reveal(ready);reveal(prefix);
    let i=previous.len() as int;let id=changes[i].target.owner();
    assert(owners(changes)[i]==id);
    assert(!owners(changes.take(i)).contains(id)) by {
        if owners(changes.take(i)).contains(id) {
            let j=choose|j:int|0<=j<i && owners(changes.take(i))[j]==id;
            assert(owners(changes)[j]==owners(changes)[i]);
        }
    }
}
proof fn append_prefix<R,H,V,M,P,C:Fn(&mut H,M)->P>(before:NativeRuntime<R,H,V>,current:NativeRuntime<R,H,V>,after:NativeRuntime<R,H,V>,changes:Seq<Change<R,M>>,previous:Seq<Previous<R,P>>,item:Previous<R,P>,callback:C)
    requires ready(before,changes),prefix(before,current,changes,previous,callback),previous.len()<changes.len(),framed(current,after),
        adopted(before.registry().entries()[changes[previous.len() as int].target.owner()],after.registry().entries()[changes[previous.len() as int].target.owner()],changes[previous.len() as int],item,callback),
        forall|n:usize|current.registry().entries().contains_key(n) && n!=changes[previous.len() as int].target.owner()
            ==> #[trigger] after.registry().entries()[n]==current.registry().entries()[n],
    ensures prefix(before,after,changes,previous.push(item),callback),
{
    reveal(ready);reveal(prefix);
    let i=previous.len() as int;let id=changes[i].target.owner();
    assert(owners(changes.take(i+1)) =~= owners(changes.take(i)).push(id));
    assert forall|j:int|0<=j<i+1 implies adopted(before.registry().entries()[changes[j].target.owner()],after.registry().entries()[changes[j].target.owner()],changes[j],#[trigger] previous.push(item)[j],callback) by {
        if j<i {assert(owners(changes)[j]!=owners(changes)[i]);assert(changes[j].target.owner()!=id);}
    }
    assert forall|n:usize|before.registry().entries().contains_key(n) && !owners(changes.take(i+1)).contains(n)
        implies #[trigger] after.registry().entries()[n]==before.registry().entries()[n] by {
        assert(n!=id);assert(!owners(changes.take(i)).contains(n));
    }
}
impl<R,H,V> NativeRuntime<R,H,V> {
    /// No caller-selected success acknowledgement. Invalid input is returned
    /// intact; successful preflight proves every real replacement can succeed.
    pub fn adopt_configurations<M,P,C:Fn(&mut H,M)->P>(&mut self,changes:Vec<Change<R,M>>,callback:C)
        ->(out:Result<Vec<Previous<R,P>>,Rejected<R,M>>)
        requires old(self).wf(),forall|h:&mut H,m:M|callback.requires((h,m)),
        ensures final(self).wf(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.changes==changes
                && rejected(*old(self),changes@,out->Err_0.failure),
            out.is_ok() ==> ready(*old(self),changes@) && out->Ok_0.len()==changes.len()
                && prefix(*old(self),*final(self),changes@,out->Ok_0@,callback),
    {
        if let Err(failure)=self.preflight_configurations(changes.as_slice()) {return Err(Rejected {failure,changes});}
        let ghost initial=*self;let ghost input=changes@;
        let mut previous:Vec<Previous<R,P>>=Vec::with_capacity(changes.len());
        proof {empty_prefix(initial,input,callback);}
        for change in iter: changes
            invariant self.wf(),initial==*old(self),initial.wf(),input==changes@,iter.seq()==input,previous.len()==iter.index(),
                ready(initial,input),prefix(initial,*self,input,previous@,callback),
                forall|h:&mut H,m:M|callback.requires((h,m)),
        {
            let ghost current=*self;let ghost index=previous.len();let ghost original=change;
            proof {assert(input[index as int]==original);unprocessed(initial,*self,input,previous@,callback);}
            let id=change.target.id();
            let recipe=self.replace_configuration(change.target,change.recipe).ok().unwrap();
            let ghost installed=*self;
            assert(framed(current,installed));
            let host=self.host_mut(id).unwrap();
            let metadata=update_metadata(host,change.metadata,&callback);
            let ghost host_after=*host;
            let item=Previous {target:change.target,recipe,metadata};
            proof {
                installed.registry().entries()[id].with_host_properties(host_after);
                assert(self.registry().entries()==installed.registry().entries().insert(id,installed.registry().entries()[id].with_host(host_after)));
                assert(self.registry().entries().dom()==installed.registry().entries().dom());
                assert(framed(installed,*self));
                assert(framed(current,*self));
                assert(adopted(initial.registry().entries()[id],self.registry().entries()[id],original,item,callback));
                append_prefix(initial,current,*self,input,previous@,item,callback);
            }
            previous.push(item);
        }
        Ok(previous)
    }
}
}
