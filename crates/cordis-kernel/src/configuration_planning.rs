//! The actual configuration planner traversal. Structured inputs determine the
//! complete parent-before-child order; every recipe/context comes from the real
//! callback for that entry and the result returned for its actual parent.
use crate::configuration_runtime::Allocation;
use crate::configuration_tree::{identity::PreparedEntry, Tree, TreeError};
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub struct Entry<T> {pub id:String,pub enabled:bool,pub payload:T,pub children:Vec<Entry<T>>}
impl<T> Entry<T> {
    pub fn new(id:String,enabled:bool,payload:T,children:Vec<Self>)->(out:Self)
        ensures out.id==id,out.enabled==enabled,out.payload==payload,out.children==children,
    {Self {id,enabled,payload,children}}
}
pub struct Flat<T> {id:String,enabled:bool,payload:T,parent:Option<usize>}
pub struct Description<T> {pub id:Seq<char>,pub enabled:bool,pub payload:T,pub parent:Option<usize>}
impl<T> Flat<T> {
    pub closed spec fn describe(&self)->Description<T> {Description {id:self.id@,enabled:self.enabled,payload:self.payload,parent:self.parent}}
}
pub open spec fn describe<T>(items:Seq<Flat<T>>)->Seq<Description<T>> {
    Seq::new(items.len(),|i:int|items[i].describe())
}
/// The order and parent of every source position, including disabled entries.
/// Offsets count all preceding entries, not just siblings or enabled entries.
pub open spec fn preorder<T>(entries:Seq<Entry<T>>,parent:Option<usize>,start:nat)->Seq<Description<T>>
    decreases entries,
{
    if entries.len()==0 {Seq::empty()} else {
        let first=entries.first();let children=preorder(first.children@,Some(start as usize),start+1);
        seq![Description {id:first.id@,enabled:first.enabled,payload:first.payload,parent}]+children
            +preorder(entries.skip(1),parent,start+1+children.len())
    }
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum InputError {Depth,Capacity}
fn append_forest<T>(out:&mut Vec<Flat<T>>,entries:Vec<Entry<T>>,parent:Option<usize>,depth:usize)->(result:Result<(),InputError>)
    requires depth<=129,
    ensures result.is_ok() ==> describe(final(out)@)==describe(old(out)@)+preorder(entries@,parent,old(out).len() as nat),
    decreases 130-depth,entries,
{
    if depth>128 {return Err(InputError::Depth);}
    let ghost input=entries@;let ghost base=out.len();
    let ghost mut done:nat=0;
    let ghost mut rest=preorder(input,parent,base as nat);
    for entry in iter: entries
        invariant depth<=128,done<=input.len(),iter.seq()==input,iter.index()==done,
            describe(out@)+rest==describe(old(out)@)+preorder(input,parent,base as nat),
            rest==preorder(input.skip(done as int),parent,out.len() as nat),
    {
        if out.len()==usize::MAX {return Err(InputError::Capacity);}
        let index=out.len();let ghost head=entry;let ghost previous=out@;
        assert(input[done as int]==entry);
        let children=entry.children;
        out.push(Flat {id:entry.id,enabled:entry.enabled,payload:entry.payload,parent});
        let ghost after_head=out@;
        append_forest(out,children,Some(index),depth+1)?;
        proof {
            assert(describe(after_head)==describe(previous).push(Description {id:head.id@,enabled:head.enabled,payload:head.payload,parent}));
            let subtree=preorder(head.children@,Some(index),index as nat+1);
            assert(after_head.len()==index+1);
            assert(describe(out@)==describe(after_head)+subtree);
            assert(describe(out@).len()==out.len());
            assert(out.len()==index+1+subtree.len());
            assert(input.skip(done as int).first()==head);
            assert(input.skip(done as int).skip(1)==input.skip((done+1) as int));
            assert(rest==seq![Description {id:head.id@,enabled:head.enabled,payload:head.payload,parent}]+subtree
                +preorder(input.skip((done+1) as int),parent,out.len() as nat));
            rest=preorder(input.skip((done+1) as int),parent,out.len() as nat);
            done=done+1;
        }
    }
    assert(done==input.len());
    Ok(())
}
pub struct Prepared<N,S> {pub data:N,pub context:S,pub allocation:Option<Allocation>}
pub struct Call<T,N,S,H,E> {
    pub before:H,pub after:H,pub input:T,pub entry:PreparedEntry,pub context:S,pub result:Result<Prepared<N,S>,E>,
}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn called<T,N,S,H,E,C:Fn(&mut H,&T,&PreparedEntry,&S)->Result<Prepared<N,S>,E>>(
    callback:C,call:Call<T,N,S,H,E>)->bool {
    exists|h:&mut H,t:&T,e:&PreparedEntry,s:&S|*h==call.before && *final(h)==call.after
        && *t==call.input && *e==call.entry && *s==call.context && callback.ensures((h,t,e,s),call.result)
}
fn invoke<T,N,S,H,E,C:Fn(&mut H,&T,&PreparedEntry,&S)->Result<Prepared<N,S>,E>>(
    host:&mut H,input:&T,entry:&PreparedEntry,context:&S,callback:&C)->(out:Result<Prepared<N,S>,E>)
    requires forall|h:&mut H,t:&T,e:&PreparedEntry,s:&S|(*callback).requires((h,t,e,s)),
    ensures called(*callback,Call {before:*old(host),after:*final(host),input:*input,entry:*entry,context:*context,result:out}),
{reveal(called);(*callback)(host,input,entry,context)}
pub enum PlanError<E> {Input(InputError),Tree {index:usize,cause:TreeError},Callback {index:usize,error:E}}
#[verifier::prophetic]
#[verifier::opaque]
pub open spec fn chain<T,N,S,H,E,C:Fn(&mut H,&T,&PreparedEntry,&S)->Result<Prepared<N,S>,E>>(
    calls:Seq<Call<T,N,S,H,E>>,initial:H,current:H,callback:C)->bool {
    (if calls.len()==0 {current==initial} else {calls.first().before==initial && calls.last().after==current})
        && forall|i:int|0<=i<calls.len() ==> {let item=#[trigger] calls[i];called(callback,item) && (i>0 ==> item.before==calls[i-1].after)}
}
pub open spec fn matches_input<T,N,S,H,E>(item:Description<T>,root:S,call:Call<T,N,S,H,E>,prior:Seq<Call<T,N,S,H,E>>)->bool {
    &&& call.entry.wf() && call.input==item.payload
    &&& call.entry.origin().local==item.id && call.entry.origin().enabled==item.enabled
    &&& call.entry.parent_index()==item.parent
    &&& match item.parent {None=>call.context==root,Some(p)=>p<prior.len() && call.context==prior[p as int].result->Ok_0.context}
}
pub open spec fn node_from_call<T,N,S,H,E>(node:crate::configuration_tree::Node<N>,call:Call<T,N,S,H,E>)->bool {
    &&& call.result.is_ok() && node.parent_index()==call.entry.parent_index()
    &&& node.source()==Some(call.entry.origin()) && node.name()==call.entry.name() && node.enabled_spec()==call.entry.enabled_spec()
    &&& node.payload()==call.result->Ok_0.data && node.allocation_spec()==call.result->Ok_0.allocation
}
/// Complete accepted prefix, using the context actually returned for its parent.
#[verifier::opaque]
pub open spec fn prefix<T,N,S,H,E>(items:Seq<Description<T>>,tree:Tree<N>,root:S,calls:Seq<Call<T,N,S,H,E>>)->bool {
    &&& tree.wf() && tree@.len()<=calls.len()<=items.len()
    &&& forall|i:int|0<=i<calls.len() ==> matches_input(items[i],root,#[trigger] calls[i],calls.take(i))
    &&& forall|i:int|0<=i<tree@.len() ==> node_from_call(tree@[i],#[trigger] calls[i])
}
proof fn empty_prefix<T,N,S,H,E>(items:Seq<Description<T>>,tree:Tree<N>,root:S)
    requires tree.wf(),tree@.len()==0,
    ensures prefix(items,tree,root,Seq::<Call<T,N,S,H,E>>::empty()),
{reveal(prefix);}
proof fn extend_prefix<T,N,S,H,E>(items:Seq<Description<T>>,tree:Tree<N>,root:S,calls:Seq<Call<T,N,S,H,E>>,call:Call<T,N,S,H,E>)
    requires prefix(items,tree,root,calls),calls.len()<items.len(),matches_input(items[calls.len() as int],root,call,calls),
    ensures prefix(items,tree,root,calls.push(call)),
{
    reveal(prefix);
    assert forall|i:int|0<=i<calls.len()+1 implies matches_input(items[i],root,#[trigger] calls.push(call)[i],calls.push(call).take(i)) by {
        if i<calls.len() {assert(calls.push(call).take(i)==calls.take(i));}
        else {assert(calls.push(call).take(i)==calls);}
    }
    assert forall|i:int|0<=i<tree@.len() implies node_from_call(tree@[i],#[trigger] calls.push(call)[i]) by { }

}
proof fn append_prefix<T,N,S,H,E>(items:Seq<Description<T>>,before:Tree<N>,after:Tree<N>,root:S,calls:Seq<Call<T,N,S,H,E>>)
    requires prefix(items,before,root,calls),after.wf(),before@.len()<items.len(),calls.len()==before@.len()+1,
        after@.len()==before@.len()+1,after@.take(before@.len() as int)==before@,
        matches_input(items[before@.len() as int],root,calls.last(),calls.drop_last()),node_from_call(after@.last(),calls.last()),
    ensures prefix(items,after,root,calls),
{
    reveal(prefix);
    assert forall|i:int|0<=i<after@.len() implies node_from_call(after@[i],#[trigger] calls[i]) by {
        if i<before@.len() {assert(after@[i]==before@[i]);}else{assert(calls[i]==calls.last());}
    }

}
proof fn empty_chain<T,N,S,H,E,C:Fn(&mut H,&T,&PreparedEntry,&S)->Result<Prepared<N,S>,E>>(host:H,callback:C)
    ensures chain(Seq::<Call<T,N,S,H,E>>::empty(),host,host,callback),
{reveal(chain);}
proof fn append_chain<T,N,S,H,E,C:Fn(&mut H,&T,&PreparedEntry,&S)->Result<Prepared<N,S>,E>>(
    calls:Seq<Call<T,N,S,H,E>>,initial:H,call:Call<T,N,S,H,E>,callback:C)
    requires chain(calls,initial,call.before,callback),called(callback,call),
    ensures chain(calls.push(call),initial,call.after,callback),
{
    reveal(chain);
    assert forall|i:int|0<=i<calls.len()+1 implies called(callback,#[trigger] calls.push(call)[i])
        && (i>0 ==> calls.push(call)[i].before==calls.push(call)[i-1].after) by {
        if i<calls.len() {assert(called(callback,calls[i]));}
        else {assert(calls.push(call)[i]==call);if i>0 {assert(calls[i-1]==calls.last());}}
    }
}
proof fn allocation_wf<T,N,S,H,E,C:Fn(&mut H,&T,&PreparedEntry,&S)->Result<Prepared<N,S>,E>>(call:Call<T,N,S,H,E>,callback:C)
    requires called(callback,call),forall|h:&mut H,t:&T,e:&PreparedEntry,s:&S,r:Result<Prepared<N,S>,E>|callback.ensures((h,t,e,s),r)
        && r.is_ok() && r->Ok_0.allocation.is_some() ==> r->Ok_0.allocation.unwrap().wf(),
    ensures call.result.is_ok() && call.result->Ok_0.allocation.is_some() ==> call.result->Ok_0.allocation.unwrap().wf(),
{reveal(called);}
type Calls<T,N,S,H,E> = Seq<Call<T,N,S,H,E>>;
#[allow(dead_code)]
pub struct Planned<T,N,S,H,E> {
    pub result:Result<Tree<N>,PlanError<E>>,pub host:H,
    calls:Ghost<Calls<T,N,S,H,E>>,partial:Ghost<Tree<N>>,
}
impl<T,N,S,H,E> Planned<T,N,S,H,E> {
    pub closed spec fn outcome(&self)->Result<Tree<N>,PlanError<E>> {self.result}
    pub closed spec fn host_spec(&self)->H {self.host}
    pub closed spec fn calls(&self)->Seq<Call<T,N,S,H,E>> {self.calls@}
    pub closed spec fn partial(&self)->Tree<N> {self.partial@}
}
pub fn plan<T,N,S,H,E,C:Fn(&mut H,&T,&PreparedEntry,&S)->Result<Prepared<N,S>,E>>(
    entries:Vec<Entry<T>>,root:S,domain:u64,parent:Option<usize>,host:H,callback:C)->(out:Planned<T,N,S,H,E>)
    requires forall|h:&mut H,t:&T,e:&PreparedEntry,s:&S|callback.requires((h,t,e,s)),
        forall|h:&mut H,t:&T,e:&PreparedEntry,s:&S,r:Result<Prepared<N,S>,E>|callback.ensures((h,t,e,s),r)
            && r.is_ok() && r->Ok_0.allocation.is_some() ==> r->Ok_0.allocation.unwrap().wf(),
    ensures chain(out.calls(),host,out.host_spec(),callback),
        out.partial().wf(),out.partial().domain_id()==domain,out.partial().root_id()==parent,
        out.outcome().is_ok() ==> out.outcome()->Ok_0==out.partial()
            && out.partial()@.len()==preorder(entries@,None,0).len() && out.calls().len()==out.partial()@.len()
            && prefix(preorder(entries@,None,0),out.partial(),root,out.calls()),
        out.outcome().is_err() ==> match out.outcome()->Err_0 {
            PlanError::Input(_)=>out.calls().len()==0 && out.partial()@.len()==0,
            PlanError::Tree {index,..}=>index==out.partial()@.len() && index<=out.calls().len()<=index+1
                && prefix(preorder(entries@,None,0),out.partial(),root,out.calls()),
            PlanError::Callback {index,error}=>index==out.partial()@.len() && out.calls().len()==index+1
                && out.calls().last().result==Err(error) && prefix(preorder(entries@,None,0),out.partial(),root,out.calls()),
        },
{
    let mut tree:Tree<N>=Tree::new(domain,parent);let mut items=Vec::new();
    let mut current=host;let ghost initial=host;let ghost mut calls:Seq<Call<T,N,S,H,E>>=Seq::empty();
    proof {empty_chain::<T,N,S,H,E,C>(host,callback);}
    if let Err(error)=append_forest(&mut items,entries,None,0) {
        return Planned {result:Err(PlanError::Input(error)),host:current,calls:Ghost(calls),partial:Ghost(tree)};
    }
    let ghost descriptions=describe(items@);
    assert(descriptions==preorder(entries@,None,0));
    proof {empty_prefix::<T,N,S,H,E>(descriptions,tree,root);}
    let length=items.len();
    let mut contexts:Vec<S>=Vec::with_capacity(length);
    for item in iter: items
        invariant initial==host,length==descriptions.len(),descriptions==preorder(entries@,None,0),contexts.len()<=descriptions.len()<=usize::MAX,iter.index()==contexts.len(),describe(iter.seq())==descriptions,
            tree.wf(),tree.domain_id()==domain,tree.root_id()==parent,tree@.len()==contexts.len(),calls.len()==contexts.len(),
            prefix(descriptions,tree,root,calls),chain(calls,initial,current,callback),
            forall|j:int|0<=j<contexts.len() ==> contexts[j]==calls[j].result->Ok_0.context,
            forall|h:&mut H,t:&T,e:&PreparedEntry,s:&S|callback.requires((h,t,e,s)),
            forall|h:&mut H,t:&T,e:&PreparedEntry,s:&S,r:Result<Prepared<N,S>,E>|callback.ensures((h,t,e,s),r)
                && r.is_ok() && r->Ok_0.allocation.is_some() ==> r->Ok_0.allocation.unwrap().wf(),
    {
        let i=contexts.len();
        assert(item.describe()==descriptions[i as int]);
        let entry=match tree.prepare_entry(item.parent,&item.id,item.enabled) {
            Ok(entry)=>entry,Err(error)=>return Planned {result:Err(PlanError::Tree {index:i,cause:error}),host:current,calls:Ghost(calls),partial:Ghost(tree)},
        };
        let context=match item.parent {None=>&root,Some(p)=>&contexts[p]};
        let ghost before=current;let ghost prepared_entry=entry;let ghost context_value=*context;
        let result=invoke(&mut current,&item.payload,&entry,context,&callback);
        proof {
            let call=Call {before,after:current,input:item.payload,entry:prepared_entry,context:context_value,result};
            assert(matches_input(descriptions[i as int],root,call,calls));
            append_chain(calls,initial,call,callback);
            extend_prefix(descriptions,tree,root,calls,call);
            allocation_wf(call,callback);
            calls=calls.push(call);
        }
        let prepared=match result {
            Ok(value)=>value,Err(error)=>return Planned {result:Err(PlanError::Callback {index:i,error}),host:current,calls:Ghost(calls),partial:Ghost(tree)},
        };
        let ghost previous=tree;
        match tree.insert_entry(entry,prepared.allocation,prepared.data) {
            Ok(_)=>{},Err(error)=>return Planned {result:Err(PlanError::Tree {index:i,cause:error}),host:current,calls:Ghost(calls),partial:Ghost(tree)},
        }
        contexts.push(prepared.context);
        proof {
            assert(calls.drop_last()==calls.take(i as int));
            assert(node_from_call(tree@.last(),calls.last()));
            append_prefix(descriptions,previous,tree,root,calls);
        }
    }
    Planned {partial:Ghost(tree),result:Ok(tree),host:current,calls:Ghost(calls)}
}
}
