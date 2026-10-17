//! Production plugin registration, realm resolution and invocation provenance.
//! The stored callback is opaque, but it cannot be replaced by a different
//! recipe between root admission and invocation without rejecting the call.
use super::LifecycleState;
use crate::action_ledger::{ActionKind, ActionTicket};
#[cfg(verus_keep_ghost)]
use crate::distinct_ports;
use crate::realm_context::RealmContext;
use crate::reversible_value::function::Body;
use crate::setup_work::{SetupWork, WorkItem, WorkReceipt, WorkTicket};
use crate::{Error, Kernel, Phase, Port};
use std::collections::BTreeMap;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;

pub open spec fn resolved(realms:Map<u64,u64>,key:u64)->Port {
    Port {key,realm:if realms.contains_key(key) {realms[key]} else {0}}
}
pub fn resolve(realms:&BTreeMap<u64,u64>,key:u64)->(out:Port)
    ensures out==resolved(realms@,key),
{
    Port {key,realm:match realms.get(&key) {Some(realm)=>*realm,None=>0}}
}
pub fn resolve_keys(keys:&[u64],realms:&BTreeMap<u64,u64>)->(out:Vec<Port>)
    ensures out@==keys@.map(|_i:int,key:u64| resolved(realms@,key)),
{
    let mut out=Vec::new();let mut i=0;
    while i<keys.len()
        invariant i<=keys.len(),out.len()==i,
            forall|j:int| 0<=j<i ==> out@[j]==resolved(realms@,keys@[j]),
        decreases keys.len()-i,
    {out.push(resolve(realms,keys[i]));i+=1;}
    proof {assert(out@ =~= keys@.map(|_i:int,key:u64| resolved(realms@,key)));}
    out
}
fn has_port(ports:&[Port],port:Port)->(out:bool)
    ensures out==ports@.contains(port),
{
    let mut i=0;
    while i<ports.len()
        invariant i<=ports.len(),forall|j:int| 0<=j<i ==> ports@[j]!=port,
        decreases ports.len()-i,
    {if ports[i]==port {return true;} i+=1;}
    false
}
fn inherit_one(dependencies:&mut Vec<Port>,provisions:&[Port],port:Port)
    ensures distinct_ports(final(dependencies)@)==distinct_ports(old(dependencies)@),
        forall|p:Port| #[trigger] final(dependencies)@.contains(p)==(old(dependencies)@.contains(p)
        || (p==port && !provisions@.contains(port))),
{
    let ghost before=dependencies@;
    if !has_port(provisions,port) && !has_port(dependencies.as_slice(),port) {dependencies.push(port);}
    proof {
        if distinct_ports(before) {
            assert forall|i:int,j:int| 0<=i<j<dependencies.len() implies dependencies@[i]!=dependencies@[j] by {
                if j<before.len() {assert(dependencies@[i]==before[i] && dependencies@[j]==before[j]);}
                else {assert(dependencies@[j]==port);assert(!before.contains(port));assert(before.contains(before[i]));}
            }
        }
        if distinct_ports(dependencies@) {
            assert forall|i:int,j:int| 0<=i<j<before.len() implies before[i]!=before[j] by {
                assert(dependencies@[i]==before[i] && dependencies@[j]==before[j]);
            }
        }
        assert forall|p:Port| #[trigger] dependencies@.contains(p)==(before.contains(p)
            || (p==port && !provisions@.contains(port))) by { }
    }
}
pub open spec fn inherited_at(inherited:Seq<Port>,realms:Map<u64,u64>,p:Port)->bool {
    exists|i:int| 0<=i<inherited.len() && (inherited[i]==p || resolved(realms,inherited[i].key)==p)
}
fn inherit_dependencies(dependencies:&mut Vec<Port>,inherited:&[Port],provisions:&[Port],realms:&BTreeMap<u64,u64>)
    ensures distinct_ports(final(dependencies)@)==distinct_ports(old(dependencies)@),
        forall|p:Port| #[trigger] final(dependencies)@.contains(p)==(old(dependencies)@.contains(p)
        || (!provisions@.contains(p) && inherited_at(inherited@,realms@,p))),
{
    let ghost initial=dependencies@;
    let mut i=0;
    while i<inherited.len()
        invariant i<=inherited.len(),initial==old(dependencies)@,
            distinct_ports(dependencies@)==distinct_ports(initial),
            forall|p:Port| #[trigger] dependencies@.contains(p)==(initial.contains(p)
            || (!provisions@.contains(p) && inherited_at(inherited@.take(i as int),realms@,p))),
        decreases inherited.len()-i,
    {
        let ghost before=dependencies@;
        let port=inherited[i];
        inherit_one(dependencies,provisions,port);
        inherit_one(dependencies,provisions,resolve(realms,port.key));
        proof {
            assert forall|p:Port| inherited_at(inherited@.take(i+1),realms@,p)==(
                inherited_at(inherited@.take(i as int),realms@,p) || port==p || resolved(realms@,port.key)==p) by {
                if inherited_at(inherited@.take(i+1),realms@,p) {
                    let j=choose|j:int| 0<=j<i+1 && (inherited@[j]==p || resolved(realms@,inherited@[j].key)==p);
                    if j<i {assert(inherited@.take(i as int)[j]==inherited@[j]);}
                }
                if inherited_at(inherited@.take(i as int),realms@,p) {
                    let j=choose|j:int| 0<=j<i && (inherited@[j]==p || resolved(realms@,inherited@[j].key)==p);
                    assert(inherited@.take(i+1)[j]==inherited@[j]);
                }
                assert(inherited@.take(i+1)[i as int]==port);
                assert(before.contains(p)==(initial.contains(p)
                    || (!provisions@.contains(p) && inherited_at(inherited@.take(i as int),realms@,p))));
            }
            assert forall|p:Port| #[trigger] dependencies@.contains(p)==(initial.contains(p)
                || (!provisions@.contains(p) && inherited_at(inherited@.take(i+1),realms@,p))) by {
                assert(before.contains(p)==(initial.contains(p)
                    || (!provisions@.contains(p) && inherited_at(inherited@.take(i as int),realms@,p))));
            }
        }
        i+=1;
    }
    proof {assert(inherited@.take(i as int)==inherited@);}
}

impl Kernel {
    /// Read the authoritative declarations, including inherited/isolated ports.
    pub fn dependency_ports(&self,id:usize)->(out:Vec<Port>)
        ensures forall|p:Port| out@.contains(p)==(self.registered(id) && self.paper().fibers[id].dependencies.contains(p)),
    {
        let mut out=Vec::new();
        if !self.contains(id) {return out;}
        let mut i=0;
        while i<self.declarations.len()
            invariant i<=self.declarations.len(),self.registered(id),
                forall|p:Port| out@.contains(p)==(exists|j:int| 0<=j<i && self.declarations@[j].owner==id
                    && !self.declarations@[j].provides && self.declarations@[j].port==p),
            decreases self.declarations.len()-i,
        {
            let d=self.declarations[i];
            let ghost before=out@;
            if d.owner==id && !d.provides {out.push(d.port);}
            proof {
                assert forall|p:Port| out@.contains(p)==(exists|j:int| 0<=j<i+1 && self.declarations@[j].owner==id
                    && !self.declarations@[j].provides && self.declarations@[j].port==p) by {
                    if exists|j:int| 0<=j<i+1 && self.declarations@[j].owner==id
                        && !self.declarations@[j].provides && self.declarations@[j].port==p {
                        let j=choose|j:int| 0<=j<i+1 && self.declarations@[j].owner==id
                            && !self.declarations@[j].provides && self.declarations@[j].port==p;
                        if j<i {assert(before.contains(p));}
                    }
                    if before.contains(p) {
                        let j=choose|j:int| 0<=j<i && self.declarations@[j].owner==id
                            && !self.declarations@[j].provides && self.declarations@[j].port==p;
                        assert(j<i+1);
                    }
                }
            }
            i+=1;
        }
        out
    }
}

pub struct PluginDefinition<T> {dependencies:Vec<u64>,provisions:Vec<u64>,payload:T}
impl<T> PluginDefinition<T> {
    pub closed spec fn dependencies(&self)->Seq<u64> {self.dependencies@}
    pub closed spec fn provisions(&self)->Seq<u64> {self.provisions@}
    pub closed spec fn payload(&self)->T {self.payload}
    pub fn new(dependencies:Vec<u64>,provisions:Vec<u64>,payload:T)->(out:Self)
        ensures out.dependencies()==dependencies@,out.provisions()==provisions@,out.payload()==payload,
    {Self {dependencies,provisions,payload}}
    pub fn into_payload(self)->(out:T) ensures out==self.payload(), {self.payload}
}

/// Created only by successful registration of this actual callback payload.
pub struct RegisteredPlugin<T> {
    domain:u64,id:usize,parent:Option<usize>,anchor:Port,realms:RealmContext,
    dependencies:Vec<Port>,provisions:Vec<Port>,revision:u64,payload:T,
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct ChildIdentity {domain:u64,parent:usize,id:usize}
impl ChildIdentity {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn owner(&self)->usize {self.parent}
    pub closed spec fn child(&self)->usize {self.id}
    pub fn id(&self)->(out:usize) ensures out==self.child(), {self.id}
}
pub struct RegisteredInvocation<A> {domain:u64,id:usize,revision:u64,lifecycle:ActionTicket,item:WorkItem<A>}
impl<A> RegisteredInvocation<A> {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn owner(&self)->usize {self.id}
    pub closed spec fn version(&self)->u64 {self.revision}
    pub closed spec fn work(&self)->WorkItem<A> {self.item}
    pub closed spec fn lifecycle(&self)->ActionTicket {self.lifecycle}
    pub fn lifecycle_ticket(&self)->(out:ActionTicket) ensures out==self.lifecycle(), {self.lifecycle}
    pub fn ticket(&self)->(out:WorkTicket) ensures out==self.work().origin(), {self.item.ticket()}
    pub(crate) fn into_work(self)->(out:WorkItem<A>) ensures out==self.work(), {self.item}
}
impl<T> RegisteredPlugin<T> {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn owner(&self)->usize {self.id}
    pub closed spec fn parent_id(&self)->Option<usize> {self.parent}
    pub closed spec fn anchor_port(&self)->Port {self.anchor}
    pub closed spec fn realms(&self)->Map<u64,u64> {self.realms.mapping()}
    pub fn realm_context(&self)->(out:RealmContext) ensures out.mapping()==self.realms(), {self.realms.clone()}
    pub closed spec fn dependencies_spec(&self)->Seq<Port> {self.dependencies@}
    pub closed spec fn provisions_spec(&self)->Seq<Port> {self.provisions@}
    pub closed spec fn version(&self)->u64 {self.revision}
    pub closed spec fn payload(&self)->T {self.payload}
    pub open spec fn same_identity(&self,prior:&Self)->bool {
        self.domain_id()==prior.domain_id() && self.owner()==prior.owner() && self.parent_id()==prior.parent_id()
            && self.anchor_port()==prior.anchor_port() && self.realms()==prior.realms() && self.dependencies_spec()==prior.dependencies_spec()
            && self.provisions_spec()==prior.provisions_spec()
    }
    pub fn domain_id_exec(&self)->(out:u64) ensures out==self.domain_id(), {self.domain}
    pub fn id(&self)->(out:usize) ensures out==self.owner(), {self.id}
    pub fn parent(&self)->(out:Option<usize>) ensures out==self.parent_id(), {self.parent}
    pub fn anchor(&self)->(out:Port) ensures out==self.anchor_port(), {self.anchor}
    pub fn dependencies(&self)->(out:&[Port]) ensures out@==self.dependencies_spec(), {self.dependencies.as_slice()}
    pub fn provisions_vec(&self)->(out:Vec<Port>) ensures out@==self.provisions_spec(), {self.provisions.clone()}
    pub fn provisions(&self)->(out:&[Port]) ensures out@==self.provisions_spec(), {self.provisions.as_slice()}
    pub fn child_identity(&self)->(out:Option<ChildIdentity>)
        ensures out.is_some()==self.parent_id().is_some(),out.is_some() ==> out.unwrap().domain_id()==self.domain_id()
            && out.unwrap().owner()==self.parent_id().unwrap() && out.unwrap().child()==self.owner(),
    {self.parent.map(|parent:usize| -> (out:ChildIdentity)
        ensures out.domain_id()==self.domain_id() && out.owner()==parent && out.child()==self.owner(),
        {ChildIdentity {domain:self.domain,parent,id:self.id}})}
    pub fn payload_ref(&self)->(out:&T) ensures *out==self.payload(), {&self.payload}
    pub fn revision(&self)->(out:u64) ensures out==self.version(), {self.revision}
    /// Explicit dependencies precede inherited aliases. Return the first
    /// registered port for this key, never a port supplied at invocation time.
    pub fn dependency_port(&self,key:u64)->(out:Option<Port>)
        ensures out.is_some()==(exists|i:int| 0<=i<self.dependencies_spec().len() && self.dependencies_spec()[i].key==key),
            out.is_some() ==> out.unwrap().key==key && self.dependencies_spec().contains(out.unwrap())
                && exists|i:int| 0<=i<self.dependencies_spec().len() && self.dependencies_spec()[i]==out.unwrap()
                    && forall|j:int| 0<=j<i ==> self.dependencies_spec()[j].key!=key,
    {
        let mut i=0;
        while i<self.dependencies.len()
            invariant i<=self.dependencies.len(),forall|j:int| 0<=j<i ==> self.dependencies_spec()[j].key!=key,
            decreases self.dependencies.len()-i,
        {let port=self.dependencies[i];if port.key==key {assert(self.dependencies_spec().contains(port));return Some(port);}i+=1;}
        None
    }
    pub fn can_replace(&self)->(out:bool) ensures out==(self.version()<u64::MAX), {self.revision<u64::MAX}
    pub fn can_replace_count(&self,count:u64)->(out:bool)
        ensures out==(self.version()+count<=u64::MAX),
    {count<=u64::MAX-self.revision}
    pub fn replace(&mut self,payload:T)->(out:Result<T,T>)
        ensures final(self).same_identity(old(self)),out.is_ok()==(old(self).version()<u64::MAX),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==payload,
            out.is_ok() ==> out->Ok_0==old(self).payload() && final(self).payload()==payload
                && final(self).version()==old(self).version()+1,
    {
        if self.revision==u64::MAX {return Err(payload);}
        let mut previous=payload;core::mem::swap(&mut self.payload,&mut previous);
        self.revision+=1;Ok(previous)
    }
    /// Call the stored native FnMut itself, using the actual admitted argument.
    /// No adapter-supplied replacement callback or expected outcome is input.
    pub fn call<A,R>(&mut self,invocation:RegisteredInvocation<A>)->(out:Result<WorkReceipt<R>,RegisteredInvocation<A>>)
        where T:FnMut(A)->R,
        requires old(self).payload().requires((invocation.work().value(),)),
        ensures final(self).same_identity(old(self)),final(self).version()==old(self).version(),
            out.is_ok()==(invocation.domain_id()==old(self).domain_id() && invocation.owner()==old(self).owner()
                && invocation.version()==old(self).version()),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==invocation,
            out.is_ok() ==> out->Ok_0.origin()==invocation.work().origin()
                && old(self).payload().ensures((invocation.work().value(),),out->Ok_0.value()),
    {
        if invocation.domain!=self.domain || invocation.id!=self.id || invocation.revision!=self.revision {return Err(invocation);}
        Ok(invocation.item.run(&mut self.payload))
    }


}

impl<C,F> RegisteredPlugin<Body<C,F>> {
    /// Opaque callbacks retain the original admission/version checks. A stored
    /// finite body cannot accidentally be dispatched through this callback path.
    pub fn call_opaque<A,O>(&mut self,invocation:RegisteredInvocation<A>)->(out:Result<WorkReceipt<O>,RegisteredInvocation<A>>)
        where C:FnMut(A)->O,
        requires old(self).payload().callback_requires::<A,O>(invocation.work().value()),
        ensures final(self).same_identity(old(self)),final(self).version()==old(self).version(),
            out.is_ok()==(invocation.domain_id()==old(self).domain_id() && invocation.owner()==old(self).owner()
                && invocation.version()==old(self).version() && old(self).payload() is Callback),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==invocation,
            out.is_ok() ==> out->Ok_0.origin()==invocation.work().origin()
                && old(self).payload().callback_ensures::<A,O>(invocation.work().value(),out->Ok_0.value()),
    {
        if invocation.domain!=self.domain || invocation.id!=self.id || invocation.revision!=self.revision {return Err(invocation);}
        match &mut self.payload {Body::Callback(callback)=>Ok(invocation.item.run(callback)),Body::Value(_)|Body::Services(_)|Body::Managed(_)=>Err(invocation)}
    }
}

pub open spec fn registered_dependencies(state:crate::refinement::State,parent:Option<usize>,keys:Seq<u64>,provided:Seq<u64>,realms:Map<u64,u64>,p:Port)->bool {
    keys.map(|_i:int,key:u64|resolved(realms,key)).contains(p)
        || (!provided.map(|_i:int,key:u64|resolved(realms,key)).contains(p) && parent.is_some()
            && (state.fibers[parent.unwrap()].dependencies.contains(p)
                || exists|q:Port| state.fibers[parent.unwrap()].dependencies.contains(q) && resolved(realms,q.key)==p))
}
impl LifecycleState {
    /// Revalidate a not-yet-executed root against the live lifecycle, rather
    /// than treating its earlier admission as permission for a later episode.
    pub open spec fn root_invocation_enabled(&self,ticket:ActionTicket)->bool {
        ticket.domain==self.protocol().domain_id() && ticket.kind==ActionKind::Setup
            && self.control().generation_of(ticket.id)==Some(ticket.generation)
            && self.protocol().recorded(ticket) && self.control().phase_of(ticket.id)==Some(Phase::Loading)
            && !self.control().is_retired(ticket.id)
    }
    pub fn accepts_root_invocation(&self,ticket:ActionTicket)->(out:bool)
        requires self.wf(), ensures out==self.root_invocation_enabled(ticket),
    {
        ticket.domain==self.domain() && ticket.kind==ActionKind::Setup
            && self.kernel.episode_generation(ticket.id)==Some(ticket.generation)
            && self.actions.pending_matches(ticket) && self.kernel.phase(ticket.id)==Some(Phase::Loading)
            && !self.kernel.retired(ticket.id)
    }
    /// Exact registration domain, including the host's stricter parent policy.
    /// Dependency availability is checked at Begin, not registration.
    pub open spec fn registration_enabled<T>(&self,parent:Option<usize>,realms:Map<u64,u64>,anchor:Port,definition:&PluginDefinition<T>)->bool {
        let provisions=definition.provisions().map(|_i:int,key:u64|resolved(realms,key)).push(anchor);
        &&& parent.is_some() ==> self.control().registered(parent.unwrap())
            && !self.control().is_retired(parent.unwrap()) && self.control().phase_of(parent.unwrap())!=Some(Phase::Unloading)
        &&& self.control().next_id()<usize::MAX
        &&& distinct_ports(definition.dependencies().map(|_i:int,key:u64|resolved(realms,key)))
        &&& distinct_ports(provisions)
        &&& crate::refinement::insertion_domain(self.control().paper(),parent,ISet::new(|p:Port|provisions.contains(p)))
    }
    /// Resolve declared keys, inherit the parent's actual dependencies, reserve
    /// the private anchor, insert the real node and retain its actual recipe.
    pub fn register_plugin<T>(&mut self,parent:Option<usize>,realms:&BTreeMap<u64,u64>,anchor:Port,definition:PluginDefinition<T>)
        ->(out:Result<RegisteredPlugin<T>,(Error,PluginDefinition<T>)>)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).protocol().same(&old(self).protocol()),
            out.is_ok()==old(self).registration_enabled(parent,realms@,anchor,&definition),
            out.is_err() ==> final(self).same(old(self)) && out->Err_0.1==definition,
            out.is_ok() ==> {
                let plugin=out->Ok_0;
                &&& plugin.domain_id()==old(self).protocol().domain_id() && plugin.owner()==old(self).control().next_id()
                &&& plugin.parent_id()==parent && plugin.anchor_port()==anchor && plugin.realms()==realms@ && plugin.version()==0 && plugin.payload()==definition.payload()
                &&& plugin.provisions_spec()==definition.provisions().map(|_i:int,key:u64|resolved(realms@,key))
                &&& crate::refinement::step(old(self).control().paper(),final(self).control().paper(),plugin.owner(),crate::refinement::Rule::Insert)
                &&& final(self).control().paper().fibers[plugin.owner()].parent==parent
                &&& forall|p:Port| #[trigger] plugin.dependencies_spec().contains(p)==registered_dependencies(old(self).control().paper(),parent,definition.dependencies(),definition.provisions(),realms@,p)
                &&& forall|p:Port| #[trigger] final(self).control().paper().fibers[plugin.owner()].dependencies.contains(p)==plugin.dependencies_spec().contains(p)
                &&& forall|p:Port| #[trigger] final(self).control().paper().fibers[plugin.owner()].provisions.contains(p)==(plugin.provisions_spec().contains(p) || p==anchor)
            },
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {reveal(Kernel::unchanged);self.actions.same_reflexive();}
        if let Some(id)=parent {
            if !self.kernel.contains(id) {return Err((Error::Unknown,definition));}
            if self.kernel.retired(id) {return Err((Error::Retired,definition));}
            if self.kernel.phase(id)==Some(Phase::Unloading) {return Err((Error::InvalidState,definition));}
        }
        let mut dependencies=resolve_keys(definition.dependencies.as_slice(),realms);
        let provisions=resolve_keys(definition.provisions.as_slice(),realms);
        if let Some(id)=parent {
            let inherited=self.kernel.dependency_ports(id);
            inherit_dependencies(&mut dependencies,inherited.as_slice(),provisions.as_slice(),realms);
            proof {
                assert forall|p:Port| inherited_at(inherited@,realms@,p)==(
                    self.kernel.paper().fibers[id].dependencies.contains(p)
                        || exists|q:Port| self.kernel.paper().fibers[id].dependencies.contains(q) && resolved(realms@,q.key)==p) by {
                    if inherited_at(inherited@,realms@,p) {
                        let j=choose|j:int| 0<=j<inherited.len() && (inherited@[j]==p || resolved(realms@,inherited@[j].key)==p);
                        assert(inherited@.contains(inherited@[j]));
                    }
                    if self.kernel.paper().fibers[id].dependencies.contains(p) {
                        assert(inherited@.contains(p));
                        let j=choose|j:int| 0<=j<inherited.len() && inherited@[j]==p;
                        assert(inherited_at(inherited@,realms@,p));
                    }
                    if exists|q:Port| self.kernel.paper().fibers[id].dependencies.contains(q) && resolved(realms@,q.key)==p {
                        let q=choose|q:Port| self.kernel.paper().fibers[id].dependencies.contains(q) && resolved(realms@,q.key)==p;
                        assert(inherited@.contains(q));
                        let j=choose|j:int| 0<=j<inherited.len() && inherited@[j]==q;
                        assert(inherited_at(inherited@,realms@,p));
                    }
                }
            }
        }
        proof {
            assert forall|p:Port| #[trigger] dependencies@.contains(p)==registered_dependencies(self.control().paper(),parent,definition.dependencies(),definition.provisions(),realms@,p) by { }
        }
        let domain=self.domain();
        let mut kernel_provisions=provisions.clone();kernel_provisions.push(anchor);
        let ghost reserved=kernel_provisions@;
        proof {
            self.kernel.paper_insert_domain(parent,dependencies@,reserved);
            assert(self.control().insert_enabled(parent,dependencies@,reserved)==self.registration_enabled(parent,realms@,anchor,&definition));
        }
        let id=match self.insert(parent,dependencies.clone(),kernel_provisions) {
            Ok(id)=>id,Err(error)=>return Err((error,definition)),
        };
        proof {
            assert(domain==old(self).protocol().domain_id());
            assert(id==old(self).control().next_id());
            assert(crate::refinement::step(old(self).control().paper(),self.control().paper(),id,crate::refinement::Rule::Insert));
            assert(self.control().paper().fibers[id].parent==parent);
            assert(provisions@==definition.provisions().map(|_i:int,key:u64|resolved(realms@,key)));
            assert forall|p:Port| #[trigger] dependencies@.contains(p)==registered_dependencies(old(self).control().paper(),parent,definition.dependencies(),definition.provisions(),realms@,p) by { }
            assert forall|p:Port| #[trigger] self.control().paper().fibers[id].dependencies.contains(p)==dependencies@.contains(p) by { }
            assert forall|p:Port| #[trigger] self.control().paper().fibers[id].provisions.contains(p)==(provisions@.contains(p) || p==anchor) by {
                assert(self.control().paper().fibers[id].provisions.contains(p)==reserved.contains(p));
                vstd::seq_lib::lemma_seq_contains_after_push(provisions@,anchor,p);
            }
        }
        Ok(RegisteredPlugin {domain,id,parent,anchor,realms:RealmContext::from_map(realms.clone()),dependencies,provisions,revision:0,payload:definition.payload})
    }

    pub fn admit_registered_root<T,C,G,A>(&self,plugin:&RegisteredPlugin<T>,work:&mut SetupWork<C,G>,argument:A)
        ->(out:Result<RegisteredInvocation<A>,A>)
        requires self.wf(),old(work).wf(),
        ensures final(work).link()==old(work).link(),final(work).origin()==old(work).origin(), final(work).domain_id()==old(work).domain_id(), final(work).accepts()==old(work).accepts(), final(work).is_closed()==old(work).is_closed(), final(work).wf(),out.is_err() ==> *final(work)==*old(work) && out->Err_0==argument,
            out.is_ok() ==> out->Ok_0.domain_id()==plugin.domain_id() && out->Ok_0.owner()==plugin.owner()
                && out->Ok_0.version()==plugin.version() && out->Ok_0.work().value()==argument
                && out->Ok_0.lifecycle()==old(work).origin().unwrap()
                && self.root_invocation_enabled(out->Ok_0.lifecycle()) && old(work).accepts()
                && old(work).origin().is_some() && old(work).origin().unwrap().id==plugin.owner()
                && old(work).origin().unwrap().domain==self.protocol().domain_id()
                && self.control().generation_of(plugin.owner())==Some(old(work).origin().unwrap().generation)
                && self.protocol().recorded(old(work).origin().unwrap())
                && final(work).root_status()==crate::setup_work::RootStatus::Queued
                && out->Ok_0.work().origin().domain_id()==old(work).domain_id()
                && out->Ok_0.work().origin().request_id()==0 && out->Ok_0.work().origin().request_kind()==crate::setup_work::WorkKind::Root,
    {
        let ticket=match work.lifecycle_ticket() {Some(ticket)=>ticket,None=>return Err(argument)};
        if plugin.domain!=self.domain() || ticket.domain!=plugin.domain || ticket.id!=plugin.id
            || ticket.kind!=ActionKind::Setup || self.kernel.episode_generation(plugin.id)!=Some(ticket.generation)
            || !self.accepts_root_invocation(ticket) || !work.accepting_now() {return Err(argument);}
        match work.issue_root(argument) {
            Ok(item)=>Ok(RegisteredInvocation {domain:plugin.domain,id:plugin.id,revision:plugin.revision,lifecycle:ticket,item}),
            Err(argument)=>Err(argument),
        }
    }

    /// Retire only the actual registered child named by its private identity.
    /// Already removed children are an idempotent stutter, not a new release.
    pub fn retire_child(&mut self,child:ChildIdentity)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),out.is_err() ==> final(self).same(old(self)),
            final(self).protocol().same(&old(self).protocol()),
            out.is_ok() ==> child.domain_id()==old(self).protocol().domain_id()
                && (if old(self).control().registered(child.child()) {
                    old(self).control().paper().fibers[child.child()].parent==Some(child.owner())
                        && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),child.child(),crate::refinement::Rule::Retire)
                } else {final(self).same(old(self))}),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {reveal(Kernel::unchanged);self.actions.same_reflexive();}
        if child.domain!=self.domain() {return Err(Error::InvalidState);}
        if !self.kernel.contains(child.id) {return Ok(());}
        if self.kernel.nodes[child.id].parent!=Some(child.parent) {return Err(Error::InvalidState);}
        self.retire(child.id)
    }
}

}

#[path = "child_slot.rs"]
pub mod child;

#[path = "shared_child.rs"]
pub mod shared_child;
