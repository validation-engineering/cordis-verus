//! Checked static-host input assembly and declared service selection.
//! Provider/lease truth comes from the embedding graph; this owner checks exact
//! imported slots, declaration coverage, immutable identity and later writes.
use crate::execution::Execution;
use crate::host_context::Association;
use crate::lifecycle_state::services::{NativeReadError, NativeValueError};
use crate::{Binding, Port};
use std::collections::BTreeMap;
use std::sync::Arc;
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn binding_provider(bindings:Seq<Binding>,port:Port)->Option<usize> {
    if exists|i:int|0<=i<bindings.len() && bindings[i].key==port.key && bindings[i].realm==port.realm {
        let i=choose|i:int|0<=i<bindings.len() && bindings[i].key==port.key && bindings[i].realm==port.realm
            && forall|j:int|0<=j<i ==> bindings[j].key!=port.key || bindings[j].realm!=port.realm;
        Some(bindings[i].provider)
    } else {None}
}

fn contains(ports:&[Port],port:Port)->(out:bool)
    ensures out==ports@.contains(port),
{
    let mut i=0;
    while i<ports.len()
        invariant i<=ports.len(),forall|j:int|0<=j<i ==> ports[j]!=port,
        decreases ports.len()-i,
    {if ports[i]==port {return true;}i+=1;}
    false
}
pub struct Import<T> {pub port:Port,pub provider:usize,pub value:Arc<T>}
pub struct Context {owner:usize,generation:u64,association:Association,bindings:Vec<Binding>,provisions:Vec<Port>}
impl Context {
    pub closed spec fn owner_id(&self)->usize {self.owner}
    pub closed spec fn episode(&self)->u64 {self.generation}
    pub closed spec fn link(&self)->Association {self.association}
    pub closed spec fn bindings(&self)->Seq<Binding> {self.bindings@}
    pub closed spec fn provisions(&self)->Seq<Port> {self.provisions@}
    pub fn owner(&self)->(out:usize) ensures out==self.owner_id(), {self.owner}
    pub fn generation(&self)->(out:u64) ensures out==self.episode(), {self.generation}
    pub fn association(&self)->(out:Association) ensures out==self.link(), {self.association}
    pub fn committed(&self)->(out:&[Binding]) ensures out@==self.bindings(), {&self.bindings}
    pub fn provision_ports(&self)->(out:&[Port]) ensures out@==self.provisions(), {&self.provisions}
}
pub struct Values<T> {context:Arc<Context>,slots:BTreeMap<(usize,u64,u64),Arc<T>>}
impl<T> Values<T> {
    pub closed spec fn context_spec(&self)->Context {*self.context}
    pub closed spec fn slots(&self)->Map<(usize,u64,u64),Arc<T>> {self.slots@}
    pub fn context(&self)->(out:Arc<Context>) ensures *out==self.context_spec(), {self.context.clone()}
    pub open spec fn imported(inputs:Seq<Import<T>>,slots:Map<(usize,u64,u64),Arc<T>>)->bool {
        (forall|i:int|0<=i<inputs.len() ==> slots.contains_key((inputs[i].provider,inputs[i].port.key,inputs[i].port.realm))
            && slots[(inputs[i].provider,inputs[i].port.key,inputs[i].port.realm)]==inputs[i].value)
            && slots.dom()==inputs.map(|i:int,input:Import<T>|(input.provider,input.port.key,input.port.realm)).to_set()
    }
    pub fn new<V,C,G,I>(execution:&Execution<V,C,G,I>,owner:usize,generation:u64,expected:Vec<Port>,provisions:Vec<Port>,inputs:Vec<Import<T>>)->(out:Result<Self,Vec<Import<T>>>)
        requires execution.wf(),ensures out.is_err() ==> out->Err_0==inputs,
            out.is_ok() ==> out->Ok_0.context_spec().owner_id()==owner && out->Ok_0.context_spec().episode()==generation && generation>0
                && out->Ok_0.context_spec().link().owns(execution) && execution.origin().is_none()
                && out->Ok_0.context_spec().provisions()==provisions@
                && out->Ok_0.context_spec().bindings()==inputs@.map(|i:int,input:Import<T>|Binding {provider:input.provider,key:input.port.key,realm:input.port.realm})
                && inputs@.map(|i:int,input:Import<T>|input.port).no_duplicates()
                && inputs@.map(|i:int,input:Import<T>|input.port).to_set()==expected@.to_set()
                && Self::imported(inputs@,out->Ok_0.slots()),
    {
        if execution.lifecycle_ticket().is_some() || generation==0 || inputs.len()!=expected.len() {return Err(inputs);}
        let mut i=0;
        while i<inputs.len()
            invariant i<=inputs.len(),inputs.len()==expected.len(),
                forall|k:int|0<=k<i ==> expected@.contains(inputs[k].port),
                forall|j:int,k:int|0<=j<k<i ==> inputs[j].port!=inputs[k].port,
            decreases inputs.len()-i,
        {
            if !contains(&expected,inputs[i].port) {return Err(inputs);}
            let mut j=0;
            while j<i
                invariant j<=i,i<inputs.len(),forall|k:int|0<=k<j ==> inputs[k].port!=inputs[i as int].port,
                decreases i-j,
            {if inputs[j].port==inputs[i].port {return Err(inputs);}j+=1;}
            i+=1;
        }
        let mut ports=Vec::new();let mut i=0;
        while i<inputs.len()
            invariant i<=inputs.len(),ports@==inputs@.take(i as int).map(|i:int,input:Import<T>|input.port),
            decreases inputs.len()-i,
        {ports.push(inputs[i].port);i+=1;}
        assert(ports@==inputs@.map(|i:int,input:Import<T>|input.port));
        let mut i=0;
        while i<expected.len()
            invariant i<=expected.len(),forall|j:int|0<=j<i ==> ports@.contains(expected[j]),
            decreases expected.len()-i,
        {if !contains(&ports,expected[i]) {return Err(inputs);}i+=1;}
        let mut slots=BTreeMap::new();let mut bindings=Vec::new();let mut i=0;
        proof {
            assert(inputs@.take(0).len()==0);
            let keys=inputs@.take(0).map(|i:int,input:Import<T>|(input.provider,input.port.key,input.port.realm));
            assert(keys =~= Seq::<(usize,u64,u64)>::empty());
            assert(keys.to_set() =~= Set::empty());
            assert(slots@.dom() =~= Set::empty());
            assert(Self::imported(inputs@.take(0),slots@));
        }
        while i<inputs.len()
            invariant i<=inputs.len(),
                bindings@==inputs@.take(i as int).map(|i:int,input:Import<T>|Binding {provider:input.provider,key:input.port.key,realm:input.port.realm}),
                Self::imported(inputs@.take(i as int),slots@),
                forall|j:int,k:int|0<=j<k<inputs.len() ==> inputs[j].port!=inputs[k].port,
            decreases inputs.len()-i,
        {
            let input=&inputs[i];let key=(input.provider,input.port.key,input.port.realm);
            let ghost prior=slots@;let ghost prefix=inputs@.take(i as int);
            slots.insert(key,input.value.clone());
            bindings.push(Binding {provider:input.provider,key:input.port.key,realm:input.port.realm});
            proof {
                assert(inputs@.take(i as int+1)==prefix.push(*input));
                assert forall|j:int|0<=j<i implies (inputs[j].provider,inputs[j].port.key,inputs[j].port.realm)!=key by {assert(inputs[j].port!=input.port);}
                let keys=prefix.map(|i:int,input:Import<T>|(input.provider,input.port.key,input.port.realm));
                assert(inputs@.take(i as int+1).map(|i:int,input:Import<T>|(input.provider,input.port.key,input.port.realm)) =~= keys.push(key));
                keys.lemma_push_to_set_commute(key);
                assert(slots@.dom() =~= keys.push(key).to_set());
            }
            i+=1;
        }
        proof {
            assert(inputs@.take(i as int)==inputs@);
            let ports=inputs@.map(|i:int,input:Import<T>|input.port);
            assert(ports.no_duplicates());
            assert(ports.to_set() =~= expected@.to_set()) by {
                assert forall|p:Port|ports.to_set().contains(p) implies expected@.to_set().contains(p) by {
                    let j=choose|j:int|0<=j<ports.len() && ports[j]==p;
                }
                assert forall|p:Port|expected@.to_set().contains(p) implies ports.to_set().contains(p) by {
                    let j=choose|j:int|0<=j<expected.len() && expected[j]==p;
                }
            }
        }
        Ok(Self {context:Arc::new(Context {owner,generation,association:Association::from_execution(execution),bindings,provisions}),slots})
    }
    pub fn own(&self,owner:usize,port:Port)->(out:Option<&Arc<T>>)
        ensures out.is_some()==self.slots().contains_key((owner,port.key,port.realm)),
            out.is_some() ==> *out.unwrap()==self.slots()[(owner,port.key,port.realm)],
    {self.slots.get(&(owner,port.key,port.realm))}
    pub fn provide(&mut self,owner:usize,provisions:&[Port],port:Port,value:Arc<T>)->(out:Result<(),(NativeValueError,Arc<T>)>)
        ensures final(self).context_spec()==old(self).context_spec(),
            out.is_ok() ==> owner==old(self).context_spec().owner_id() && old(self).context_spec().provisions().contains(port)
                && !old(self).slots().contains_key((owner,port.key,port.realm)) && final(self).slots()==old(self).slots().insert((owner,port.key,port.realm),value),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.1==value,
    {
        if owner!=self.context.owner || !contains(&self.context.provisions,port) || !contains(provisions,port) {return Err((NativeValueError::Undeclared,value));}
        let key=(owner,port.key,port.realm);
        if self.slots.contains_key(&key) {return Err((NativeValueError::Duplicate,value));}
        self.slots.insert(key,value);Ok(())
    }
    pub open spec fn provider(&self,port:Port)->Option<usize> {
        if self.context_spec().provisions().contains(port) {Some(self.context_spec().owner_id())}
        else {binding_provider(self.context_spec().bindings(),port)}
    }
    fn select(&self,port:Port)->(out:Option<usize>) ensures out==self.provider(port), {
        if contains(&self.context.provisions,port) {return Some(self.context.owner);}
        let mut i=0;
        while i<self.context.bindings.len()
            invariant i<=self.context.bindings.len(),!self.context_spec().provisions().contains(port),
                forall|j:int|0<=j<i ==> self.context.bindings[j].key!=port.key || self.context.bindings[j].realm!=port.realm,
            decreases self.context.bindings.len()-i,
        {
            let b=self.context.bindings[i];
            if b.key==port.key && b.realm==port.realm {
                proof {let bs=self.context_spec().bindings();
                    assert(exists|j:int|0<=j<bs.len() && bs[j].key==port.key && bs[j].realm==port.realm);
                    let chosen=choose|j:int|0<=j<bs.len() && bs[j].key==port.key && bs[j].realm==port.realm
                        && forall|k:int|0<=k<j ==> bs[k].key!=port.key || bs[k].realm!=port.realm;
                    assert(chosen==i);
                }
                return Some(b.provider);
            }
            i+=1;
        }
        None
    }
    pub fn read(&self,port:Port)->(out:Result<(usize,&Arc<T>),NativeReadError>)
        ensures out.is_ok() ==> self.provider(port)==Some(out->Ok_0.0) && self.slots().contains_key((out->Ok_0.0,port.key,port.realm))
            && *out->Ok_0.1==self.slots()[(out->Ok_0.0,port.key,port.realm)],
            out.is_err() ==> (self.provider(port).is_none() || !self.slots().contains_key((self.provider(port).unwrap(),port.key,port.realm))),
    {
        match self.select(port) {
            None=>Err(NativeReadError {reason:NativeValueError::Undeclared,provider:None}),
            Some(provider)=>match self.slots.get(&(provider,port.key,port.realm)) {
                Some(slot)=>Ok((provider,slot)),None=>Err(NativeReadError {reason:NativeValueError::Missing,provider:Some(provider)}),
            },
        }
    }
}
/// Actual static definition and inherited dependency context, resolved by the
/// same checked realm implementation used for native registration.
pub struct Definition {
    pub owner:usize,pub generation:u64,pub realms:crate::realm_context::RealmContext,
    pub dependencies:Vec<u64>,pub inherited:Vec<Port>,pub provisions:Vec<u64>,
}
impl Definition {
    pub open spec fn dependencies(&self)->Set<Port> {
        self.dependencies@.map(|i:int,key:u64|crate::lifecycle_state::registration::resolved(self.realms.mapping(),key)).to_set()+self.inherited@.to_set()
    }
    pub open spec fn provisions(&self)->Seq<Port> {
        self.provisions@.map(|i:int,key:u64|crate::lifecycle_state::registration::resolved(self.realms.mapping(),key))
    }
    fn resolved_dependencies(&self)->(out:Vec<Port>) ensures out@.to_set()==self.dependencies(), {
        let mut ports=crate::lifecycle_state::registration::resolve_keys(&self.dependencies,self.realms.as_map());
        let ghost initial=ports@.to_set();let mut i=0;
        while i<self.inherited.len()
            invariant i<=self.inherited.len(),ports@.to_set()==initial+self.inherited@.take(i as int).to_set(),
            decreases self.inherited.len()-i,
        {
            let port=self.inherited[i];let ghost before=ports@;
            if !contains(&ports,port) {ports.push(port);proof {before.lemma_push_to_set_commute(port);}}
            proof {
                assert(self.inherited@.take(i as int+1)==self.inherited@.take(i as int).push(port));
                self.inherited@.take(i as int).lemma_push_to_set_commute(port);
                assert(ports@.to_set() =~= initial+self.inherited@.take(i as int+1).to_set());
            }
            i+=1;
        }
        assert(self.inherited@.take(i as int)==self.inherited@);ports
    }
}
impl<T> Values<T> {
    pub fn from_definition<V,C,G,I>(execution:&Execution<V,C,G,I>,definition:Definition,inputs:Vec<Import<T>>)->(out:Result<Self,Vec<Import<T>>>)
        requires execution.wf(),ensures out.is_err() ==> out->Err_0==inputs,
            out.is_ok() ==> out->Ok_0.context_spec().owner_id()==definition.owner && out->Ok_0.context_spec().episode()==definition.generation
                && out->Ok_0.context_spec().link().owns(execution) && execution.origin().is_none() && definition.generation>0
                && out->Ok_0.context_spec().provisions()==definition.provisions()
                && out->Ok_0.context_spec().bindings()==inputs@.map(|i:int,input:Import<T>|Binding {provider:input.provider,key:input.port.key,realm:input.port.realm})
                && inputs@.map(|i:int,input:Import<T>|input.port).to_set()==definition.dependencies()
                && Self::imported(inputs@,out->Ok_0.slots()),
    {
        let expected=definition.resolved_dependencies();
        let provisions=crate::lifecycle_state::registration::resolve_keys(&definition.provisions,definition.realms.as_map());
        Self::new(execution,definition.owner,definition.generation,expected,provisions,inputs)
    }
}

}
