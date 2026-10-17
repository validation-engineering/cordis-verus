//! Immutable provenance of the actual Begin capture. All fields are ghost
//! data: no extra Arc owners, copied runtime tables or historical allocations.
//! This is not an authenticity token for arbitrary same-domain host instances.
#[cfg(verus_keep_ghost)]
use super::NativePublication;
#[cfg(verus_keep_ghost)]
use crate::action_ledger::ActionKind;
use crate::action_ledger::ActionTicket;
use crate::{Binding, Kernel, Port};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
pub struct Source<T> {pub origin:ActionTicket,pub values:Map<(u64,u64),Arc<T>>}
pub open spec fn sources<T>(entries:Map<usize,NativePublication<T>>)->Map<usize,Source<T>> {
    Map::new(entries.dom(),|id:usize| Source {origin:entries[id].origin(),values:entries[id].values()})
}
pub struct Capture<T> {
    pub origin:ActionTicket,
    pub work_domain:u64,
    pub realms:Map<u64,u64>,
    pub anchor:Port,
    pub control:Kernel,
    pub provisions:Seq<Port>,
    pub bindings:Seq<Binding>,
    pub imports:Map<(usize,u64,u64),Arc<T>>,
    pub sources:Map<usize,Source<T>>,
}
impl<T> Capture<T> {
    pub open spec fn available(&self,provider:usize,port:Port)->bool {
        self.sources.contains_key(provider)
            && self.control.generation_of(provider)==Some(self.sources[provider].origin.generation)
            && self.sources[provider].values.contains_key((port.key,port.realm))
    }
    pub open spec fn wf(&self)->bool {
        &&& self.control.wf() && self.origin.kind==ActionKind::Setup
        &&& self.control.generation_of(self.origin.id)==Some(self.origin.generation)
        &&& forall|id:usize| #[trigger] self.sources.contains_key(id) ==> self.sources[id].origin.id==id
            && self.sources[id].origin.domain==self.origin.domain && self.sources[id].origin.kind==ActionKind::Setup
        &&& forall|b:Binding| self.bindings.contains(b)==self.control.binding_recorded(self.origin.id,b)
        &&& forall|key:(usize,u64,u64)| #[trigger] self.imports.contains_key(key)==(
            self.bindings.contains(Binding {provider:key.0,key:key.1,realm:key.2})
                && self.available(key.0,Port {key:key.1,realm:key.2}))
        &&& forall|key:(usize,u64,u64)| #[trigger] self.imports.contains_key(key) ==>
            self.imports[key]==self.sources[key.0].values[(key.1,key.2)]
    }
    /// Import lookup is complete and keeps the actual captured provider slot,
    /// even if today's target or publication table has changed.
    pub proof fn dependency(&self,b:Binding)
        requires self.wf(),self.bindings.contains(b),
        ensures self.imports.contains_key((b.provider,b.key,b.realm))==self.available(b.provider,Port {key:b.key,realm:b.realm}),
            self.imports.contains_key((b.provider,b.key,b.realm)) ==> self.imports[(b.provider,b.key,b.realm)]==self.sources[b.provider].values[(b.key,b.realm)],
    {}
}
}
