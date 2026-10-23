//! Actual reference-owner transitions, with the protocol cut read by each guard.
//! Each cut is an authentic Node history, not a fabricated common clock. The
//! reference history never runs or interprets the interiors of a foreign T.
use super::{Claim, HostSnapshot};
#[cfg(verus_keep_ghost)]
use crate::node_runtime::handles;
use crate::node_runtime::history as node;
use vstd::prelude::*;
verus! {
pub struct Observation<T> {
    pub domain:u64,pub next:u64,pub objects:Map<u64,T>,pub fibers:Map<usize,u64>,pub claims:Map<usize,Claim>,pub issued:Map<u64,T>,
}
impl<T> Observation<T> {
    pub open spec fn empty(domain:u64)->Self {
        Self {domain,next:1,objects:Map::empty(),fibers:Map::empty(),claims:Map::empty(),issued:Map::empty()}
    }
}
#[allow(inconsistent_fields)]
pub enum Event<T> {
    Issue {value:T},Bind {id:usize,key:u64,node:node::History},Unbind {id:usize,node:node::History},
    Begin {claim:Claim,node:node::History},Finish {claim:Claim,node:node::History},Remove {id:u64,node:node::History},
}
pub open spec fn protocol<T>(a:Observation<T>,h:node::History)->bool {
    h.valid() && h.states.last().control.protocol().domain_id()==a.domain
}
#[verifier::opaque]
pub open spec fn step<T>(a:Observation<T>,b:Observation<T>,event:Event<T>)->bool {
    match event {
        Event::Issue {value}=>a.next<u64::MAX && !a.issued.contains_key(a.next)
            && b==(Observation {next:(a.next+1) as u64,objects:a.objects.insert(a.next,value),issued:a.issued.insert(a.next,value),..a}),
        Event::Bind {id,key,node}=>protocol(a,node) && node.states.last().interfaces.contains_key(id)
            && a.objects.contains_key(key) && !a.fibers.contains_key(id)
            && b==(Observation {fibers:a.fibers.insert(id,key),..a}),
        Event::Unbind {id,node}=>protocol(a,node) && !node.states.last().interfaces.contains_key(id) && !a.claims.contains_key(id)
            && b==(Observation {fibers:a.fibers.remove(id),..a}),
        Event::Begin {claim,node}=>protocol(a,node) && claim.ticket.domain==a.domain
            && node.states.last().control.protocol().recorded(claim.ticket)
            && a.fibers.contains_pair(claim.ticket.id,claim.fiber) && a.objects.contains_key(claim.recipe)
            && !a.claims.contains_key(claim.ticket.id)
            && b==(Observation {claims:a.claims.insert(claim.ticket.id,claim),..a}),
        Event::Finish {claim,node}=>protocol(a,node) && !node.states.last().control.protocol().recorded(claim.ticket)
            && a.claims.contains_pair(claim.ticket.id,claim)
            && b==(Observation {claims:a.claims.remove(claim.ticket.id),..a}),
        Event::Remove {id,node}=>protocol(a,node) && !handles::held(node.states.last().store,id)
            && (forall|owner:usize|a.fibers.contains_key(owner) ==> a.fibers[owner]!=id)
            && (forall|owner:usize|a.claims.contains_key(owner) ==> a.claims[owner].recipe!=id)
            && b==(Observation {objects:a.objects.remove(id),..a}),
    }
}
pub struct History<T> {pub states:Seq<Observation<T>>,pub events:Seq<Event<T>>}
impl<T> History<T> {
    pub open spec fn valid(&self)->bool {
        self.states.len()==self.events.len()+1 && self.states[0]==Observation::empty(self.states[0].domain)
            && forall|i:int|0<=i<self.events.len() ==> #[trigger] step(self.states[i],self.states[i+1],self.events[i])
    }
    pub open spec fn append(&self,state:Observation<T>,event:Event<T>)->Self {Self {states:self.states.push(state),events:self.events.push(event)}}
    pub proof fn extended(&self,state:Observation<T>,event:Event<T>)
        requires self.valid(),step(self.states.last(),state,event),ensures self.append(state,event).valid(),
    {
        assert forall|i:int|0<=i<self.events.len()+1 implies #[trigger] step(self.append(state,event).states[i],self.append(state,event).states[i+1],self.append(state,event).events[i]) by {
            if i<self.events.len() {assert(step(self.states[i],self.states[i+1],self.events[i]));}
        }
    }
    /// A live reference has an actual issuance in this owner's history. Removal
    /// and callback completion cannot reinsert a displaced reference or reuse ID.
    pub proof fn object_origin(&self,end:int,key:u64)->(at:int)
        requires self.valid(),0<=end<self.states.len(),self.states[end].objects.contains_key(key),
        ensures 0<=at<end,self.events[at] is Issue,self.states[at].next==key,
            self.events[at]->Issue_value==self.states[end].objects[key],
        decreases end,
    {
        assert(end>0);let i=end-1;assert(0<=i<self.events.len());assert(step(self.states[i],self.states[i+1],self.events[i]));reveal(step);
        if self.events[i] is Issue && self.states[i].next==key {i} else {self.object_origin(i,key)}
    }
    /// A retained invocation has a real guard read of a pending ticket, Fiber
    /// and recipe. This is provenance of the dispatched references, not success
    /// or termination of the callback using them.
    pub proof fn claim_origin(&self,end:int,id:usize)->(at:int)
        requires self.valid(),0<=end<self.states.len(),self.states[end].claims.contains_key(id),
        ensures 0<=at<end,self.events[at] is Begin,
            self.events[at]->Begin_claim==self.states[end].claims[id],
            protocol(self.states[at],self.events[at]->Begin_node),
            self.events[at]->Begin_node.states.last().control.protocol().recorded(self.states[end].claims[id].ticket),
        decreases end,
    {
        assert(end>0);let i=end-1;assert(0<=i<self.events.len());assert(step(self.states[i],self.states[i+1],self.events[i]));reveal(step);
        if self.events[i] is Begin && self.events[i]->Begin_claim.ticket.id==id {i} else {self.claim_origin(i,id)}
    }
}
impl<T> HostSnapshot<T> {
    pub proof fn production_trace(&self)
        requires self.certified(),ensures self.bridge().valid(),crate::node_runtime::production::interpreted(self.native()),
            forall|key:u64|self.objects().contains_key(key) ==> exists|at:int|0<=at<self.bridge().events.len()
                && self.bridge().events[at] is Issue && self.bridge().states[at].next==key
                && self.bridge().events[at]->Issue_value==self.objects()[key],
            forall|id:usize|self.bridge().states.last().claims.contains_key(id) ==> exists|at:int|0<=at<self.bridge().events.len()
                && self.bridge().events[at] is Begin && self.bridge().events[at]->Begin_claim==self.bridge().states.last().claims[id]
                && self.bridge().events[at]->Begin_node.states.last().control.protocol().recorded(self.bridge().states.last().claims[id].ticket),
    {
        self.native().production_trace();
        assert forall|id:usize|self.bridge().states.last().claims.contains_key(id) implies exists|at:int|0<=at<self.bridge().events.len()
                && self.bridge().events[at] is Begin && self.bridge().events[at]->Begin_claim==self.bridge().states.last().claims[id]
                && self.bridge().events[at]->Begin_node.states.last().control.protocol().recorded(self.bridge().states.last().claims[id].ticket) by {
            let at=self.bridge().claim_origin(self.bridge().states.len() as int-1,id);
        }
        assert forall|key:u64|self.objects().contains_key(key) implies exists|at:int|0<=at<self.bridge().events.len()
                && self.bridge().events[at] is Issue && self.bridge().states[at].next==key
                && self.bridge().events[at]->Issue_value==self.objects()[key] by {
            let at=self.bridge().object_origin(self.bridge().states.len() as int-1,key);
        }
    }
}
}
