//! Host object identity and callback dispatch on the actual Node owner.
//! T is the adapter's real retained reference (a weak Node-API reference in JS).
//! Payload interiors and foreign-runtime reference dereferencing are boundaries.
use super::*;
#[path = "node_bridge_history.rs"]
pub mod trace;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct ObjectKey {domain:u64,id:u64}
impl ObjectKey {
    pub closed spec fn number(&self)->u64 {self.id}
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    #[verifier::when_used_as_spec(number)]
    pub fn id(&self)->(out:u64) ensures out==self.number(), {self.id}
    #[verifier::when_used_as_spec(domain_id)]
    pub fn domain(&self)->(out:u64) ensures out==self.domain_id(), {self.domain}
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum BridgeError {Domain,Capacity,Unknown,Bound,Retained,Stale,Busy}
#[allow(dead_code)]
pub struct Call {ticket:ActionTicket,fiber:ObjectKey,recipe:ObjectKey,origin:Ghost<History>}
impl Call {
    pub closed spec fn ticket_spec(&self)->ActionTicket {self.ticket}
    pub closed spec fn fiber_spec(&self)->ObjectKey {self.fiber}
    pub closed spec fn recipe_spec(&self)->ObjectKey {self.recipe}
    pub closed spec fn origin(&self)->History {self.origin@}
    pub open spec fn certified(&self)->bool {
        self.origin().valid() && self.origin().states.last().control.protocol().recorded(self.ticket_spec())
            && self.fiber_spec().domain()==self.ticket_spec().domain && self.recipe_spec().domain()==self.ticket_spec().domain
    }
    pub fn ticket(&self)->(out:ActionTicket) ensures out==self.ticket_spec(), {self.ticket}
    pub fn fiber(&self)->(out:ObjectKey) ensures out==self.fiber_spec(), {self.fiber}
    pub fn recipe(&self)->(out:ObjectKey) ensures out==self.recipe_spec(), {self.recipe}
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Claim {pub ticket:ActionTicket,pub fiber:u64,pub recipe:u64}
/// Issued IDs are never reused. The real payload map is private; the ghost map
/// remembers issuance only for proofs and is erased in production.
#[allow(dead_code)]
pub struct Bridge<T> {
    domain:u64,next:u64,objects:BTreeMap<u64,T>,fibers:BTreeMap<usize,u64>,claims:BTreeMap<usize,Claim>,
    issued:Ghost<Map<u64,T>>,history:Ghost<trace::History<T>>,
}
impl<T> Bridge<T> {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn next_id(&self)->u64 {self.next}
    pub closed spec fn objects(&self)->Map<u64,T> {self.objects@}
    pub closed spec fn fibers(&self)->Map<usize,u64> {self.fibers@}
    pub closed spec fn issued(&self)->Map<u64,T> {self.issued@}
    pub closed spec fn observation(&self)->trace::Observation<T> {
        trace::Observation {domain:self.domain,next:self.next,objects:self.objects@,fibers:self.fibers@,claims:self.claims@,issued:self.issued@}
    }
    pub closed spec fn history(&self)->trace::History<T> {self.history@}
    pub closed spec fn wf(&self)->bool {
        self.tables_valid() && self.history().valid() && self.history().states.last()==self.observation()
    }
    pub closed spec fn tables_valid(&self)->bool {
        self.next>0
            && (forall|key:u64|#[trigger] self.issued@.contains_key(key) ==> 0<key<self.next)
            && (forall|key:u64|#[trigger] self.objects@.contains_key(key) ==> self.issued@.contains_key(key) && self.objects@[key]==self.issued@[key])
            && (forall|id:usize|#[trigger] self.fibers@.contains_key(id) ==> self.objects@.contains_key(self.fibers@[id]))
            && (forall|id:usize|#[trigger] self.claims@.contains_key(id) ==> self.claims@[id].ticket.id==id
                && self.claims@[id].ticket.domain==self.domain && self.fibers@.contains_key(id)
                && self.fibers@[id]==self.claims@[id].fiber && self.objects@.contains_key(self.claims@[id].recipe))
    }
    pub fn new(node:&NodeRuntime)->(out:Self)
        requires node.wf(),ensures out.wf(),out.domain_id()==node.observation().control.protocol().domain_id(),out.objects()==Map::empty(),
    {
        let domain=node.state().domain();
        Self {domain,next:1,objects:BTreeMap::new(),fibers:BTreeMap::new(),claims:BTreeMap::new(),issued:Ghost(Map::empty()),
            history:Ghost(trace::History {states:seq![trace::Observation::empty(domain)],events:Seq::empty()})}
    }
    proof fn record(tracked &mut self,event:trace::Event<T>)
        requires old(self).tables_valid(),old(self).history().valid(),
            trace::step(old(self).history().states.last(),old(self).observation(),event),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),
            final(self).history()==old(self).history().append(old(self).observation(),event),
    {
        self.history@.extended(self.observation(),event);
        self.history=Ghost(self.history@.append(self.observation(),event));
    }
    pub fn issue(&mut self,value:T)->(out:Result<ObjectKey,T>)
        requires old(self).wf(),ensures final(self).wf(),final(self).domain_id()==old(self).domain_id(),
            out.is_ok() ==> out->Ok_0.domain()==old(self).domain_id() && out->Ok_0.id()==old(self).next_id()
                && final(self).next_id()==old(self).next_id()+1 && final(self).objects()==old(self).objects().insert(out->Ok_0.id(),value)
                && !old(self).issued().contains_key(out->Ok_0.id()),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==value,
    {
        if self.next==u64::MAX {return Err(value);}
        let ghost original=value;
        let id=self.next;self.next+=1;
        proof {self.issued=Ghost(self.issued@.insert(id,value));}
        self.objects.insert(id,value);
        proof {reveal(trace::step);self.record(trace::Event::Issue {value:original});}
        Ok(ObjectKey {domain:self.domain,id})
    }
    pub fn contains(&self,key:ObjectKey)->(out:bool)
        ensures out==(key.domain()==self.domain_id() && self.objects().contains_key(key.id())),
    {key.domain()==self.domain && self.objects.contains_key(&key.id())}
    pub fn get(&self,key:ObjectKey)->(out:Option<&T>)
        requires self.wf(),ensures out.is_some()==(key.domain()==self.domain_id() && self.objects().contains_key(key.id())),
            out.is_some() ==> *out.unwrap()==self.objects()[key.id()] && *out.unwrap()==self.issued()[key.id()],
    {if key.domain()!=self.domain {None} else {self.objects.get(&key.id())}}
    pub fn lookup(&self,id:u64)->(out:Option<&T>)
        requires self.wf(),ensures out.is_some()==self.objects().contains_key(id),out.is_some() ==> *out.unwrap()==self.issued()[id],
    {self.get(ObjectKey {domain:self.domain,id})}
    pub fn bind_fiber(&mut self,node:&NodeRuntime,id:usize,key:ObjectKey)->(out:Result<(),BridgeError>)
        requires old(self).wf(),node.wf(),ensures final(self).wf(),final(self).objects()==old(self).objects(),final(self).issued()==old(self).issued(),
            out.is_ok() ==> final(self).fibers()==old(self).fibers().insert(id,key.id()) && node.observation().interfaces.contains_key(id)
                && key.domain()==node.observation().control.protocol().domain_id() && old(self).objects().contains_key(key.id()) && !old(self).fibers().contains_key(id),
            out.is_err() ==> *final(self)==*old(self),
    {
        if self.domain!=node.state().domain() || key.domain()!=self.domain {return Err(BridgeError::Domain);}
        if !node.interfaces().contains_key(&id) || !self.contains(key) {return Err(BridgeError::Unknown);}
        if self.fibers.contains_key(&id) {return Err(BridgeError::Bound);}
        self.fibers.insert(id,key.id());
        proof {reveal(trace::step);self.record(trace::Event::Bind {id,key:key.id(),node:node.history()});}Ok(())
    }
    pub fn fiber(&self,id:usize)->(out:Option<&T>)
        requires self.wf(),ensures out.is_some()==self.fibers().contains_key(id),
            out.is_some() ==> *out.unwrap()==self.issued()[self.fibers()[id]],
    {match self.fibers.get(&id) {Some(key)=>self.objects.get(key),None=>None}}
    pub fn unbind_fiber(&mut self,node:&NodeRuntime,id:usize)->(out:Result<Option<u64>,BridgeError>)
        requires old(self).wf(),node.wf(),ensures final(self).wf(),final(self).objects()==old(self).objects(),
            out.is_ok() ==> !node.observation().interfaces.contains_key(id) && final(self).fibers()==old(self).fibers().remove(id),
            out.is_err() ==> *final(self)==*old(self),
    {
        if self.domain!=node.state().domain() {return Err(BridgeError::Domain);}
        if node.interfaces().contains_key(&id) || self.claims.contains_key(&id) {return Err(BridgeError::Retained);}
        let out=self.fibers.remove(&id);
        proof {reveal(trace::step);self.record(trace::Event::Unbind {id,node:node.history()});}Ok(out)
    }
    pub fn begin_call(&mut self,node:&NodeRuntime,ticket:ActionTicket,fiber:ObjectKey,recipe:ObjectKey)->(out:Result<Call,BridgeError>)
        requires old(self).wf(),node.wf(),ensures final(self).wf(),final(self).objects()==old(self).objects(),final(self).issued()==old(self).issued(),
            final(self).fibers()==old(self).fibers(),
            out.is_ok() ==> out->Ok_0.certified() && out->Ok_0.ticket_spec()==ticket && out->Ok_0.origin()==node.history()
                && out->Ok_0.fiber_spec()==fiber && out->Ok_0.recipe_spec()==recipe && final(self).owns(&out->Ok_0)
                && old(self).objects().contains_key(recipe.id()) && old(self).fibers()[ticket.id]==fiber.id(),
            out.is_err() ==> *final(self)==*old(self),
    {
        if self.domain!=node.state().domain() || ticket.domain!=self.domain || fiber.domain()!=self.domain || recipe.domain()!=self.domain {return Err(BridgeError::Domain);}
        if self.fibers.get(&ticket.id)!=Some(&fiber.id()) || !self.contains(recipe) {return Err(BridgeError::Unknown);}
        if !node.state().pending_matches(ticket) {return Err(BridgeError::Stale);}
        if self.claims.contains_key(&ticket.id) {return Err(BridgeError::Busy);}
        self.claims.insert(ticket.id,Claim {ticket,fiber:fiber.id(),recipe:recipe.id()});
        proof {reveal(trace::step);self.record(trace::Event::Begin {claim:Claim {ticket,fiber:fiber.id(),recipe:recipe.id()},node:node.history()});}
        Ok(Call {ticket,fiber,recipe,origin:Ghost(node.history())})
    }
    pub closed spec fn owns(&self,call:&Call)->bool {
        call.ticket_spec().domain==self.domain && call.fiber_spec().domain==self.domain && call.recipe_spec().domain==self.domain
            && self.claims@.get(call.ticket_spec().id)==Some(Claim {ticket:call.ticket_spec(),fiber:call.fiber_spec().id,recipe:call.recipe_spec().id})
    }
    pub fn validate_call(&self,call:&Call)->(out:bool) ensures out==self.owns(call), {
        call.ticket.domain==self.domain && call.fiber.domain()==self.domain && call.recipe.domain()==self.domain
            && self.claims.get(&call.ticket.id)==Some(&Claim {ticket:call.ticket,fiber:call.fiber.id(),recipe:call.recipe.id()})
    }
    /// The adapter first completes the exact ticket, then consumes the retained
    /// dispatch only after the authoritative action ledger confirms consumption.
    pub fn finish_call(&mut self,node:&NodeRuntime,call:&Call)->(out:Result<(),BridgeError>)
        requires old(self).wf(),node.wf(),ensures final(self).wf(),final(self).objects()==old(self).objects(),final(self).fibers()==old(self).fibers(),
            out.is_ok() ==> old(self).owns(call) && !final(self).owns(call) && !node.observation().control.protocol().recorded(call.ticket_spec()),
            out.is_err() ==> *final(self)==*old(self),
    {
        if self.domain!=node.state().domain() {return Err(BridgeError::Domain);}
        if !self.validate_call(call) {return Err(BridgeError::Stale);}
        if node.state().pending_matches(call.ticket) {return Err(BridgeError::Busy);}
        self.claims.remove(&call.ticket.id);
        proof {reveal(trace::step);self.record(trace::Event::Finish {claim:Claim {ticket:call.ticket,fiber:call.fiber.id(),recipe:call.recipe.id()},node:node.history()});}Ok(())
    }
    /// Releasing a JS retention root requires both the real publication table
    /// and every retained Fiber/callback claim to have relinquished this key.
    pub fn remove(&mut self,node:&NodeRuntime,id:u64)->(out:Result<Option<T>,BridgeError>)
        requires old(self).wf(),node.wf(),ensures final(self).wf(),
            out.is_ok() ==> !handles::held(node.observation().store,id) && final(self).objects()==old(self).objects().remove(id)
                && out->Ok_0==old(self).objects().get(id),
            out.is_err() ==> *final(self)==*old(self),
            final(self).issued()==old(self).issued(),final(self).fibers()==old(self).fibers(),
    {
        if self.domain!=node.state().domain() {return Err(BridgeError::Domain);}
        if node.store().contains_handle(id) {return Err(BridgeError::Retained);}
        let keys=self.fibers.keys();let ghost all=keys.remaining();let _count=self.fibers.len();
        proof {assert forall|j:int|0<=j<all.len() implies self.fibers@.contains_key(*all[j]) by {assert(all.unref()[j]==*all[j]);assert(all.unref().contains(*all[j]));}}
        for key in iter: keys
            invariant self.wf(),all==iter.seq(),all.len()==_count,
                forall|j:int|0<=j<iter.index() ==> self.fibers@[*all[j]]!=id,
                forall|owner:usize|self.fibers@.contains_key(owner) ==> all.contains(&owner),
                forall|j:int|0<=j<all.len() ==> self.fibers@.contains_key(*all[j]),
            decreases _count as int-iter.index(),
        {if *self.fibers.get(key).unwrap()==id {return Err(BridgeError::Retained);}}
        proof {assert forall|owner:usize|self.fibers@.contains_key(owner) implies self.fibers@[owner]!=id by {
            let j=choose|j:int|0<=j<all.len() && all[j]==&owner;
        }}
        let keys=self.claims.keys();let ghost all=keys.remaining();let _count=self.claims.len();
        proof {assert forall|j:int|0<=j<all.len() implies self.claims@.contains_key(*all[j]) by {assert(all.unref()[j]==*all[j]);assert(all.unref().contains(*all[j]));}}
        for key in iter: keys
            invariant self.wf(),all==iter.seq(),all.len()==_count,
                forall|j:int|0<=j<iter.index() ==> self.claims@[*all[j]].recipe!=id,
                forall|owner:usize|self.claims@.contains_key(owner) ==> all.contains(&owner),
                forall|j:int|0<=j<all.len() ==> self.claims@.contains_key(*all[j]),
            decreases _count as int-iter.index(),
        {if self.claims.get(key).unwrap().recipe==id {return Err(BridgeError::Retained);}}
        proof {assert forall|owner:usize|self.claims@.contains_key(owner) implies self.claims@[owner].recipe!=id by {
            let j=choose|j:int|0<=j<all.len() && all[j]==&owner;
        }}
        let out=self.objects.remove(&id);
        proof {reveal(trace::step);self.record(trace::Event::Remove {id,node:node.history()});}Ok(out)
    }
    pub fn publish(&self,node:&mut NodeRuntime,owner:usize,generation:u64,port:Port,key:ObjectKey)
        ->(out:Result<Result<PublicationId,interfaces::PublishError>,BridgeError>)
        requires self.wf(),old(node).wf(),ensures final(node).wf(),
            out.is_ok() ==> self.objects().contains_key(key.id()) && key.domain()==self.domain_id()
                && key.domain()==old(node).observation().control.protocol().domain_id()
                && interfaces::service_published(old(node).history(),final(node).history(),owner,generation,port,key.id(),out->Ok_0),
            out.is_err() ==> *final(node)==*old(node),
    {
        if self.domain!=node.state().domain() || key.domain()!=self.domain {return Err(BridgeError::Domain);}
        if !self.contains(key) {return Err(BridgeError::Unknown);}
        Ok(node.publish_service(owner,generation,port,key.id()))
    }
    pub fn replace(&self,node:&mut NodeRuntime,owner:usize,generation:u64,publication:PublicationId,key:ObjectKey)
        ->(out:Result<Result<u64,RejectedValue<u64>>,BridgeError>)
        requires self.wf(),old(node).wf(),ensures final(node).wf(),
            out.is_ok() ==> self.objects().contains_key(key.id()) && key.domain()==self.domain_id()
                && key.domain()==old(node).observation().control.protocol().domain_id()
                && final(node).history()==old(node).history().append(final(node).observation(),Event::Replace {id:publication,owner,generation,value:key.id(),out:out->Ok_0}),
            out.is_err() ==> *final(node)==*old(node),
    {
        if self.domain!=node.state().domain() || key.domain()!=self.domain {return Err(BridgeError::Domain);}
        if !self.contains(key) {return Err(BridgeError::Unknown);}
        Ok(node.replace(publication,owner,generation,key.id()))
    }
    pub fn resolve<'a>(&'a self,node:&mut NodeRuntime,port:Port,consumer:Option<usize>,generation:Option<u64>)->(out:Result<Option<(reads::Read,&'a T)>,BridgeError>)
        requires self.wf(),old(node).wf(),ensures final(node).wf(),
            out.is_ok() && out->Ok_0.is_some() ==> {
                let found=out->Ok_0.unwrap();
                self.domain_id()==old(node).observation().control.protocol().domain_id() && self.objects().contains_key(found.0.value)
                    && *found.1==self.issued()[found.0.value]
                    && reads::result(old(node).observation(),port,consumer,generation)==Ok(Some(found.0))
            },
    {
        if self.domain!=node.state().domain() {return Err(BridgeError::Domain);}
        match node.resolve(port,consumer,generation) {
            Err(_)=>Err(BridgeError::Stale),
            Ok(None)=>Ok(None),Ok(Some(read))=>match self.objects.get(&read.value) {Some(value)=>Ok(Some((read,value))),None=>Err(BridgeError::Unknown)},
        }
    }
}
/// A same-borrow cut of the actual protocol and foreign-reference owner.
/// Coverage is checked at runtime; a missing JS reference is not assumed away.
#[allow(dead_code)]
pub struct HostSnapshot<T> {native:Ghost<History>,objects:Ghost<Map<u64,T>>,fibers:Ghost<Map<usize,u64>>,bridge:Ghost<trace::History<T>>}
impl<T> HostSnapshot<T> {
    pub closed spec fn native(&self)->History {self.native@}
    pub closed spec fn bridge(&self)->trace::History<T> {self.bridge@}
    pub closed spec fn objects(&self)->Map<u64,T> {self.objects@}
    pub closed spec fn fibers(&self)->Map<usize,u64> {self.fibers@}
    pub open spec fn certified(&self)->bool {
        self.native().valid() && self.native().states.last().wf()
            && self.bridge().valid() && self.bridge().states.last().objects==self.objects()
            && self.bridge().states.last().fibers==self.fibers()
            && self.bridge().states.last().domain==self.native().states.last().control.protocol().domain_id()
            && (forall|i:int|0<=i<self.native().states.last().store.values().len()
                && self.native().states.last().store.values()[i].is_some() ==>
                self.objects().contains_key(self.native().states.last().store.values()[i].unwrap()))
            && (forall|id:usize|self.native().states.last().interfaces.contains_key(id) ==>
                self.fibers().contains_key(id) && self.objects().contains_key(self.fibers()[id]))
    }
    /// The foreign-reference heap is the functional image of the actual retained
    /// publication table. A caller's lease-based lookup uses this same image.
    pub open spec fn heap(&self)->IMap<PublicationId,T> {
        IMap::new(|p:PublicationId|p.0<self.native().states.last().store.values().len()
            && self.native().states.last().store.values()[p.0 as int].is_some(),
            |p:PublicationId|self.objects()[self.native().states.last().store.values()[p.0 as int].unwrap()])
    }
    pub proof fn selected(&self,selected:&reads::Selected)
        requires self.certified(),selected.certified(),selected.origin().states.last()==self.native().states.last(),
        ensures self.heap().contains_key(selected.read_spec().publication) && self.objects().contains_key(selected.read_spec().value)
            && self.heap()[selected.read_spec().publication]==self.objects()[selected.read_spec().value],
    {}

}
impl<T> Bridge<T> {
    pub fn snapshot(&self,node:&NodeRuntime)->(out:Result<HostSnapshot<T>,BridgeError>)
        requires self.wf(),node.wf(),ensures out.is_ok() ==> out->Ok_0.certified()
            && out->Ok_0.native()==node.history() && out->Ok_0.objects()==self.objects() && out->Ok_0.fibers()==self.fibers()
            && out->Ok_0.bridge()==self.history() && super::production::interpreted(out->Ok_0.native()),
    {
        if self.domain!=node.state().domain() {return Err(BridgeError::Domain);}
        let count=node.store().registry().publication_records();let mut i=0;
        proof {node.observation().store.slot_count();}
        while i<count
            invariant self.wf(),node.wf(),i<=count,count==node.observation().store.values().len(),
                forall|j:int|0<=j<i && node.observation().store.values()[j].is_some() ==> self.objects().contains_key(node.observation().store.values()[j].unwrap()),
            decreases count-i,
        {
            if let Some(value)=node.store().value(PublicationId(i)) {if !self.objects.contains_key(value) {return Err(BridgeError::Unknown);}}
            i+=1;
        }
        let keys=node.interfaces().keys();let ghost all=keys.remaining();let _count=node.interfaces().len();
        for id in iter: keys
            invariant self.wf(),node.wf(),all==iter.seq(),all.len()==_count,
                forall|j:int|0<=j<node.observation().store.values().len() && node.observation().store.values()[j].is_some() ==> self.objects().contains_key(node.observation().store.values()[j].unwrap()),
                forall|j:int|0<=j<iter.index() ==> self.fibers().contains_key(*all[j]),
                forall|id:usize|node.observation().interfaces.contains_key(id) ==> all.unref().contains(id),
            decreases _count as int-iter.index(),
        {if !self.fibers.contains_key(id) {return Err(BridgeError::Unknown);}}
        proof {assert forall|id:usize|node.observation().interfaces.contains_key(id) implies self.fibers().contains_key(id) by {
            let j=choose|j:int|0<=j<all.len() && all.unref()[j]==id;
            assert(all.unref()[j]==*all[j]);
        }}
        let out=HostSnapshot {native:Ghost(node.history()),objects:Ghost(self.objects()),fibers:Ghost(self.fibers()),bridge:Ghost(self.history())};
        proof {out.production_trace();}Ok(out)
    }
}

}
