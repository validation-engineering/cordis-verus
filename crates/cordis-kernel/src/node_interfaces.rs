//! Actual Node declarations and reserved interfaces, owned with their lifecycle.
//! Static setup requirements remain distinct from dynamic provider reservations.
use super::*;
#[cfg(verus_keep_ghost)]
use crate::{lifecycle_state::history as c, refinement as r};
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;
verus! {
pub struct Interface {
    pub parent:Option<usize>,pub provisions:Vec<Port>,pub dependencies:Vec<Port>,
}
pub open spec fn initial(a:Observation,id:usize,port:Port)->bool {
    a.interfaces.contains_key(id) && a.interfaces[id].provisions@.contains(port)
}
pub open spec fn without(map:Map<(u64,u64),usize>,id:usize)->Map<(u64,u64),usize> {
    map.restrict(map.dom().filter(|p:(u64,u64)|map[p]!=id))
}
pub(super) fn remove_owner(map:&mut BTreeMap<(u64,u64),usize>,id:usize)
    ensures final(map)@==without(old(map)@,id),
{
    let ghost before=map@;let mut iter=map.iter();let ghost all=iter.remaining();let count=map.len();let mut i=0;let mut keys=Vec::new();
    while i<count
        invariant i<=count,all.len()==count,map@==before,iter.obeys_prophetic_iter_laws(),iter.remaining()==all.skip(i as int),
            forall|j:int|0<=j<keys.len() ==> before.contains_key(keys[j]) && before[keys[j]]==id,
            forall|j:int|0<=j<i && *all[j].1==id ==> keys@.contains(*all[j].0),
            forall|j:int|0<=j<all.len() ==> before.contains_key(*all[j].0) && before[*all[j].0]==*all[j].1,
            forall|key:(u64,u64)|before.contains_key(key) ==> all.contains((&key,&before[key])),
        decreases count-i,
    {
        let (key,owner)=iter.next().unwrap();let ghost prior_keys=keys@;
        assert(*key==*all[i as int].0 && *owner==*all[i as int].1);
        if *owner==id {keys.push(*key);}
        assert forall|j:int|0<=j<i+1 && *all[j].1==id implies keys@.contains(*all[j].0) by {
            if j<i {assert(prior_keys.contains(*all[j].0));}
            if *owner==id {vstd::seq_lib::lemma_seq_contains_after_push(prior_keys,*key,*all[j].0);}
        }
        i+=1;
    }
    assert forall|key:(u64,u64)|before.contains_key(key) && before[key]==id implies keys@.contains(key) by {
        let j=choose|j:int|0<=j<all.len() && all[j]==(&key,&before[key]);assert(keys@.contains(*all[j].0));
    }
    let mut j=0;
    while j<keys.len()
        invariant j<=keys.len(),map@==before.remove_keys(keys@.take(j as int).to_set()),
            forall|key:(u64,u64)|keys@.contains(key)==(before.contains_key(key) && before[key]==id),
        decreases keys.len()-j,
    {
        proof {keys@.lemma_take_succ_push(j as int);keys@.take(j as int).lemma_push_to_set_commute(keys[j as int]);}
        map.remove(&keys[j]);
        assert(map@ =~= before.remove_keys(keys@.take(j+1).to_set()));j+=1;
    }
    assert(keys@.take(j as int)==keys@);assert(map@ =~= without(before,id));
}
pub open spec fn step(a:Observation,b:Observation,event:Event)->bool {
    match event {
        Event::Insert {parent,dependencies,provisions,out}=>b.dynamic==a.dynamic && if out.is_ok() {
            b.interfaces.contains_key(out->Ok_0) && b.interfaces==a.interfaces.insert(out->Ok_0,b.interfaces[out->Ok_0])
                && b.interfaces[out->Ok_0].parent==parent && b.interfaces[out->Ok_0].provisions@==provisions
                && b.interfaces[out->Ok_0].dependencies@==dependencies
        } else {b.interfaces==a.interfaces},
        Event::Declare {id,port,out}=>b.interfaces==a.interfaces
            && b.dynamic==if out.is_ok() && !initial(a,id,port) {a.dynamic.insert((port.key,port.realm),id)} else {a.dynamic},
        Event::Dependencies {id,dependencies,out}=>b.dynamic==a.dynamic && if out.is_ok() {
            a.interfaces.contains_key(id) && b.interfaces.contains_key(id)
                && b.interfaces==a.interfaces.insert(id,Interface {dependencies:b.interfaces[id].dependencies,..a.interfaces[id]})
                && b.interfaces[id].dependencies@==dependencies
        } else {b.interfaces==a.interfaces},
        Event::ReleaseProvision {id,port,out}=>b.interfaces==a.interfaces
            && b.dynamic==if out.is_ok() && a.dynamic.get((port.key,port.realm))==Some(id) {a.dynamic.remove((port.key,port.realm))} else {a.dynamic},
        Event::Cleanup {command:CleanupCommand::Remove {id},out,..} if out.is_ok()=>b.interfaces==a.interfaces.remove(id) && b.dynamic==without(a.dynamic,id),
        _=>b.interfaces==a.interfaces && b.dynamic==a.dynamic,
    }
}
/// Descriptor membership, parent and current declared dependencies are the real
/// paper control projection. Initial provisions are a setup requirement, not
/// a claim that every dynamic publication belongs to the current provider.
pub open spec fn corresponds(a:Observation)->bool {
    (forall|id:usize|a.interfaces.contains_key(id)==r::registered(a.control.control().paper(),id))
        && (forall|id:usize|a.interfaces.contains_key(id) ==>
            a.interfaces[id].parent==a.control.control().paper().fibers[id].parent
            && a.interfaces[id].dependencies@.to_set().to_iset()==a.control.control().paper().fibers[id].dependencies)
}
impl NodeRuntime {
    pub fn interfaces(&self)->(out:&BTreeMap<usize,Interface>)
        ensures out@==self.observation().interfaces,
    {&self.interfaces}
    pub fn dynamic_declarations(&self)->(out:&BTreeMap<(u64,u64),usize>)
        ensures out@==self.observation().dynamic,
    {&self.dynamic}
    pub(super) fn initial_provision(&self,id:usize,port:Port)->(out:bool)
        ensures out==initial(self.observation(),id,port),
    {
        if let Some(node)=self.interfaces.get(&id) {
            let mut i=0;
            while i<node.provisions.len()
                invariant self.interfaces@.contains_key(id),*node==self.interfaces@[id],i<=node.provisions.len(),forall|j:int|0<=j<i ==> node.provisions[j]!=port,
                decreases node.provisions.len()-i,
            {
                if node.provisions[i]==port {return true;}i+=1;
            }
        }
        false
    }
}
impl History {
    pub proof fn interface_correspondence(&self,end:int)
        requires self.valid(),0<=end<self.states.len(),
        ensures corresponds(self.states[end]),
        decreases end,
    {
        if end>0 {
            self.interface_correspondence(end-1);let i=end-1;let a=self.states[i];let b=self.states[end];
            assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
            if b.control.same(&a.control) {b.control.same_components(&a.control);}
            if b.control.control().unchanged(&a.control.control()) {b.control.control().unchanged_observations(&a.control.control());}
            self.control_classified(i);
            let pa=a.control.control().paper();let pb=b.control.control().paper();
            match self.events[i] {
                Event::Insert {out,..} if out.is_ok()=>{},
                Event::Dependencies {id,out,..} if out.is_ok()=>{},
                Event::Cleanup {command:CleanupCommand::Remove {id},out,..} if out.is_ok()=>{},
                _=>{},
            }
            assert forall|id:usize|b.interfaces.contains_key(id) implies
                b.interfaces[id].parent==pb.fibers[id].parent && b.interfaces[id].dependencies@.to_set().to_iset()==pb.fibers[id].dependencies by {
                if a.interfaces.contains_key(id) {assert(a.interfaces[id].parent==pa.fibers[id].parent);}
            }
        }
    }
}
/// Every tracked dynamic port belongs to a present fiber that really declares
/// it. Publication ownership may already differ while old commitments drain.
pub open spec fn dynamic_corresponds(a:Observation)->bool {
    forall|key:(u64,u64)|a.dynamic.contains_key(key) ==> {
        let id=a.dynamic[key];let port=Port {key:key.0,realm:key.1};
        a.interfaces.contains_key(id) && !initial(a,id,port)
            && a.control.control().paper().fibers[id].provisions.contains(port)
    }
}
impl History {
    pub proof fn interface_control_step(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),
            self.states[index+1].control.control_history().extends(self.states[index].control.control_history()),
        ensures c::step(self.states[index].control.control().paper(),self.states[index+1].control.control().paper(),self.states[index+1].control.control_history().labels.last()),
    {
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));
        self.states[index].control.control_history_correspondence();self.states[index+1].control.control_history_correspondence();
        let a=self.states[index].control.control_history();let b=self.states[index+1].control.control_history();
        assert(b.states[b.labels.len()-1]==a.states.last());
        assert(c::step(b.states[b.labels.len()-1],b.states[b.labels.len() as int],b.labels[b.labels.len()-1]));
    }
    pub proof fn dynamic_correspondence(&self,end:int)
        requires self.valid(),0<=end<self.states.len(),
        ensures dynamic_corresponds(self.states[end]),
        decreases end,
    {
        self.interface_correspondence(end);
        if end>0 {
            self.dynamic_correspondence(end-1);self.interface_correspondence(end-1);let i=end-1;
            assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
            let a=self.states[i];let b=self.states[end];
            if b.control.same(&a.control) {b.control.same_components(&a.control);}
            if b.control.control().unchanged(&a.control.control()) {b.control.control().unchanged_observations(&a.control.control());}
            if b.control.control_history().extends(a.control.control_history()) {self.interface_control_step(i);}
            assert forall|key:(u64,u64)|b.dynamic.contains_key(key) implies {
                let id=b.dynamic[key];let port=Port {key:key.0,realm:key.1};
                b.interfaces.contains_key(id) && !initial(b,id,port) && b.control.control().paper().fibers[id].provisions.contains(port)
            } by {
                let id=b.dynamic[key];let port=Port {key:key.0,realm:key.1};
                if a.dynamic.get(key)==Some(id) {
                    assert(a.interfaces.contains_key(id));
                    assert(!initial(a,id,port));
                    assert(a.control.control().paper().fibers[id].provisions.contains(port));
                }
                match self.events[i] {
                    Event::Declare {id:owner,port:declared,out} if out.is_ok() && (declared.key,declared.realm)==key && !initial(a,owner,declared)=>{
                        assert(declared==port);assert(id==owner);
                    },
                    _=>{assert(a.dynamic.get(key)==Some(id));},
                }
            }
        }
    }
    pub open spec fn declaration_issued_at(&self,index:int,key:(u64,u64),owner:usize)->bool {
        0<=index<self.events.len() && self.events[index] is Declare && self.events[index]->Declare_id==owner
            && self.events[index]->Declare_port==(Port {key:key.0,realm:key.1}) && self.events[index]->Declare_out.is_ok()
            && !initial(self.states[index],owner,Port {key:key.0,realm:key.1})
    }
    /// The ownership table is constructed by successful real declarations.
    pub proof fn declaration_origin(&self,end:int,key:(u64,u64))
        requires self.valid(),0<=end<self.states.len(),self.states[end].dynamic.contains_key(key),
        ensures exists|i:int|0<=i<end && self.declaration_issued_at(i,key,self.states[end].dynamic[key]),
        decreases end,
    {
        assert(end>0);let i=end-1;
        assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
        match self.events[i] {
            Event::Declare {id,port,out} if out.is_ok() && (port.key,port.realm)==key && !initial(self.states[i],id,port)=>{
                assert(port==(Port {key:key.0,realm:key.1}));
                assert(self.states[end].dynamic[key]==id);
                assert(0<=i<self.events.len());
                assert(!initial(self.states[i],id,Port {key:key.0,realm:key.1}));
                assert(self.declaration_issued_at(i,key,self.states[end].dynamic[key]));
            },
            _=>{assert(self.states[i].dynamic.get(key)==self.states[end].dynamic.get(key));self.declaration_origin(i,key);},
        }
    }
    /// The original mount requirements cannot be changed by later declarations,
    /// sealing, retries, cleanup, or another fiber's removal.
    pub proof fn mount_origin(&self,end:int,id:usize)
        requires self.valid(),0<=end<self.states.len(),self.states[end].interfaces.contains_key(id),
        ensures exists|i:int|0<=i<end && self.events[i] is Insert && self.events[i]->Insert_out==Ok(id)
            && self.events[i]->Insert_parent==self.states[end].interfaces[id].parent
            && self.events[i]->Insert_provisions==self.states[end].interfaces[id].provisions@,
        decreases end,
    {
        assert(end>0);let i=end-1;
        assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
        match self.events[i] {
            Event::Insert {out,..} if out==Ok(id)=>{
                assert(self.events[i]->Insert_parent==self.states[end].interfaces[id].parent);
            },
            _=>{self.mount_origin(i,id);},
        }
    }
    /// Releasing a declaration is permitted only after every committed
    /// consumer of that exact owner/port has drained. Revocation alone is not
    /// sufficient; a failed cleanup does not discharge the commitment.
    pub proof fn release_requires_drained_commitments(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is ReleaseProvision,self.events[index]->ReleaseProvision_out.is_ok(),
        ensures {
            let owner=self.events[index]->ReleaseProvision_id;let port=self.events[index]->ReleaseProvision_port;
            let s=self.states[index].control.control().paper();
            forall|id:usize,binding:crate::Binding|r::registered(s,id) && #[trigger] s.fibers[id].committed.contains(binding)
                ==> binding.provider!=owner || binding.key!=port.key || binding.realm!=port.realm
        },
    {
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
        self.interface_control_step(index);
    }
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Choice {Untracked,Keep {owner:usize},Release {owner:usize,next:Option<usize>}}
pub open spec fn successor_open(a:Observation,id:usize)->bool {
    let k=a.control.control();
    !k.is_retired(id) && (k.phase_of(id)==Some(Phase::Loading) || k.phase_of(id)==Some(Phase::Active)
        || (k.phase_of(id)==Some(Phase::Inactive) && k.generation_of(id)==Some(0) && a.episodes.contains_key(id) && a.episodes[id].prepared))
}
#[verifier::opaque]
pub open spec fn choice(a:Observation,port:Port)->Choice {
    if !a.dynamic.contains_key((port.key,port.realm)) {Choice::Untracked} else {
        let owner=a.dynamic[(port.key,port.realm)];let visible=reads::visible_choice(a,port);
        let next=if visible.is_some() {Some(a.store.registry_view().publications()[visible.unwrap().0 as int].owner)} else {None};
        if next==Some(owner) {Choice::Keep {owner}}
        else {Choice::Release {owner,next:if next.is_some() && successor_open(a,next.unwrap()) {next} else {None}}}
    }
}
pub open spec fn prefix(a:History,b:History)->bool {
    a.events.len()<=b.events.len() && a.states.len()<=b.states.len() && b.events.take(a.events.len() as int)==a.events && b.states.take(a.states.len() as int)==a.states
}
pub proof fn prefix_reflexive(a:History)
    ensures prefix(a,a),
{assert(a.events.take(a.events.len() as int) =~= a.events);assert(a.states.take(a.states.len() as int) =~= a.states);}
pub proof fn prefix_append(a:History,state:Observation,event:Event)
    ensures prefix(a,a.append(state,event)),
{assert(a.append(state,event).events.take(a.events.len() as int) =~= a.events);assert(a.append(state,event).states.take(a.states.len() as int) =~= a.states);}
pub proof fn prefix_transitive(a:History,b:History,c:History)
    requires prefix(a,b),prefix(b,c),a.states.len()<=b.states.len(),
    ensures prefix(a,c),
{assert(c.events.take(a.events.len() as int) =~= a.events);assert(c.states.take(a.states.len() as int) =~= a.states);}
/// Exact finite call sequence for one reconciliation. An installation error
/// after release is a retained partial prefix, never an atomic rollback claim.
#[verifier::opaque]
pub open spec fn reconciled(a:History,b:History,port:Port,out:Result<(),Error>)->bool {
    prefix(a,b) && match choice(a.states.last(),port) {
        Choice::Untracked|Choice::Keep {..}=>b==a && out==Ok(()),
        Choice::Release {owner,next}=>{
            let i=a.events.len() as int;
            b.events.len()>i && b.events[i] is ReleaseProvision && b.events[i]->ReleaseProvision_id==owner && b.events[i]->ReleaseProvision_port==port
                && if b.events[i]->ReleaseProvision_out.is_err() {
                    b.events.len()==i+1 && out==if b.events[i]->ReleaseProvision_out==Err(Error::Relied) {Ok(())} else {b.events[i]->ReleaseProvision_out}
                } else if next.is_some() {
                    b.events.len()==i+2 && b.events[i+1]==(Event::Declare {id:next.unwrap(),port,out})
                } else {b.events.len()==i+1 && out==Ok(())}
        },
    }
}
impl NodeRuntime {
    fn declaration_choice(&self,port:Port)->(out:Choice)
        requires self.wf(),ensures out==choice(self.observation(),port),
    {
        proof {reveal(choice);}
        let owner=match self.dynamic.get(&(port.key,port.realm)) {Some(id)=>*id,None=>return Choice::Untracked};
        if let Some(id)=self.visible_lookup(port) {
            let next=self.store.registry().entry(id).unwrap().owner;
            if next==owner {return Choice::Keep {owner};}
            let phase=self.control.kernel().phase(next);
            let prepared=match self.episodes.get(&next) {Some(e)=>e.prepared,None=>false};
            if !self.control.kernel().retired(next) && (phase==Some(Phase::Loading) || phase==Some(Phase::Active)
                || (phase==Some(Phase::Inactive) && self.control.kernel().episode_generation(next)==Some(0) && prepared)) {
                return Choice::Release {owner,next:Some(next)};
            }
        }
        Choice::Release {owner,next:None}
    }
    pub fn reconcile_declaration(&mut self,port:Port)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),reconciled(old(self).history(),final(self).history(),port,out),
    {
        let ghost before=self.history();
        let plan=self.declaration_choice(port);
        proof {reveal(reconciled);prefix_reflexive(before);}
        match plan {
            Choice::Untracked|Choice::Keep {..}=>Ok(()),
            Choice::Release {owner,next}=>{
                let released=self.release_provision(owner,port);
                assert(self.history()==before.append(self.observation(),Event::ReleaseProvision {id:owner,port,out:released}));
                assert(self.history().events[before.events.len() as int]==(Event::ReleaseProvision {id:owner,port,out:released}));
                proof {prefix_append(before,self.observation(),Event::ReleaseProvision {id:owner,port,out:released});}
                let ghost released_history=self.history();
                match released {
                    Err(Error::Relied)=>return Ok(()),Err(error)=>return Err(error),Ok(())=>{},
                }
                if let Some(next)=next {
                    let out=self.declare_provision(next,port);
                    assert(self.history()==released_history.append(self.observation(),Event::Declare {id:next,port,out}));
                    proof {prefix_append(released_history,self.observation(),Event::Declare {id:next,port,out});prefix_transitive(before,released_history,self.history());}
                    assert(self.history().events[before.events.len() as int] is ReleaseProvision && self.history().events[before.events.len() as int]->ReleaseProvision_out.is_ok());
                    out
                } else {Ok(())}
            },
        }
    }
}
impl History {
    /// A successful replacement reservation uses the actual visible, admissible
    /// successor selected at the call boundary, after the old reservation has
    /// passed the real committed-consumer release guard.
    pub proof fn reconciled_transfer(&self,before:History,port:Port,out:Result<(),Error>)
        requires self.valid(),before.valid(),reconciled(before,*self,port,out),
            self.events.len()==before.events.len()+2,out.is_ok(),
        ensures {
            let i=before.events.len() as int;
            let owner=self.events[i]->ReleaseProvision_id;let next=self.events[i+1]->Declare_id;
            self.events[i] is ReleaseProvision && self.events[i]->ReleaseProvision_port==port && self.events[i]->ReleaseProvision_out.is_ok()
                && self.events[i+1] is Declare && self.events[i+1]->Declare_port==port && self.events[i+1]->Declare_out.is_ok()
                && owner!=next && successor_open(before.states.last(),next)
                && reads::visible_choice(before.states.last(),port).is_some()
                && before.states.last().store.registry_view().publications()[reads::visible_choice(before.states.last(),port).unwrap().0 as int].owner==next
                && forall|id:usize,binding:crate::Binding|r::registered(self.states[i].control.control().paper(),id)
                    && #[trigger] self.states[i].control.control().paper().fibers[id].committed.contains(binding)
                    ==> binding.provider!=owner || binding.key!=port.key || binding.realm!=port.realm
        },
    {
        reveal(reconciled);reveal(choice);self.release_requires_drained_commitments(before.events.len() as int);
    }
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum PublishError {Access(EpisodeError),Declaration(Error),Publication(PublicationError)}
/// A successful publication follows the actual declaration attempt. A conflict
/// is tolerated only for a tracked dynamic reservation that must drain first.
#[verifier::opaque]
pub open spec fn service_published(a:History,b:History,owner:usize,generation:u64,port:Port,value:u64,out:Result<PublicationId,PublishError>)->bool {
    prefix(a,b) && {
        let state=a.states.last();let validation=episode::validation(state,owner,generation);let i=a.events.len() as int;
        if validation.is_err() {b==a && out==Err(PublishError::Access(validation->Err_0))}
        else if reads::visible_choice(state,port).is_some() {b==a && out==Err(PublishError::Publication(PublicationError::Conflict))}
        else if state.store.registry_view().publications().len()==usize::MAX {b==a && out==Err(PublishError::Publication(PublicationError::Capacity))}
        else {
            b.events.len()>i && b.events[i] is Declare && b.events[i]->Declare_id==owner && b.events[i]->Declare_port==port && {
                let declared=b.events[i]->Declare_out;
                if declared.is_err() && !(declared==Err(Error::Conflict) && state.dynamic.contains_key((port.key,port.realm))) {
                    b.events.len()==i+1 && out==Err(PublishError::Declaration(declared->Err_0))
                } else {
                    b.events.len()==i+2 && b.events[i+1] is Publish && b.events[i+1]->Publish_owner==owner
                        && b.events[i+1]->Publish_generation==generation && b.events[i+1]->Publish_port==port && b.events[i+1]->Publish_value==value
                        && out==match b.events[i+1]->Publish_out {Ok(id)=>Ok(id),Err(rejected)=>Err(PublishError::Publication(rejected.error))}
                }
            }
        }
    }
}
impl NodeRuntime {
    /// The Node adapter's real publish entry: admission, visible conflict and
    /// capacity checks, tracked declaration conflict, then the actual payload.
    pub fn publish_service(&mut self,owner:usize,generation:u64,port:Port,value:u64)->(out:Result<PublicationId,PublishError>)
        requires old(self).wf(),
        ensures final(self).wf(),service_published(old(self).history(),final(self).history(),owner,generation,port,value,out),
    {
        let ghost before=self.history();let ghost original=self.observation();
        proof {reveal(service_published);prefix_reflexive(before);}
        if let Err(error)=self.validate(owner,generation) {return Err(PublishError::Access(error));}
        if self.visible_lookup(port).is_some() {return Err(PublishError::Publication(PublicationError::Conflict));}
        if self.store.registry().publication_records()==usize::MAX {return Err(PublishError::Publication(PublicationError::Capacity));}
        let declared=self.declare_provision(owner,port);
        proof {
            prefix_append(before,self.observation(),Event::Declare {id:owner,port,out:declared});
            assert(history::step(original,self.observation(),self.history().events.last()));reveal(history::operation);
        }
        match declared {
            Ok(())=>{},
            Err(Error::Conflict) if self.dynamic.contains_key(&(port.key,port.realm))=>{},
            Err(error)=>return Err(PublishError::Declaration(error)),
        }
        let ghost admitted=self.history();
        let result=self.publish(owner,generation,port,value);
        proof {
            prefix_append(admitted,self.observation(),Event::Publish {owner,generation,port,value,out:result});
            prefix_transitive(before,admitted,self.history());
        }
        match result {Ok(id)=>Ok(id),Err(rejected)=>Err(PublishError::Publication(rejected.error))}
    }
}
pub open spec fn ports_cover(a:Observation,ports:Seq<Port>)->bool {
    ports.len()==a.dynamic.len()
        && (forall|i:int|0<=i<ports.len() ==> a.dynamic.contains_key((ports[i].key,ports[i].realm)))
        && (forall|key:(u64,u64)|a.dynamic.contains_key(key) ==> ports.contains(Port {key:key.0,realm:key.1}))
}
pub open spec fn batch_prefix(ports:Seq<Port>,runs:Seq<History>,results:Seq<Result<(),Error>>)->bool {
    runs.len()==results.len()+1 && results.len()<=ports.len()
        && forall|i:int|0<=i<results.len() ==> reconciled(runs[i],runs[i+1],ports[i],results[i])
}
pub open spec fn batch_result(a:History,b:History,ports:Seq<Port>,runs:Seq<History>,results:Seq<Result<(),Error>>,out:Result<(),Error>)->bool {
    ports_cover(a.states.last(),ports) && batch_prefix(ports,runs,results) && runs[0]==a && runs.last()==b
        && (forall|i:int|0<=i<results.len()-1 ==> results[i].is_ok())
        && if out.is_ok() {results.len()==ports.len() && (results.len()>0 ==> results.last().is_ok())}
            else {results.len()>0 && results.last()==out}
}
impl NodeRuntime {
    fn dynamic_ports(&self)->(out:Vec<Port>)
        ensures ports_cover(self.observation(),out@),
    {
        let mut iter=self.dynamic.iter();let ghost all=iter.remaining();let count=self.dynamic.len();let mut i=0;let mut out=Vec::new();
        while i<count
            invariant i<=count,count==all.len(),count==self.dynamic@.len(),out.len()==i,
                iter.obeys_prophetic_iter_laws(),iter.remaining()==all.skip(i as int),
                forall|j:int|0<=j<i ==> out[j]==(Port {key:all[j].0.0,realm:all[j].0.1}),
                forall|j:int|0<=j<all.len() ==> self.dynamic@.contains_key(*all[j].0),
                forall|key:(u64,u64)|self.dynamic@.contains_key(key) ==> all.contains((&key,&self.dynamic@[key])),
            decreases count-i,
        {
            let (key,_)=iter.next().unwrap();out.push(Port {key:key.0,realm:key.1});i+=1;
        }
        assert forall|key:(u64,u64)|self.dynamic@.contains_key(key) implies out@.contains(Port {key:key.0,realm:key.1}) by {
            let j=choose|j:int|0<=j<all.len() && all[j]==(&key,&self.dynamic@[key]);assert(out[j]==(Port {key:key.0,realm:key.1}));
        }
        out
    }
    /// Visit every original dynamic port in map order. A returned error keeps
    /// exactly the completed prefix and the failed call in this same history.
    pub fn reconcile_declarations(&mut self)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),prefix(old(self).history(),final(self).history()),
            exists|ports:Seq<Port>,runs:Seq<History>,results:Seq<Result<(),Error>>|
                batch_result(old(self).history(),final(self).history(),ports,runs,results,out),
    {
        let ghost before=self.history();let ports=self.dynamic_ports();let mut i=0;
        let ghost mut runs=seq![before];let ghost mut results:Seq<Result<(),Error>>=Seq::empty();
        proof {prefix_reflexive(before);}
        while i<ports.len()
            invariant self.wf(),i<=ports.len(),i==results.len(),batch_prefix(ports@,runs,results),
                runs[0]==before,runs.last()==self.history(),before==old(self).history(),
                ports_cover(before.states.last(),ports@),prefix(before,self.history()),
                forall|j:int|0<=j<i ==> results[j].is_ok(),
            decreases ports.len()-i,
        {
            let ghost prior=self.history();let result=self.reconcile_declaration(ports[i]);
            proof {
                reveal(reconciled);prefix_transitive(before,prior,self.history());
                results=results.push(result);runs=runs.push(self.history());
                assert forall|j:int|0<=j<results.len() implies reconciled(runs[j],runs[j+1],ports[j],results[j]) by {
                    if j<i {assert(reconciled(runs[j],runs[j+1],ports[j],results[j]));}
                }
            }
            if result.is_err() {
                assert(batch_result(before,self.history(),ports@,runs,results,result));return result;
            }
            i+=1;
        }
        assert(batch_result(before,self.history(),ports@,runs,results,Ok(())));Ok(())
    }
}
}
