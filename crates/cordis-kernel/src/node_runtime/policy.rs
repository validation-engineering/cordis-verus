//! Production Node admission policy, interpreted as explicit host extensions.
//! Gates observe the real owner; failed gates cannot mutate its observation.
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Profile {Cordis,Harness}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Policy {pub profile:Profile,pub configured:bool}
impl Policy {pub open spec fn initial()->Self {Self {profile:Profile::Cordis,configured:false}}}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum PolicyError {ProfileFrozen,ParentClosed,AlreadySealed,Kernel(Error),Episode(EpisodeError)}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Gate {Mount {parent:Option<usize>},Seal {id:usize}}
pub open spec fn gate_result(a:Observation,gate:Gate)->Result<bool,PolicyError> {
    match gate {
        Gate::Mount {parent}=>if parent.is_some() && (!a.control.control().registered(parent.unwrap())
            || a.control.control().is_retired(parent.unwrap()) || a.control.control().phase_of(parent.unwrap())==Some(Phase::Unloading))
            {Err(PolicyError::ParentClosed)} else {Ok(true)},
        Gate::Seal {id}=>if !a.interfaces.contains_key(id) || !a.episodes.contains_key(id) {Err(PolicyError::Kernel(Error::Unknown))}
            else if a.episodes[id].sealed {Err(PolicyError::AlreadySealed)}
            else {Ok(!a.control.control().is_retired(id))},
    }
}
pub open spec fn step(a:Observation,b:Observation,event:Event)->bool {
    match event {
        Event::Configure {profile,out}=>out==if a.policy.configured {Err(PolicyError::ProfileFrozen)} else {Ok(())}
            && b.policy==if out.is_ok() {Policy {profile,configured:true}} else {a.policy},
        Event::Insert {out,..}=>b.policy==if out.is_ok() {Policy {configured:true,..a.policy}} else {a.policy},
        Event::Gate {gate,out}=>b.policy==a.policy && out==gate_result(a,gate),
        _=>b.policy==a.policy,
    }
}
/// Exact finite trace of the real mount entry, including early rejection.
/// A failed later phase retains its actual completed prefix.
#[verifier::opaque]
pub open spec fn mount_trace(a:History,b:History,parent:Option<usize>,dependencies:Seq<Port>,provisions:Seq<Port>,sealed:bool,out:Result<usize,PolicyError>)->bool {
    let i=a.events.len() as int;let gate=gate_result(a.states.last(),Gate::Mount {parent});
    &&& a.prefix_of(b) && b.events.len()>i
    &&& b.events[i]==(Event::Gate {gate:Gate::Mount {parent},out:gate}) && b.states[i+1]==a.states.last()
    &&& if gate.is_err() {b.events.len()==i+1 && out==Err(gate->Err_0)} else {
        &&& b.events.len()>=i+2 && b.events[i+1] is Insert
        &&& b.events[i+1]->Insert_parent==parent && b.events[i+1]->Insert_dependencies==dependencies && b.events[i+1]->Insert_provisions==provisions
        &&& match b.events[i+1]->Insert_out {
            Err(error)=>b.events.len()==i+2 && out==Err(PolicyError::Kernel(error)),
            Ok(id)=>b.events.len()==i+3 && b.events[i+2] is Episode
                && b.events[i+2]->Episode_command==(EpisodeCommand::Seal {id,sealed})
                && out==match b.events[i+2]->Episode_out {Ok(())=>Ok(id),Err(error)=>Err(PolicyError::Episode(error))},
        }
    }
}
/// The gate, declaration update and seal result all come from this invocation.
#[verifier::opaque]
pub open spec fn seal_trace(a:History,b:History,id:usize,dependencies:Seq<Port>,out:Result<(),PolicyError>)->bool {
    let i=a.events.len() as int;let gate=gate_result(a.states.last(),Gate::Seal {id});
    &&& a.prefix_of(b) && b.events.len()>i
    &&& b.events[i]==(Event::Gate {gate:Gate::Seal {id},out:gate}) && b.states[i+1]==a.states.last()
    &&& match gate {
        Err(error)=>b.events.len()==i+1 && out==Err(error),
        Ok(false)=>b.events.len()==i+1 && out==Ok(()),
        Ok(true)=>{
            &&& b.events.len()>=i+2 && b.events[i+1] is Dependencies
            &&& b.events[i+1]->Dependencies_id==id && b.events[i+1]->Dependencies_dependencies==dependencies
            &&& match b.events[i+1]->Dependencies_out {
                Err(error)=>b.events.len()==i+2 && out==Err(PolicyError::Kernel(error)),
                Ok(())=>b.events.len()==i+3 && b.events[i+2] is Episode
                    && b.events[i+2]->Episode_command==(EpisodeCommand::Seal {id,sealed:true})
                    && out==match b.events[i+2]->Episode_out {Ok(())=>Ok(()),Err(error)=>Err(PolicyError::Episode(error))},
            }
        },
    }
}
impl History {
    pub open spec fn prefix_of(&self,later:Self)->bool {
        interfaces::prefix(*self,later)
    }
    pub proof fn prefix_append(&self,next:Observation,event:Event)
        ensures self.prefix_of(self.append(next,event)),
    {interfaces::prefix_append(*self,next,event);}
    pub proof fn prefix_transitive(&self,middle:Self,later:Self)
        requires self.prefix_of(middle),middle.prefix_of(later),
        ensures self.prefix_of(later),
    {
        interfaces::prefix_transitive(*self,middle,later);
    }
    pub proof fn last_step(&self)
        requires self.valid(),self.events.len()>0,
        ensures history::step(self.states[self.events.len()-1],self.states.last(),self.events.last()),
    {
        let i=self.events.len()-1;
        assert(history::step(self.states[i],self.states[i+1],self.events[i]));
    }
    /// A frozen profile stays frozen even after the last fiber is removed.
    pub proof fn frozen_profile(&self,start:int,end:int)
        requires self.valid(),0<=start<=end<self.states.len(),self.states[start].policy.configured,
        ensures self.states[end].policy==self.states[start].policy,
        decreases end-start,
    {
        if start<end {
            self.frozen_profile(start,end-1);let i=end-1;
            assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
        }
    }
    /// The actual history, rather than a caller-provided empty-domain flag,
    /// explains why registration permanently freezes profile selection.
    pub proof fn registration_freezes_profile(&self,index:int,end:int)
        requires self.valid(),0<=index<end<self.states.len(),self.events[index] is Insert,self.events[index]->Insert_out.is_ok(),
        ensures self.states[end].policy.configured,self.states[end].policy.profile==self.states[index].policy.profile,
    {
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
        self.frozen_profile(index+1,end);
    }
}
impl NodeRuntime {
    pub fn profile(&self)->(out:Profile) ensures out==self.observation().policy.profile, {self.policy.profile}
    pub fn configure_profile(&mut self,profile:Profile)->(out:Result<(),PolicyError>)
        requires old(self).wf(),
        ensures final(self).wf(),out==if old(self).observation().policy.configured {Err(PolicyError::ProfileFrozen)} else {Ok(())},
            final(self).history()==old(self).history().append(final(self).observation(),Event::Configure {profile,out}),
            final(self).observation()==(Observation {policy:if out.is_ok() {Policy {profile,configured:true}} else {old(self).observation().policy},..old(self).observation()}),
    {
        let ghost before=self.observation();
        let out=if self.policy.configured {Err(PolicyError::ProfileFrozen)} else {self.policy=Policy {profile,configured:true};Ok(())};
        proof {self.scopes.unchanged_reflexive();reveal(history::operation);self.record(before,Event::Configure {profile,out});}
        out
    }
    fn gate(&mut self,gate:Gate)->(out:Result<bool,PolicyError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),out==gate_result(old(self).observation(),gate),
            final(self).history()==old(self).history().append(final(self).observation(),Event::Gate {gate,out}),
    {
        let ghost before=self.observation();
        let out=match gate {
            Gate::Mount {parent}=>match parent {
                Some(id) if !self.control.kernel().contains(id) || self.control.kernel().retired(id) || self.control.kernel().phase(id)==Some(Phase::Unloading)=>Err(PolicyError::ParentClosed),
                _=>Ok(true),
            },
            Gate::Seal {id}=>if !self.interfaces.contains_key(&id) || !self.episodes.contains_key(&id) {Err(PolicyError::Kernel(Error::Unknown))}
                else if self.episodes.get(&id).unwrap().sealed {Err(PolicyError::AlreadySealed)}
                else {Ok(!self.control.kernel().retired(id))},
        };
        proof {self.scopes.unchanged_reflexive();reveal(history::operation);self.record(before,Event::Gate {gate,out});}
        out
    }
    /// Real mount command: check the parent, allocate exactly these declarations
    /// and seal the actual returned episode before exposing its identity.
    pub fn mount(&mut self,parent:Option<usize>,dependencies:Vec<Port>,provisions:Vec<Port>,sealed:bool)->(out:Result<usize,PolicyError>)
        requires old(self).wf(),
        ensures final(self).wf(),old(self).history().prefix_of(final(self).history()),
            mount_trace(old(self).history(),final(self).history(),parent,dependencies@,provisions@,sealed,out),
            out==Err(PolicyError::ParentClosed) ==> final(self).observation()==old(self).observation(),
            out.is_ok() ==> gate_result(old(self).observation(),Gate::Mount {parent})==Ok(true)
                && final(self).observation().policy.configured
                && final(self).observation().interfaces.contains_key(out->Ok_0)
                && final(self).observation().interfaces[out->Ok_0].parent==parent
                && final(self).observation().interfaces[out->Ok_0].dependencies@==dependencies@
                && final(self).observation().interfaces[out->Ok_0].provisions@==provisions@
                && final(self).observation().episodes.contains_key(out->Ok_0)
                && final(self).observation().episodes[out->Ok_0].sealed==sealed,
    {
        proof {reveal(mount_trace);}
        let ghost initial=self.history();
        let gate=self.gate(Gate::Mount {parent});
        proof {initial.prefix_append(self.observation(),Event::Gate {gate:Gate::Mount {parent},out:gate});}
        let ghost gated=self.history();
        gate?;
        let allocation=self.insert(parent,dependencies,provisions);
        proof {
            gated.prefix_append(self.observation(),self.history().events.last());
            initial.prefix_transitive(gated,self.history());
            self.history().last_step();reveal(history::operation);
        }
        let id=match allocation {Ok(id)=>id,Err(error)=>return Err(PolicyError::Kernel(error))};
        let ghost inserted=self.history();
        let result=self.episode_command(EpisodeCommand::Seal {id,sealed});
        proof {
            inserted.prefix_append(self.observation(),self.history().events.last());
            initial.prefix_transitive(inserted,self.history());
            self.history().last_step();reveal(history::operation);
        }
        match result {Ok(())=>Ok(id),Err(error)=>Err(PolicyError::Episode(error))}
    }
    /// A retired unsealed reservation keeps its original no-op behavior. A
    /// rejected gate never changes declarations; successful sealing uses the
    /// actual supplied dependency list and actual Episode command outcome.
    pub fn seal_declarations(&mut self,id:usize,dependencies:Vec<Port>)->(out:Result<(),PolicyError>)
        requires old(self).wf(),
        ensures final(self).wf(),old(self).history().prefix_of(final(self).history()),
            seal_trace(old(self).history(),final(self).history(),id,dependencies@,out),
            gate_result(old(self).observation(),Gate::Seal {id})!=Ok(true) ==> final(self).observation()==old(self).observation(),
            out.is_ok() ==> gate_result(old(self).observation(),Gate::Seal {id})==Ok(false)
                || (final(self).observation().episodes.contains_key(id) && final(self).observation().episodes[id].sealed
                    && final(self).observation().interfaces.contains_key(id) && final(self).observation().interfaces[id].dependencies@==dependencies@),
    {
        proof {reveal(seal_trace);}
        let ghost initial=self.history();
        let gate=self.gate(Gate::Seal {id});
        proof {initial.prefix_append(self.observation(),Event::Gate {gate:Gate::Seal {id},out:gate});}
        match gate {Err(error)=>return Err(error),Ok(false)=>return Ok(()),Ok(true)=>{}}
        let ghost gated=self.history();
        let configuration=self.configure_pending_dependencies(id,dependencies);
        proof {
            gated.prefix_append(self.observation(),self.history().events.last());
            initial.prefix_transitive(gated,self.history());
            self.history().last_step();reveal(history::operation);
        }
        if let Err(error)=configuration {return Err(PolicyError::Kernel(error));}
        let ghost configured=self.history();
        let out=self.episode_command(EpisodeCommand::Seal {id,sealed:true});
        proof {
            configured.prefix_append(self.observation(),self.history().events.last());
            initial.prefix_transitive(configured,self.history());
            self.history().last_step();reveal(history::operation);
        }
        match out {Ok(())=>Ok(()),Err(error)=>Err(PolicyError::Episode(error))}
    }
}

pub open spec fn overlaps(a:Seq<Port>,b:Seq<Port>)->bool {
    exists|p:Port|a.contains(p) && b.contains(p)
}
fn intersects(a:&[Port],b:&[Port])->(out:bool)
    ensures out==overlaps(a@,b@),
{
    let mut i=0;
    while i<a.len()
        invariant i<=a.len(),forall|j:int|0<=j<i ==> !b@.contains(a@[j]),
        decreases a.len()-i,
    {
        let mut j=0;
        while j<b.len()
            invariant i<a.len(),j<=b.len(),forall|k:int|0<=k<j ==> b@[k]!=a@[i as int],
            decreases b.len()-j,
        {
            if a[i]==b[j] {
                assert(a@.contains(a@[i as int]));assert(b@.contains(a@[i as int]));
                assert(overlaps(a@,b@));return true;
            }
            j+=1;
        }
        assert(!b@.contains(a@[i as int]));i+=1;
    }
    assert(!overlaps(a@,b@));false
}
pub open spec fn selected(a:Observation,id:usize,ports:Seq<Port>)->bool {
    a.interfaces.contains_key(id) && a.episodes.contains_key(id) && !a.episodes[id].cleanup_failed
        && overlaps(a.interfaces[id].dependencies@,ports)
}
pub open spec fn retry_set(a:Observation,ports:Seq<Port>)->Set<usize> {
    a.interfaces.dom().filter(|id:usize|selected(a,id,ports))
}
pub open spec fn cleared(episodes:Map<usize,Episode>,ids:Set<usize>)->Map<usize,Episode> {
    Map::new(episodes.dom(),|id:usize|if ids.contains(id) {Episode {failed:None,..episodes[id]}} else {episodes[id]})
}
pub proof fn clear_one(episodes:Map<usize,Episode>,done:Set<usize>,id:usize)
    requires episodes.contains_key(id),
    ensures cleared(episodes,done.insert(id))==cleared(episodes,done).insert(id,Episode {failed:None,..episodes[id]}),
{assert(cleared(episodes,done.insert(id)) =~= cleared(episodes,done).insert(id,Episode {failed:None,..episodes[id]}));}
impl NodeRuntime {
    /// Select from the real interface map; the adapter cannot supply a partial
    /// affected-consumer list or clear a failed cleanup through notification.
    pub(super) fn retry_notified(&mut self,ports:&[Port])
        requires old(self).observation().wf(),
        ensures final(self).observation()==(Observation {episodes:cleared(old(self).observation().episodes,retry_set(old(self).observation(),ports@)),..old(self).observation()}),
            final(self).history()==old(self).history(),
    {
        let ghost before=self.observation();let ghost affected=retry_set(before,ports@);let ghost mut visited:Set<usize>=Set::empty();
        let mut iter=self.interfaces.iter();let ghost all=iter.remaining();let count=self.interfaces.len();let mut i=0;
        proof {
            assert(affected.intersect(visited) =~= Set::empty());
            assert(cleared(before.episodes,Set::empty()) =~= before.episodes);
            assert(self.observation()==(Observation {episodes:cleared(before.episodes,affected.intersect(visited)),..before}));
        }
        while i<count
            invariant i<=count,all.len()==count,iter.obeys_prophetic_iter_laws(),iter.remaining()==all.skip(i as int),
                affected==retry_set(before,ports@),
                self.history()==old(self).history(),
                self.observation()==(Observation {episodes:cleared(before.episodes,affected.intersect(visited)),..before}),
                visited==all.take(i as int).map(|_:int,p:(&usize,&Interface)|*p.0).to_set(),
                forall|j:int|0<=j<all.len() ==> before.interfaces.contains_key(*all[j].0) && before.interfaces[*all[j].0]==*all[j].1,
                forall|id:usize|before.interfaces.contains_key(id) ==> all.contains((&id,&before.interfaces[id])),
            decreases count-i,
        {
            let (id,interface)=iter.next().unwrap();let ghost done=affected.intersect(visited);
            assert(*id==*all[i as int].0 && *interface==*all[i as int].1);
            let should_retry=if let Some(e)=self.episodes.get(id) {!e.cleanup_failed && intersects(interface.dependencies.as_slice(),ports)} else {false};
            assert(should_retry==selected(before,*id,ports@));
            if should_retry {
                self.episodes.get_mut(id).unwrap().failed=None;
                proof {clear_one(before.episodes,done,*id);}
            }
            proof {
                visited=visited.insert(*id);
                vstd::set::lemma_set_filter(before.interfaces.dom(),|id:usize|selected(before,id,ports@),*id);
                assert(affected.contains(*id)==should_retry);
                assert(affected.intersect(visited) =~= if should_retry {done.insert(*id)} else {done});
                assert(self.episodes@ =~= cleared(before.episodes,affected.intersect(visited)));
                assert(all.take(i+1).map(|_:int,p:(&usize,&Interface)|*p.0) =~= all.take(i as int).map(|_:int,p:(&usize,&Interface)|*p.0).push(*id));
                all.take(i as int).map(|_:int,p:(&usize,&Interface)|*p.0).lemma_push_to_set_commute(*id);
            }
            i+=1;
        }
        assert(affected.subset_of(visited)) by {
            assert forall|id:usize|affected.contains(id) implies visited.contains(id) by {
                let j=choose|j:int|0<=j<all.len() && all[j]==(&id,&before.interfaces[id]);
                assert(all.map(|_:int,p:(&usize,&Interface)|*p.0)[j]==id);
                assert(visited.contains(id));
            }
        }
        assert(affected.intersect(visited) =~= affected);
    }
}
impl History {
    /// Notification changes only failure flags of exactly the matching,
    /// cleanup-unblocked consumers, and only under the frozen Harness profile.
    pub proof fn notification_frame(&self,index:int,id:usize)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is Notify,self.states[index].episodes.contains_key(id),
        ensures {
            let a=self.states[index];let b=self.states[index+1];let e=self.events[index];
            &&& b.episodes.contains_key(id)
            &&& b.episodes[id]==if e->Notify_out.is_ok() && a.policy.profile==Profile::Harness && selected(a,id,e->Notify_ports)
                {Episode {failed:None,..a.episodes[id]}} else {a.episodes[id]}
            &&& a.episodes[id].cleanup_failed ==> b.episodes[id]==a.episodes[id]
        },
    {assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);}
}
}
