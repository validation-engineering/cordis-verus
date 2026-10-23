//! Persistent producer evidence survives typed retirement. Every actual
//! allocation write is classified; Replace and Retire stay explicit barriers
//! to reversible recovery instead of disappearing from an inverse-only log.
use super::super::{history::Witness, joint};
use super::{Observation, SharedPayload, State};
use vstd::prelude::*;

verus! {
/// The lock invariant stores owner-independent data. Referring back to a
/// SharedPayload predicate here would form a recursive lock invariant.
#[allow(dead_code)]
pub(super) tracked struct Retained<T:?Sized> {
    ghost states:Seq<State<T>>,ghost positions:Seq<nat>,ghost revision:u64,
    history:Witness<State<T>>,ghost commit:joint::Receipt,checkpoint:joint::Receipt,
}
impl<T:?Sized> Retained<T> {
    pub(super) closed spec fn source(&self)->vstd::resource::Loc {self.history.source()}
    pub(super) closed spec fn journal(&self)->joint::Journal {self.commit.journal()}
    pub(super) closed spec fn key(&self)->nat {self.commit.event().key}
    pub(super) closed spec fn initial(&self)->std::sync::Arc<T> {self.states.first().value}
    pub(super) closed spec fn checkpoint(&self)->joint::Receipt {self.checkpoint}
    pub(super) closed spec fn wf(&self)->bool {
        self.history.wf() && self.history.events()==self.states && self.states.len()==self.revision as nat+1
            && self.states.last().head<=self.revision && self.states[self.states.last().head as int]==self.states.last()
            && self.revision as int+self.states.last().depth as int<=u64::MAX
            && self.commit.wf() && self.commit.event().after==(joint::Record::Payload {source:self.source(),revision:self.revision})
            && joint::payload::indexed(self.states.len(),self.positions,self.commit.events(),self.key(),self.source())
            && super::semantic_history::valid(self.states,self.positions,self.commit.events())
            && self.checkpoint.wf() && self.checkpoint.follows(&self.commit)
            && self.checkpoint.event().key==self.key() && self.checkpoint.event().change==joint::Change::PayloadRetire
            && self.checkpoint.event().after==(joint::Record::RetiredPayload {source:self.source(),revision:self.revision})
    }
    pub(super) proof fn new(observation:Observation<T>,tracked history:Witness<State<T>>,tracked checkpoint:joint::Receipt)->(tracked out:Self)
        requires observation.wf(),history.wf(),history.source()==observation.owner.source(),history.events()==observation.states,
            checkpoint.wf(),checkpoint.follows(&observation.commit),checkpoint.event().key==observation.owner.key(),
            checkpoint.event().change==joint::Change::PayloadRetire,
            checkpoint.event().after==(joint::Record::RetiredPayload {source:observation.owner.source(),revision:observation.revision}),
        ensures out.wf(),out.source()==observation.owner.source(),out.journal()==observation.owner.journal_spec(),out.key()==observation.owner.key(),
            out.initial()==observation.owner.initial(),out.checkpoint().same(&checkpoint),
    {
        Self {states:observation.states,positions:observation.positions,revision:observation.revision,history,commit:observation.commit,checkpoint}
    }
    proof fn bind(tracked &self,owner:SharedPayload<T>)->(tracked out:Source<T>)
        requires self.wf(),owner.source()==self.source(),owner.journal_spec()==self.journal(),owner.key()==self.key(),owner.initial()==self.initial(),
        ensures out.wf(),out.observation().owner==owner,out.checkpoint().same(&self.checkpoint()),out.retired(),
    {
        let observation=Observation {owner,revision:self.revision,value:self.states.last().value,history:super::values(self.states),states:self.states,positions:self.positions,commit:self.commit};
        assert(observation.wf());assert(self.checkpoint().events().take(self.checkpoint().events().len() as int) =~= self.checkpoint().events());
        Source {observation,history:self.history.duplicate(),checkpoint:self.checkpoint.duplicate(),observed:self.checkpoint.duplicate(),retired:true}
    }
}
#[allow(dead_code)]
pub tracked struct Source<T:?Sized> {ghost observation:Observation<T>,history:Witness<State<T>>,checkpoint:joint::Receipt,observed:joint::Receipt,ghost retired:bool}
impl<T:?Sized> Source<T> {
    pub closed spec fn observation(&self)->Observation<T> {self.observation}
    pub closed spec fn checkpoint(&self)->joint::Receipt {self.checkpoint}
    pub closed spec fn observation_cut(&self)->joint::Receipt {self.observed}
    pub closed spec fn retired(&self)->bool {self.retired}
    pub closed spec fn wf(&self)->bool {
        self.observation().wf() && self.history.wf() && self.history.source()==self.observation().owner.source()
            && self.history.events()==self.observation().states && self.checkpoint().wf()
            && self.observation_cut().wf() && self.observation_cut().covers(&self.checkpoint())
            && joint::ownership::quiet(self.observation_cut().events(),self.checkpoint().events().len(),self.observation_cut().events().len(),self.observation().owner.key())
            && if self.retired() {
                self.checkpoint().follows(&self.observation().commit) && self.checkpoint().event().key==self.observation().owner.key()
                    && self.checkpoint().event().change==joint::Change::PayloadRetire
                    && self.checkpoint().event().after==(joint::Record::RetiredPayload {source:self.observation().owner.source(),revision:self.observation().revision})
            } else {self.checkpoint().same(&self.observation().commit)}
    }
    pub proof fn facts(&self)
        requires self.wf(),
        ensures self.observation().wf(),self.checkpoint().wf(),self.checkpoint().covers(&self.observation().commit),
            self.observation_cut().wf(),self.observation_cut().covers(&self.checkpoint()),
            joint::ownership::quiet(self.observation_cut().events(),self.checkpoint().events().len(),self.observation_cut().events().len(),self.observation().owner.key()),
            self.retired() ==> self.checkpoint().follows(&self.observation().commit)
                && self.checkpoint().event().key==self.observation().owner.key() && self.checkpoint().event().change==joint::Change::PayloadRetire,
            !self.retired() ==> self.checkpoint().same(&self.observation().commit),
    {if !self.retired() {assert(self.checkpoint().events().take(self.checkpoint().events().len() as int) =~= self.checkpoint().events());}}
    pub open spec fn positions(&self)->Seq<nat> {
        if self.retired() {self.observation().positions.push(self.checkpoint().at())} else {self.observation().positions}
    }
    #[verifier::spinoff_prover]
    pub proof fn extend_cut(tracked &mut self,tracked cut:joint::Receipt)
        requires old(self).wf(),cut.wf(),cut.covers(&old(self).checkpoint()),
            !old(self).retired() ==> joint::state_at(cut.events(),cut.events().len()).contains_pair(old(self).observation().owner.key(),old(self).checkpoint().event().after),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),final(self).checkpoint()==old(self).checkpoint(),
            final(self).retired()==old(self).retired(),final(self).observation_cut()==cut,
    {
        hide(joint::valid);hide(joint::step);
        let end=self.checkpoint();let key=self.observation().owner.key();let f=cut.events();let from=end.events().len();
        assert(f[end.at() as int]==end.events()[end.at() as int]);
        assert(joint::step(joint::state_at(f,end.at()),f[end.at() as int].state,end.event())) by {reveal(joint::valid);}
        reveal(joint::step);
        assert forall|at:int|from<=at<f.len() implies (#[trigger] f[at]).event.key!=key by {
            joint::payload::retained(f,from,at as nat,key);joint::payload::edge(f,at as nat,key);
            joint::payload::retained(f,at as nat+1,f.len(),key);
            if f[at].event.key==key {assert(false);}
        }
        self.observed=cut;
    }
    pub proof fn duplicate(tracked &self)->(tracked out:Self)
        requires self.wf(),ensures out.wf(),out.observation()==self.observation(),out.checkpoint().same(&self.checkpoint()),out.observation_cut().same(&self.observation_cut()),out.retired()==self.retired(),
    {Self {observation:self.observation,history:self.history.duplicate(),checkpoint:self.checkpoint.duplicate(),observed:self.observed.duplicate(),retired:self.retired}}
    pub(crate) proof fn witness(tracked &self)->(tracked out:Witness<State<T>>)
        requires self.wf(),ensures out.wf(),out.source()==self.observation().owner.source(),out.events()==self.observation().states,
    {self.history.duplicate()}
    /// Classify every producer write, including the terminal retirement. The
    /// caller does not supply an external-coverage premise.
    pub proof fn source_at(&self,at:nat)->(i:int)
        requires self.wf(),at<self.observation_cut().events().len(),self.observation_cut().events()[at as int].event.key==self.observation().owner.key(),
        ensures 0<=i<self.positions().len(),self.positions()[i]==at,
    {
        let v=self.observation();let end=self.checkpoint();let frames=end.events();let key=v.owner.key();
        assert(at<end.events().len());assert(frames[at as int]==self.observation_cut().events()[at as int]);
        if self.retired() && at==end.at() {v.positions.len() as int} else {
            if self.retired() && at>=v.commit.events().len() {
                assert(joint::step(joint::state_at(frames,v.commit.at()),frames[v.commit.at() as int].state,frames[v.commit.at() as int].event));
                joint::payload::retained(frames,v.commit.events().len(),at,key);joint::payload::edge(frames,at,key);
                joint::payload::retained(frames,at+1,end.at(),key);joint::payload::edge(frames,end.at(),key);
                assert(false);
            }
            let i=joint::payload::complete_at(v.commit.events(),v.positions,key,v.owner.source(),v.states.len(),at);
            i
        }
    }
    pub proof fn restore_origin(&self,i:int)->(created:int)
        requires self.wf(),0<i<self.observation().states.len(),
            self.checkpoint().events()[self.positions()[i] as int].event.change==joint::Change::PayloadRestore,
        ensures created==self.observation().states[i-1].head,0<created<i,self.checkpoint().events()[self.positions()[created] as int].event.change==joint::Change::PayloadApply,
            self.observation().states[i-1]==self.observation().states[created],self.observation().states[i]==self.observation().states[created-1],
            forall|j:int|0<j<self.observation().states.len() && (#[trigger] self.observation().states[j-1]).head==self.observation().states[i-1].head
                && self.checkpoint().events()[self.positions()[j] as int].event.change==joint::Change::PayloadRestore ==> j==i,
    {
        let v=self.observation();let f=v.commit.events();let head=v.states[i-1].head as int;
        assert(f[v.positions[i] as int]==self.checkpoint().events()[self.positions()[i] as int]);
        super::semantic_history::restore_origin(v.states,v.positions,f,i);
        assert forall|j:int|0<j<v.states.len() && (#[trigger] v.states[j-1]).head==v.states[i-1].head
            && self.checkpoint().events()[self.positions()[j] as int].event.change==joint::Change::PayloadRestore implies j==i by {
            assert(f[v.positions[j] as int]==self.checkpoint().events()[self.positions()[j] as int]);
            super::semantic_history::unique_restore(v.states,v.positions,f,i,j);
        }
        head
    }
}
impl<T:?Sized> SharedPayload<T> {
    /// Capture a complete producer through a real shared read cut, including
    /// after retirement. The optional cause is certified under that same read.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    pub fn source_snapshot_in(&self,journal:&joint::Journal,Tracked(cause):Tracked<Option<&joint::Receipt>>)->(out:Tracked<Source<T>>)
        requires *journal==self.journal_spec(),cause.is_some() ==> cause.unwrap().wf(),
        ensures out@.wf(),out@.observation().owner==*self,
            cause.is_some() && cause.unwrap().journal()==*journal ==> out@.observation_cut().covers(cause.unwrap()),
    {
        let guard=self.inner.acquire_read();let storage=guard.borrow();
        let tracked mut out;
        let tracked mut receipts=Map::<u8,joint::Receipt>::tracked_empty();
        if let Some(cell)=&storage.live {
            let _observed=cell.evidence(self);
            proof {
                assert(cell.member.events().take(cell.member.events().len() as int) =~= cell.member.events());
                out=Source {observation:_observed@,history:cell.authority.borrow().snapshot(),checkpoint:cell.member.receipt(),observed:cell.member.receipt(),retired:false};
            }
        } else {proof {out=storage.retired_source.borrow().tracked_borrow().bind(*self);}}
        proof {assert(out.wf());out.facts();receipts.tracked_insert(0,out.checkpoint.duplicate());if let Some(cause)=cause {receipts.tracked_insert(1,cause.duplicate());}}
        let view=journal.read();
        if let Some(cell)=&storage.live {cell.member.certify(&view);}
        view.certify_receipts::<u8>(Tracked(&receipts));view.valid_history();
        proof {assert(receipts[0].journal()==view.journal_spec());assert(receipts[0].wf());assert(view.events().len()>=receipts[0].events().len());}
        let snapshot=view.finish();let Tracked(cut)=snapshot.checkpoint_receipt();
        proof {
            if let Some(cause)=cause {if cause.journal()==*journal {assert(receipts[1].same(cause));assert(cut.covers(cause));}}
            out.extend_cut(cut);
        }
        guard.release_read();Tracked(out)
    }
    /// The real storage lock supplies live or retained terminal evidence. This
    /// also works after `capture()` starts returning None on retirement.
    pub fn source_snapshot(&self)->(out:Tracked<Source<T>>)
        ensures out@.wf(),out@.observation().owner.source()==self.source(),
            out@.observation().owner.journal_spec()==self.journal_spec(),out@.observation().owner.key()==self.key(),
    {
        let guard=self.inner.acquire_read();let storage=guard.borrow();
        let tracked out;if let Some(cell)=&storage.live {
                let _observed=cell.evidence(self);
                proof {assert(cell.member.events().take(cell.member.events().len() as int) =~= cell.member.events());out=Source {observation:_observed@,history:cell.authority.borrow().snapshot(),checkpoint:cell.member.receipt(),observed:cell.member.receipt(),retired:false};}
        } else {proof {out=storage.retired_source.borrow().tracked_borrow().bind(*self);}}
        guard.release_read();Tracked(out)
    }
}
}
