//! Exact typed configuration states indexed into the shared execution Journal.
//! Only the real production wrapper constructs these entries. Payloads and old
//! Futures erase; current plans remain exclusively owned by the protocol.
use crate::configuration_transaction::Configuration;
use crate::reversible_value::joint::{self, configuration as r};
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn shape<S,R,K,U>(state:Configuration<S,R,K,U>,index:nat)->r::State {
    r::State {index,version:state.version(),pending:state.staged().is_some(),phase:state.structural_phase(),
        length:state.batch().entries().len(),applied:state.batch().applied(),attempted:state.batch().attempted(),restoring:state.batch().restoring()}
}
pub open spec fn step<S,R,K,U>(a:Configuration<S,R,K,U>,b:Configuration<S,R,K,U>,event:r::Event)->bool {
    &&& a.wf() && b.wf() && r::step(shape(a,0),shape(b,1),event)
    &&& match event {
        r::Event::Begin {..}=>b.accepted()==a.accepted(),
        r::Event::Update {..}|r::Event::Rollback {..}=>b.accepted()==a.accepted() && b.staged()==a.staged(),
        r::Event::Structure {..}=>b.accepted()==a.accepted() && b.batch()==a.batch(),
        r::Event::Commit=>b.accepted()==a.staged().unwrap().candidate && a.batch().complete()
            && (a.structural_phase().is_some() ==> a.forward_steps()==crate::configuration_transaction::forward_stages()),
        r::Event::Recover=>a.structural_phase().is_some() ==> a.recovery_steps()==crate::configuration_transaction::recovery_stages(),
        r::Event::Refresh=>b.batch()==a.batch() && b.staged()==a.staged(),
    }
}
pub proof fn project_step<S,R,K,U>(a:Configuration<S,R,K,U>,b:Configuration<S,R,K,U>,event:r::Event,index:nat)
    requires step(a,b,event),ensures r::step(shape(a,index),shape(b,index+1),event),
{reveal(r::step);}
pub struct History<S,R,K,U> {pub states:Seq<Configuration<S,R,K,U>>,pub events:Seq<r::Event>}
impl<S,R,K,U> History<S,R,K,U> {
    pub open spec fn valid(&self)->bool {
        self.states.len()==self.events.len()+1 && self.states[0].wf() && self.states[0].version()==0 && self.states[0].staged().is_none()
            && forall|i:int|0<=i<self.events.len() ==> step(self.states[i],self.states[i+1],#[trigger] self.events[i])
    }
    pub open spec fn indexed(&self,positions:Seq<nat>,frames:Seq<joint::Frame>,key:nat)->bool {
        &&& positions.len()==self.states.len()
        &&& forall|i:int|0<=i<self.states.len() ==> #[trigger] positions[i]<frames.len()
            && frames[positions[i] as int].event.key==key
            && frames[positions[i] as int].event.after==(joint::Record::Configuration {state:shape(self.states[i],i as nat)})
            && frames[positions[i] as int].event.change==if i==0 {joint::Change::Allocate} else {joint::Change::Configuration {event:self.events[i-1]}}
        &&& forall|i:int,j:int|0<=i<j<self.states.len() ==> #[trigger] positions[i]<#[trigger] positions[j]
    }
    pub proof fn extend_indexed(&self,positions:Seq<nat>,before:Seq<joint::Frame>,after:Seq<joint::Frame>,key:nat)
        requires self.indexed(positions,before,key),before.len()<=after.len(),after.take(before.len() as int)==before,
        ensures self.indexed(positions,after,key),
    {
        assert forall|i:int|0<=i<self.states.len() implies #[trigger] positions[i]<after.len()
            && after[positions[i] as int].event.key==key
            && after[positions[i] as int].event.after==(joint::Record::Configuration {state:shape(self.states[i],i as nat)})
            && after[positions[i] as int].event.change==if i==0 {joint::Change::Allocate} else {joint::Change::Configuration {event:self.events[i-1]}} by {
            assert(after[positions[i] as int]==before[positions[i] as int]);
        }
    }
    pub open spec fn append(&self,next:Configuration<S,R,K,U>,event:r::Event)->Self {Self {states:self.states.push(next),events:self.events.push(event)}}
    pub proof fn extended(&self,next:Configuration<S,R,K,U>,event:r::Event)
        requires self.valid(),step(self.states.last(),next,event),ensures self.append(next,event).valid(),
    {
        assert forall|i:int|0<=i<self.events.len()+1 implies step(self.states.push(next)[i],self.states.push(next)[i+1],#[trigger] self.events.push(event)[i]) by {
            if i<self.events.len() {assert(step(self.states[i],self.states[i+1],self.events[i]));}
        }
    }
    pub proof fn append_indexed(&self,positions:Seq<nat>,before:Seq<joint::Frame>,after:Seq<joint::Frame>,key:nat,next:Configuration<S,R,K,U>,event:r::Event)
        requires self.valid(),self.indexed(positions,before,key),before.len()<after.len(),after.take(before.len() as int)==before,
            after.last().event.key==key,after.last().event.change==(joint::Change::Configuration {event}),
            after.last().event.after==(joint::Record::Configuration {state:shape(next,self.states.len())}),
        ensures self.append(next,event).indexed(positions.push((after.len()-1) as nat),after,key),
    {
        self.extend_indexed(positions,before,after,key);let updated=positions.push((after.len()-1) as nat);
        assert forall|i:int,j:int|0<=i<j<self.states.len()+1 implies #[trigger] updated[i]<#[trigger] updated[j] by {
            if j==self.states.len() {assert(positions[i]<before.len());}
        }
    }
    pub proof fn accepted_origin(&self,end:int)
        requires self.valid(),0<=end<self.states.len(),
        ensures self.states[end].accepted()==self.states[0].accepted() || exists|i:int|0<=i<end
            && (self.events[i]==r::Event::Commit || self.events[i]==r::Event::Recover || self.events[i]==r::Event::Refresh)
            && self.states[end].accepted()==self.states[i+1].accepted(),
        decreases end,
    {
        if end>0 {
            let i=end-1;assert(step(self.states[i],self.states[end],self.events[i]));
            if !(self.events[i]==r::Event::Commit || self.events[i]==r::Event::Recover || self.events[i]==r::Event::Refresh) {self.accepted_origin(i);}
        }
    }
    /// An accepted commit entails the real owned success prefix and candidate.
    pub proof fn commit_inputs(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),self.events[index]==r::Event::Commit,
        ensures self.states[index].staged().is_some(),self.states[index].batch().complete(),
            self.states[index+1].accepted()==self.states[index].staged().unwrap().candidate,
            self.states[index+1].version()==self.states[index].version()+1,
            self.states[index].structural_phase().is_some() ==> self.states[index].forward_steps()==crate::configuration_transaction::forward_stages(),
    {assert(step(self.states[index],self.states[index+1],self.events[index]));reveal(r::step);}
}
#[allow(dead_code)]
pub(crate) struct Ledger<S,R,K,U> {history:Ghost<History<S,R,K,U>>,positions:Ghost<Seq<nat>>,member:joint::Member}
impl<S,R,K,U> Ledger<S,R,K,U> {
    pub closed spec fn history(&self)->History<S,R,K,U> {self.history@}
    pub closed spec fn positions(&self)->Seq<nat> {self.positions@}
    pub closed spec fn frames(&self)->Seq<joint::Frame> {self.member.events()}
    pub closed spec fn journal(&self)->joint::Journal {self.member.journal()}
    pub closed spec fn key(&self)->nat {self.member.key()}
    pub open spec fn current(&self)->Configuration<S,R,K,U> {self.history().states.last()}
    pub open spec fn record(&self)->r::State {shape(self.current(),self.history().events.len())}
    pub closed spec fn wf(&self)->bool {
        self.history().valid() && self.member.wf() && self.member.record()==(joint::Record::Configuration {state:self.record()})
            && self.history().indexed(self.positions(),self.member.events(),self.key())
    }
    pub(crate) fn new(journal:&joint::Journal,Ghost(initial):Ghost<Configuration<S,R,K,U>>)->(out:Self)
        requires initial.wf(),initial.version()==0,initial.staged().is_none(),
        ensures out.wf(),out.journal()==*journal,out.current()==initial,out.history().events.len()==0,
    {
        let member=journal.allocate(Ghost(joint::Record::Configuration {state:shape(initial,0)}));
        let ghost positions=seq![(member.events().len()-1) as nat];
        Self {history:Ghost(History {states:seq![initial],events:Seq::empty()}),positions:Ghost(positions),member}
    }
    pub(crate) fn advance(&mut self,Ghost(next):Ghost<Configuration<S,R,K,U>>,Ghost(event):Ghost<r::Event>)
        requires old(self).wf(),step(old(self).current(),next,event),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).history()==old(self).history().append(next,event),final(self).current()==next,
            old(self).frames().len()<final(self).frames().len(),final(self).frames().take(old(self).frames().len() as int)==old(self).frames(),
    {
        let ghost prior=*self;
        proof {project_step(self.current(),next,event,self.history().events.len());reveal(joint::changes);}
        self.member.update(Ghost(joint::Record::Configuration {state:shape(next,self.history().events.len()+1)}),Ghost(joint::Change::Configuration {event}));
        proof {
            prior.history().extended(next,event);
            prior.history().append_indexed(prior.positions(),prior.frames(),self.frames(),self.key(),next,event);
            self.history=Ghost(prior.history().append(next,event));self.positions=Ghost(prior.positions().push((self.frames().len()-1) as nat));
        }
    }
    pub(crate) fn domain(&self)->(out:joint::Journal) ensures out==self.journal(), {self.member.domain()}
    pub(crate) fn certify_write(&self,view:&joint::WriteView)
        requires self.wf(),view.wf(),view.journal_spec()==self.journal(),
        ensures view.state().contains_pair(self.key(),joint::Record::Configuration {state:self.record()}),
    {self.member.certify_write(view);}
    pub(crate) fn certify(&self,view:&joint::ReadView)
        requires self.wf(),view.wf(),view.journal_spec()==self.journal(),
        ensures view.state().contains_pair(self.key(),joint::Record::Configuration {state:self.record()}),
            self.frames().len()<=view.events().len(),view.events().take(self.frames().len() as int)==self.frames(),
    {self.member.certify(view);}
    pub(crate) fn capture(&self,snapshot:joint::Snapshot)->(out:Snapshot<S,R,K,U>)
        requires self.wf(),snapshot.certified(),snapshot.journal_spec()==self.journal(),
            self.frames().len()<=snapshot.events().len(),snapshot.events().take(self.frames().len() as int)==self.frames(),
            snapshot.last().contains_pair(self.key(),joint::Record::Configuration {state:self.record()}),
        ensures out.certified(),out.history()==self.history(),out.key()==self.key(),out.joint_spec()==snapshot,
    {
        proof {self.history().extend_indexed(self.positions(),self.frames(),snapshot.events(),self.key());}
        Snapshot {joint:snapshot,history:Ghost(self.history()),positions:Ghost(self.positions()),key:Ghost(self.key())}
    }
    pub(crate) fn snapshot(&self)->(out:Snapshot<S,R,K,U>)
        requires self.wf(),
        ensures out.certified(),out.history()==self.history(),out.key()==self.key(),out.joint_spec().journal_spec()==self.journal(),
    {
        let snapshot=self.member.observe();
        proof {self.history().extend_indexed(self.positions(),self.frames(),snapshot.events(),self.key());}
        Snapshot {joint:snapshot,history:Ghost(self.history()),positions:Ghost(self.positions()),key:Ghost(self.key())}
    }
}
#[allow(dead_code)]
pub struct Snapshot<S,R,K,U> {joint:joint::Snapshot,history:Ghost<History<S,R,K,U>>,positions:Ghost<Seq<nat>>,key:Ghost<nat>}
impl<S,R,K,U> Snapshot<S,R,K,U> {
    pub closed spec fn history(&self)->History<S,R,K,U> {self.history@}
    pub closed spec fn key(&self)->nat {self.key@}
    pub closed spec fn positions(&self)->Seq<nat> {self.positions@}
    pub closed spec fn joint_spec(&self)->joint::Snapshot {self.joint}
    pub closed spec fn certified(&self)->bool {
        self.joint_spec().certified() && self.history().valid()
            && self.history().indexed(self.positions(),self.joint_spec().events(),self.key())
            && self.joint_spec().last().contains_pair(self.key(),joint::Record::Configuration {state:shape(self.history().states.last(),self.history().events.len())})
    }
    pub proof fn valid_history(&self)
        requires self.certified(),ensures self.joint_spec().certified(),self.history().valid(),
            self.positions().len()==self.history().states.len(),
            self.joint_spec().last().contains_pair(self.key(),joint::Record::Configuration {state:shape(self.history().states.last(),self.history().events.len())}),
    {}
    pub(crate) proof fn position(&self,i:int)
        requires self.certified(),0<=i<self.history().states.len(),
        ensures self.positions()[i]<self.joint_spec().events().len(),
            self.joint_spec().events()[self.positions()[i] as int].event.key==self.key(),
            self.joint_spec().events()[self.positions()[i] as int].event.after==(joint::Record::Configuration {state:shape(self.history().states[i],i as nat)}),
    {}
    pub(crate) proof fn complete_at(&self,n:nat)->(index:int)
        requires self.certified(),n<self.joint_spec().events().len(),
            self.joint_spec().events()[n as int].event.key==self.key(),
        ensures 0<=index<self.history().states.len(),self.positions()[index]==n,
    {
        let frames=self.joint_spec().events();let key=self.key();let positions=self.positions();let h=self.history();
        self.joint.valid_history();
        if n<positions[0] {
            assert(joint::step(joint::state_at(frames,n),frames[n as int].state,frames[n as int].event));
            assert(joint::state_at(frames,n+1).contains_key(key));
            joint::key_persists(frames,n+1,positions[0],key);
            assert(frames[positions[0] as int].event.change==joint::Change::Allocate);
            assert(joint::step(joint::state_at(frames,positions[0]),frames[positions[0] as int].state,frames[positions[0] as int].event));
            assert(false);
        }
        if n==positions[0] {0} else {
            let start=positions[0];
            assert(0<h.states.len());assert(positions[0]<frames.len());
            assert(frames[start as int].event.after==(joint::Record::Configuration {state:shape(h.states[0],0)}));
            assert(joint::step(joint::state_at(frames,start),frames[start as int].state,frames[start as int].event));
            assert(r::recorded(frames,start+1,key));
            r::monotone(frames,start+1,n,key);r::edge(frames,n,key);
            r::monotone(frames,n+1,frames.len(),key);
            assert(r::at(frames,frames.len(),key)==(shape(h.states.last(),h.events.len())));
            let i=frames[n as int].event.after->Configuration_state.index as int;
            assert(0<=i<h.states.len());
            assert(positions[i]<frames.len());
            assert(frames[positions[i] as int].event.after==(joint::Record::Configuration {state:shape(h.states[i],i as nat)}));
            r::unique_index(frames,n,positions[i],key);
            i
        }
    }
    /// Every mutation of this configuration owner in the complete checkpoint is an
    /// indexed typed state. Other records may interleave, but none is hidden.
    pub proof fn complete_projection(&self)
        requires self.certified(),
        ensures forall|n:int| 0<=n<self.joint_spec().events().len()
            && #[trigger] self.joint_spec().events()[n].event.key==self.key() ==>
                exists|i:int| 0<=i<self.history().states.len() && self.positions()[i]==n,
    {
        assert forall|n:int| 0<=n<self.joint_spec().events().len()
            && #[trigger] self.joint_spec().events()[n].event.key==self.key() implies
                exists|i:int| 0<=i<self.history().states.len() && self.positions()[i]==n by {
            let i=self.complete_at(n as nat);assert(self.positions()[i]==n);
        }
    }
    pub fn joint(&self)->(out:&joint::Snapshot) ensures *out==self.joint_spec(), {&self.joint}
    pub fn into_joint(self)->(out:joint::Snapshot) ensures out==self.joint_spec(), {self.joint}
}
}
