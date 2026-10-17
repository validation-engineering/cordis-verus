//! Exact load/save/checkpoint history joined to its real configuration owner.
//! Current payloads stay in Source; histories, positions and review states erase.
use crate::configuration_history as configuration;
#[cfg(verus_keep_ghost)]
use crate::configuration_save::sources;
use crate::configuration_save::sources::{Event, History, Observation};
use crate::reversible_value::joint;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint::sources as r;
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn shape<P,V>(state:Observation<P,V>,configuration:nat,index:nat)->r::State {
    r::State {configuration,index,loaded:state.root.is_some()}
}
pub open spec fn kind<P,V>(event:Event<P,V>)->r::Kind {
    match event {Event::Clear=>r::Kind::Clear,Event::Load {..}=>r::Kind::Load,Event::Save {domain,..}=>r::Kind::Save {domain}}
}
pub open spec fn reviewed<P,V>(event:Event<P,V>,accepted:joint::configuration::State)->bool {
    !accepted.pending && match event {Event::Save {revision,..}=>revision==accepted.version,_=>true}
}
pub proof fn project_step<P,V>(a:Observation<P,V>,b:Observation<P,V>,event:Event<P,V>,configuration:nat,index:nat,accepted:joint::configuration::State)
    requires sources::step(a,b,event),
    ensures r::step(shape(a,configuration,index),shape(b,configuration,index+1),r::Event {kind:kind(event),accepted}),
{reveal(r::step);}
impl<P,V> History<P,V> {
    pub open spec fn indexed(&self,positions:Seq<nat>,reviews:Seq<joint::configuration::State>,frames:Seq<joint::Frame>,key:nat,configuration:nat)->bool {
        &&& positions.len()==self.states.len() && reviews.len()==self.events.len()
        &&& forall|i:int|0<=i<self.events.len() ==> #[trigger] reviewed(self.events[i],reviews[i])
        &&& forall|i:int|0<=i<self.states.len() ==> #[trigger] positions[i]<frames.len()
            && frames[positions[i] as int].event.key==key
            && frames[positions[i] as int].event.after==(joint::Record::Sources {state:shape(self.states[i],configuration,i as nat)})
            && frames[positions[i] as int].event.change==if i==0 {joint::Change::Allocate} else {joint::Change::Sources {event:r::Event {kind:kind(self.events[i-1]),accepted:reviews[i-1]}}}
        &&& forall|i:int,j:int|0<=i<j<self.states.len() ==> #[trigger] positions[i]<#[trigger] positions[j]
    }
    pub proof fn extend_indexed(&self,positions:Seq<nat>,reviews:Seq<joint::configuration::State>,before:Seq<joint::Frame>,after:Seq<joint::Frame>,key:nat,configuration:nat)
        requires self.indexed(positions,reviews,before,key,configuration),before.len()<=after.len(),after.take(before.len() as int)==before,
        ensures self.indexed(positions,reviews,after,key,configuration),
    {
        assert forall|i:int|0<=i<self.states.len() implies #[trigger] positions[i]<after.len()
            && after[positions[i] as int].event.key==key
            && after[positions[i] as int].event.after==(joint::Record::Sources {state:shape(self.states[i],configuration,i as nat)})
            && after[positions[i] as int].event.change==if i==0 {joint::Change::Allocate} else {joint::Change::Sources {event:r::Event {kind:kind(self.events[i-1]),accepted:reviews[i-1]}}} by {
            assert(after[positions[i] as int]==before[positions[i] as int]);
        }
    }
    pub proof fn append_indexed(&self,positions:Seq<nat>,reviews:Seq<joint::configuration::State>,before:Seq<joint::Frame>,after:Seq<joint::Frame>,key:nat,configuration:nat,next:Observation<P,V>,event:Event<P,V>,accepted:joint::configuration::State)
        requires self.valid(),self.indexed(positions,reviews,before,key,configuration),reviewed(event,accepted),
            before.len()<after.len(),after.take(before.len() as int)==before,
            after.last().event.key==key,after.last().event.change==(joint::Change::Sources {event:r::Event {kind:kind(event),accepted}}),
            after.last().event.after==(joint::Record::Sources {state:shape(next,configuration,self.states.len())}),
        ensures self.append(next,event).indexed(positions.push((after.len()-1) as nat),reviews.push(accepted),after,key,configuration),
    {
        self.extend_indexed(positions,reviews,before,after,key,configuration);let updated=positions.push((after.len()-1) as nat);
        assert forall|i:int,j:int|0<=i<j<self.states.len()+1 implies #[trigger] updated[i]<#[trigger] updated[j] by {
            if j==self.states.len() {assert(positions[i]<before.len());}
        }
        assert forall|i:int|0<=i<self.events.len()+1 implies #[trigger] reviewed(self.events.push(event)[i],reviews.push(accepted)[i]) by {
            if i<self.events.len() {assert(reviewed(self.events[i],reviews[i]));}
        }
    }
}
#[allow(dead_code)]
pub(crate) struct Ledger<P,V> {
    history:Ghost<History<P,V>>,positions:Ghost<Seq<nat>>,reviews:Ghost<Seq<joint::configuration::State>>,
    configuration:Ghost<nat>,member:joint::Member,
}
impl<P,V> Ledger<P,V> {
    pub closed spec fn history(&self)->History<P,V> {self.history@}
    pub closed spec fn positions(&self)->Seq<nat> {self.positions@}
    pub closed spec fn reviews(&self)->Seq<joint::configuration::State> {self.reviews@}
    pub closed spec fn frames(&self)->Seq<joint::Frame> {self.member.events()}
    pub closed spec fn journal(&self)->joint::Journal {self.member.journal()}
    pub closed spec fn key(&self)->nat {self.member.key()}
    pub closed spec fn configuration(&self)->nat {self.configuration@}
    pub open spec fn current(&self)->Observation<P,V> {self.history().states.last()}
    pub open spec fn record(&self)->r::State {shape(self.current(),self.configuration(),self.history().events.len())}
    pub closed spec fn wf(&self)->bool {
        self.history().valid() && self.member.wf() && self.member.record()==(joint::Record::Sources {state:self.record()})
            && self.history().indexed(self.positions(),self.reviews(),self.frames(),self.key(),self.configuration())
    }
    pub(crate) fn new<S,R,K,U>(configuration:&configuration::Ledger<S,R,K,U>)->(out:Self)
        requires configuration.wf(),
        ensures out.wf(),out.journal()==configuration.journal(),out.configuration()==configuration.key(),
            out.current()==Observation::<P,V>::empty(),out.history().events.len()==0,
            out.history()==(History {states:seq![Observation::<P,V>::empty()],events:Seq::empty()}),
    {
        let journal=configuration.domain();
        let member=journal.allocate(Ghost(joint::Record::Sources {state:shape(Observation::<P,V>::empty(),configuration.key(),0)}));
        let ghost positions=seq![(member.events().len()-1) as nat];
        Self {history:Ghost(History {states:seq![Observation::empty()],events:Seq::empty()}),positions:Ghost(positions),
            reviews:Ghost(Seq::empty()),configuration:Ghost(configuration.key()),member}
    }
    pub(crate) fn advance<S,R,K,U>(&mut self,configuration:&configuration::Ledger<S,R,K,U>,Ghost(next):Ghost<Observation<P,V>>,Ghost(event):Ghost<Event<P,V>>)
        requires old(self).wf(),configuration.wf(),configuration.journal()==old(self).journal(),configuration.key()==old(self).configuration(),
            sources::step(old(self).current(),next,event),reviewed(event,configuration.record()),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),final(self).configuration()==old(self).configuration(),
            final(self).history()==old(self).history().append(next,event),final(self).current()==next,
            final(self).reviews()==old(self).reviews().push(configuration.record()),
    {
        let ghost prior=*self;let ghost accepted=configuration.record();
        let journal=self.member.domain();let view=journal.write();
        self.member.certify_write(&view);configuration.certify_write(&view);
        proof {project_step(self.current(),next,event,self.configuration(),self.history().events.len(),accepted);reveal(joint::changes);}
        let view=self.member.update_guarded(view,
            Ghost(joint::Record::Sources {state:shape(next,self.configuration(),self.history().events.len()+1)}),
            Ghost(joint::Change::Sources {event:r::Event {kind:kind(event),accepted}}));
        proof {
            prior.history().extend(next,event);
            prior.history().append_indexed(prior.positions(),prior.reviews(),prior.frames(),self.frames(),self.key(),self.configuration(),next,event,accepted);
            self.history=Ghost(prior.history().append(next,event));self.positions=Ghost(prior.positions().push((self.frames().len()-1) as nat));
            self.reviews=Ghost(prior.reviews().push(accepted));
        }
        view.finish();
    }
    /// Certify the actual native member as well as both configuration owners
    /// under one read guard. No callback or payload lock is entered here.
    pub(crate) fn snapshot_with<S,R,K,U>(&self,configuration:&configuration::Ledger<S,R,K,U>,native:&joint::Member)->(out:Snapshot<S,R,K,U,P,V>)
        requires self.wf(),configuration.wf(),configuration.journal()==self.journal(),configuration.key()==self.configuration(),
            native.wf(),native.journal()==self.journal(),
        ensures out.certified(),out.history()==self.history(),out.key()==self.key(),out.reviews()==self.reviews(),
            out.configuration().history()==configuration.history(),out.configuration().key()==self.configuration(),out.joint_spec().journal_spec()==self.journal(),
            out.joint_spec().certified(),out.joint_spec().last().contains_pair(native.key(),native.record()),
            native.events().len()<=out.joint_spec().events().len(),out.joint_spec().events().take(native.events().len() as int)==native.events(),
    {
        let journal=self.member.domain();let view=journal.read();self.member.certify(&view);configuration.certify(&view);native.certify(&view);
        proof {self.history().extend_indexed(self.positions(),self.reviews(),self.frames(),view.events(),self.key(),self.configuration());}
        let snapshot=view.finish();let configuration=configuration.capture(snapshot);
        proof {reveal(Snapshot::certified);}
        Snapshot {configuration,history:Ghost(self.history()),positions:Ghost(self.positions()),reviews:Ghost(self.reviews()),key:Ghost(self.key())}
    }
    pub(crate) fn snapshot<S,R,K,U>(&self,configuration:&configuration::Ledger<S,R,K,U>)->(out:Snapshot<S,R,K,U,P,V>)
        requires self.wf(),configuration.wf(),configuration.journal()==self.journal(),configuration.key()==self.configuration(),
        ensures out.certified(),out.history()==self.history(),out.key()==self.key(),out.reviews()==self.reviews(),
            out.configuration().history()==configuration.history(),out.configuration().key()==self.configuration(),out.joint_spec().journal_spec()==self.journal(),
    {
        let journal=self.member.domain();let view=journal.read();self.member.certify(&view);configuration.certify(&view);
        proof {self.history().extend_indexed(self.positions(),self.reviews(),self.frames(),view.events(),self.key(),self.configuration());}
        let snapshot=view.finish();let configuration=configuration.capture(snapshot);
        proof {reveal(Snapshot::certified);}
        Snapshot {configuration,history:Ghost(self.history()),positions:Ghost(self.positions()),reviews:Ghost(self.reviews()),key:Ghost(self.key())}
    }
}
#[allow(dead_code)]
pub struct Snapshot<S,R,K,U,P,V> {
    configuration:configuration::Snapshot<S,R,K,U>,history:Ghost<History<P,V>>,positions:Ghost<Seq<nat>>,
    reviews:Ghost<Seq<joint::configuration::State>>,key:Ghost<nat>,
}
impl<S,R,K,U,P,V> Snapshot<S,R,K,U,P,V> {
    pub closed spec fn configuration(&self)->configuration::Snapshot<S,R,K,U> {self.configuration}
    pub closed spec fn history(&self)->History<P,V> {self.history@}
    pub closed spec fn key(&self)->nat {self.key@}
    pub closed spec fn positions(&self)->Seq<nat> {self.positions@}
    pub closed spec fn reviews(&self)->Seq<joint::configuration::State> {self.reviews@}
    pub open spec fn joint_spec(&self)->joint::Snapshot {self.configuration().joint_spec()}
    #[verifier::opaque]
    pub closed spec fn certified(&self)->bool {
        self.configuration().certified() && self.history().valid()
            && self.history().indexed(self.positions(),self.reviews(),self.joint_spec().events(),self.key(),self.configuration().key())
            && self.joint_spec().last().contains_pair(self.key(),joint::Record::Sources {state:shape(self.history().states.last(),self.configuration().key(),self.history().events.len())})
    }
    /// Export only the facts needed when composing this certificate with
    /// another typed history; callers need not reveal its implementation.
    pub proof fn valid_history(&self)
        requires self.certified(),
        ensures self.configuration().certified(),self.joint_spec().certified(),self.history().valid(),
            self.positions().len()==self.history().states.len(),self.reviews().len()==self.history().events.len(),
    {reveal(Snapshot::certified);self.configuration.valid_history();}
    proof fn facts(&self)
        requires self.certified(),
        ensures self.configuration().certified(),self.joint_spec().certified(),
            self.history().states.len()==self.history().events.len()+1,
            self.joint_spec().last().contains_pair(self.key(),joint::Record::Sources {state:shape(self.history().states.last(),self.configuration().key(),self.history().events.len())}),
    {reveal(Snapshot::certified);self.configuration.valid_history();}
    proof fn position(&self,i:int)
        requires self.certified(),0<=i<self.history().states.len(),
        ensures self.positions()[i]<self.joint_spec().events().len(),
            self.joint_spec().events()[self.positions()[i] as int].event.key==self.key(),
            self.joint_spec().events()[self.positions()[i] as int].event.after==(joint::Record::Sources {state:shape(self.history().states[i],self.configuration().key(),i as nat)}),
            self.joint_spec().events()[self.positions()[i] as int].event.change==if i==0 {joint::Change::Allocate} else {joint::Change::Sources {event:r::Event {kind:kind(self.history().events[i-1]),accepted:self.reviews()[i-1]}}},
            i>0 ==> reviewed(self.history().events[i-1],self.reviews()[i-1]),
    {reveal(Snapshot::certified);}
    proof fn complete_at(&self,n:nat)->(index:int)
        requires self.certified(),n<self.joint_spec().events().len(),self.joint_spec().events()[n as int].event.key==self.key(),
        ensures 0<=index<self.history().states.len(),self.positions()[index]==n,
    {
        let frames=self.joint_spec().events();let key=self.key();let positions=self.positions();let h=self.history();
        self.facts();self.position(0);self.joint_spec().valid_history();
        r::modification_index(frames,positions[0],n,key,h.events.len());
        let i=frames[n as int].event.after->Sources_state.index as int;
        assert(0<=i<h.states.len());self.position(i);assert(positions[i]<frames.len());
        assert(frames[positions[i] as int].event.after==(joint::Record::Sources {state:shape(h.states[i],self.configuration().key(),i as nat)}));
        r::unique_index(frames,n,positions[i],key);i
    }
    pub proof fn complete_projection(&self)
        requires self.certified(),
        ensures forall|n:int|0<=n<self.joint_spec().events().len() && #[trigger] self.joint_spec().events()[n].event.key==self.key() ==>
            exists|i:int|0<=i<self.history().states.len() && self.positions()[i]==n,
    {
        assert forall|n:int|0<=n<self.joint_spec().events().len() && #[trigger] self.joint_spec().events()[n].event.key==self.key() implies
            exists|i:int|0<=i<self.history().states.len() && self.positions()[i]==n by {
            let i=self.complete_at(n as nat);assert(self.positions()[i]==n);
        }
    }
    /// Resolve the guard to an exact typed configuration state produced earlier
    /// in this same history, including same-version recovery/refresh steps.
    pub proof fn accepted_configuration(&self,index:int)->(at:int)
        requires self.certified(),0<=index<self.history().events.len(),
        ensures 0<=at<self.configuration().history().states.len(),
            self.configuration().positions()[at]<self.positions()[index+1],
            configuration::shape(self.configuration().history().states[at],at as nat)==self.reviews()[index],
            self.configuration().history().states[at].staged().is_none(),
            self.history().events[index] is Save ==> self.history().events[index]->Save_revision==self.configuration().history().states[at].version(),
    {
        let frames=self.joint_spec().events();let pos=self.positions()[index+1];let key=self.configuration().key();
        self.facts();self.position(index+1);self.joint_spec().valid_history();
        assert(joint::step(joint::state_at(frames,pos),frames[pos as int].state,frames[pos as int].event));
        assert(frames[pos as int].event.change==(joint::Change::Sources {event:r::Event {kind:kind(self.history().events[index]),accepted:self.reviews()[index]}}));
        reveal(joint::changes);reveal(r::step);
        assert(joint::state_at(frames,pos).contains_pair(key,joint::Record::Configuration {state:self.reviews()[index]}));
        let n=joint::record_origin(frames,pos,key);let at=self.configuration.complete_at(n);self.configuration.position(at);
        at
    }
    /// A retained merge base has a real load/processed-save origin, with the
    /// corresponding accepted configuration state in the common execution.
    pub proof fn checkpoint_origin(&self,end:int,key:P)->(out:(int,int))
        requires self.certified(),0<=end<self.history().states.len(),self.history().states[end].checkpoints.contains_key(key),
        ensures 0<=out.0<end,self.history().introduces(out.0,key,self.history().states[end].checkpoints[key].value),
            0<=out.1<self.configuration().history().states.len(),self.configuration().history().states[out.1].staged().is_none(),
            self.configuration().positions()[out.1]<self.positions()[out.0+1],
            configuration::shape(self.configuration().history().states[out.1],out.1 as nat)==self.reviews()[out.0],
            self.history().events[out.0] is Save ==> self.history().events[out.0]->Save_revision==self.configuration().history().states[out.1].version(),
    {
        reveal(Snapshot::certified);self.history().checkpoint_origin(end,key);
        let event=choose|i:int|0<=i<end && self.history().introduces(i,key,self.history().states[end].checkpoints[key].value);
        let at=self.accepted_configuration(event);(event,at)
    }
    pub fn joint(&self)->(out:&joint::Snapshot) ensures *out==self.joint_spec(), {self.configuration.joint()}
    pub fn into_joint(self)->(out:joint::Snapshot) ensures out==self.joint_spec(), {self.configuration.into_joint()}
}
}
