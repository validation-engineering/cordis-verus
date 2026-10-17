//! Production configuration execution in the native value/lifecycle Journal.
//! User callbacks run before recording, outside the Journal lock. No mutable
//! access to the protocol owner escapes this composition boundary.
use crate::configuration_batch::{Action, Batch, StepError};
#[cfg(verus_keep_ghost)]
use crate::configuration_history as history;
use crate::configuration_history::{Ledger, Snapshot};
use crate::configuration_save::{
    sources::{self, Source, Target},
    Save,
};
use crate::configuration_source_history as source_history;
use crate::configuration_transaction::{
    Configuration, Pending, Rejected, SaveStamp, Structure, StructureError, TransactionError,
};
use crate::reversible_value::joint::{self, configuration as r};
use std::collections::BTreeMap;
use std::task::Poll;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::btree::key_obeys_cmp_spec;
verus! {
/// Actual loaded inputs. Rejection returns these inputs unchanged.
#[derive(Debug)]
pub struct Load<P,V> {pub root:P,pub contents:BTreeMap<P,String>,pub checkpoints:Vec<(P,V)>,pub resolutions:BTreeMap<P,P>}
pub struct Recorded<S,R,K,U,P=(),V=()> {
    inner:Configuration<S,R,K,U>,ledger:Ledger<S,R,K,U>,sources:Source<P,V>,source_ledger:source_history::Ledger<P,V>,
}
impl<S,R,K,U,P:Ord,V> Recorded<S,R,K,U,P,V> {
    pub closed spec fn core(&self)->Configuration<S,R,K,U> {self.inner}
    pub closed spec fn history(&self)->history::History<S,R,K,U> {self.ledger.history()}
    pub closed spec fn journal(&self)->joint::Journal {self.ledger.journal()}
    pub closed spec fn key(&self)->nat {self.ledger.key()}
    pub closed spec fn source(&self)->Source<P,V> {self.sources}
    pub closed spec fn source_key(&self)->nat {self.source_ledger.key()}
    closed spec fn configuration_wf(&self)->bool {self.core().wf() && self.ledger.wf() && self.ledger.current()==self.core()}
    closed spec fn source_wf(&self)->bool {
        self.sources.wf() && self.source_ledger.wf() && self.sources.history()==self.source_ledger.history()
            && self.source_ledger.journal()==self.journal() && self.source_ledger.configuration()==self.key()
    }
    pub closed spec fn wf(&self)->bool {self.configuration_wf() && self.source_wf()}
    fn record(&mut self,Ghost(event):Ghost<r::Event>)
        requires old(self).source_wf(),old(self).core().wf(),old(self).ledger.wf(),history::step(old(self).ledger.current(),old(self).core(),event),
        ensures final(self).wf(),final(self).core()==old(self).core(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).history()==old(self).history().append(old(self).core(),event),
            final(self).source()==old(self).source(),final(self).source_ledger==old(self).source_ledger,
    {self.ledger.advance(Ghost(self.core()),Ghost(event));}
    pub fn new_in(journal:&joint::Journal,current:S)->(out:Self)
        ensures out.wf(),out.journal()==*journal,out.core().accepted()==current,out.core().version()==0,out.core().staged().is_none(),
            out.history().events.len()==0,out.source().history().events.len()==0,out.source().observation()==sources::Observation::<P,V>::empty(),
    {
        let inner=Configuration::new(current);let ledger=Ledger::new(journal,Ghost(inner));
        let sources=Source::new();let source_ledger=source_history::Ledger::new(&ledger);
        proof {
            assert(sources.history().states =~= source_ledger.history().states);
            assert(sources.history().events =~= source_ledger.history().events);
        }
        Self {inner,ledger,sources,source_ledger}
    }
    pub fn new(current:S)->(out:Self)
        ensures out.wf(),out.core().accepted()==current,out.core().version()==0,out.core().staged().is_none(),out.history().events.len()==0,out.source().history().events.len()==0,out.source().observation()==sources::Observation::<P,V>::empty(),
    {Self::new_in(&joint::Journal::new(),current)}
    pub fn protocol(&self)->(out:&Configuration<S,R,K,U>) ensures *out==self.core(), {&self.inner}
    pub fn current(&self)->(out:&S) ensures *out==self.core().accepted(), {self.inner.current()}
    pub fn revision(&self)->(out:u64) ensures out==self.core().version(), {self.inner.revision()}
    pub fn pending(&self)->(out:Option<&Pending<S,R>>)
        ensures out.is_some()==self.core().staged().is_some(),out.is_some() ==> *out.unwrap()==self.core().staged().unwrap(),
    {self.inner.pending()}
    pub fn updates(&self)->(out:&Batch<K,U>) ensures *out==self.core().batch(), {self.inner.updates()}
    pub fn structure(&self)->(out:Option<Structure>) ensures out==self.core().structural_phase(), {self.inner.structure()}
    pub fn check_begin(&self)->(out:Result<(),TransactionError>)
        ensures out.is_ok()==(self.core().staged().is_none() && self.core().version()<u64::MAX),
    {self.inner.check_begin()}
    pub fn save_stamp(&self,domain:u64)->(out:Option<SaveStamp>)
        requires self.wf(),ensures out.is_some()==self.core().staged().is_none(),
            out.is_some() ==> out.unwrap().domain()==domain && out.unwrap().revision()==self.core().version(),
    {self.inner.save_stamp(domain)}
    pub fn accepts_save(&self,domain:u64,stamp:&SaveStamp)->(out:bool)
        requires self.wf(),ensures out==(self.core().staged().is_none() && domain==stamp.domain() && self.core().version()==stamp.revision()),
    {self.inner.accepts_save(domain,stamp)}
    pub fn begin_structural(&mut self,candidate:S,recovery:R,updates:Vec<Action<K,U>>)->(out:Result<(),Rejected<S,R,K,U>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).source()==old(self).source(),final(self).source_key()==old(self).source_key(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> final(self).core().staged()==Some(Pending {candidate,recovery}) && final(self).core().batch().entries()==updates@
                && final(self).history()==old(self).history().append(final(self).core(),r::Event::Begin {structural:true}),
    {
        let result=self.inner.begin_structural(candidate,recovery,updates);
        if result.is_ok() {
            proof {reveal(r::step);}
            self.record(Ghost(r::Event::Begin {structural:true}));
        }
        result
    }
    pub fn poll_update<E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(&mut self,callback:C)->(out:Poll<Result<bool,StepError<E>>>)
        requires old(self).wf(),forall|k:&K,u:&mut U|callback.requires((k,u)),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).source()==old(self).source(),final(self).source_key()==old(self).source_key(),
            final(self).history()==old(self).history().append(final(self).core(),r::Event::Update {result:r::outcome(out)}),
            crate::configuration_transaction::update_result(old(self).core(),final(self).core(),callback,out),
    {
        let result=self.inner.poll_update(callback);
        proof {reveal(r::step);}
        self.record(Ghost(r::Event::Update {result:r::outcome(result)}));result
    }
    pub fn poll_rollback<E,C:FnOnce(&K,&mut U)->Poll<Result<(),E>>>(&mut self,callback:C)->(out:Poll<Result<bool,E>>)
        requires old(self).wf(),forall|k:&K,u:&mut U|callback.requires((k,u)),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).source()==old(self).source(),final(self).source_key()==old(self).source_key(),
            final(self).history()==old(self).history().append(final(self).core(),r::Event::Rollback {result:r::outcome(out)}),
            crate::configuration_batch::rollback_result(old(self).core().batch(),final(self).core().batch(),callback,out),
    {
        let result=self.inner.poll_rollback(callback);
        proof {reveal(r::step);}
        self.record(Ghost(r::Event::Rollback {result:r::outcome(result)}));result
    }
    pub fn poll_structure<E,C:FnOnce(Structure,&S,&mut Pending<S,R>)->Poll<Result<(),E>>>(&mut self,callback:C)->(out:Poll<Result<bool,StructureError<E>>>)
        requires old(self).wf(),forall|s:Structure,a:&S,p:&mut Pending<S,R>|callback.requires((s,a,p)),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).source()==old(self).source(),final(self).source_key()==old(self).source_key(),
            final(self).history()==old(self).history().append(final(self).core(),r::Event::Structure {result:r::outcome(out)}),
            crate::configuration_transaction::structure_result(old(self).core(),final(self).core(),callback,out),
    {
        let result=self.inner.poll_structure(callback);
        proof {reveal(r::step);}
        self.record(Ghost(r::Event::Structure {result:r::outcome(result)}));result
    }
    pub fn commit(&mut self)->(out:Result<(S,R,Batch<K,U>),TransactionError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).source()==old(self).source(),final(self).source_key()==old(self).source_key(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> final(self).history()==old(self).history().append(final(self).core(),r::Event::Commit)
                && out->Ok_0==(old(self).core().accepted(),old(self).core().staged().unwrap().recovery,old(self).core().batch()),
    {
        let result=self.inner.commit();
        if result.is_ok() {
            proof {reveal(r::step);old(self).core().state_facts();self.inner.state_facts();}
            self.record(Ghost(r::Event::Commit));
        }
        result
    }
    pub fn recover_with<C:FnOnce(&mut R)->S>(&mut self,callback:C)->(out:Result<(S,Pending<S,R>),TransactionError>)
        requires old(self).wf(),forall|r:&mut R|callback.requires((r,)),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).source()==old(self).source(),final(self).source_key()==old(self).source_key(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> final(self).history()==old(self).history().append(final(self).core(),r::Event::Recover)
                && crate::configuration_transaction::reconstructed(callback,old(self).core().staged().unwrap().recovery,out->Ok_0.1.recovery,final(self).core().accepted()),
    {
        let result=self.inner.recover_with(callback);
        if result.is_ok() {
            proof {reveal(r::step);old(self).core().state_facts();self.inner.state_facts();}
            self.record(Ghost(r::Event::Recover));
        }
        result
    }
    pub fn refresh(&mut self,current:S)->(out:Result<S,S>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),
            final(self).source()==old(self).source(),final(self).source_key()==old(self).source_key(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==current,
            out.is_ok() ==> final(self).core().accepted()==current && out->Ok_0==old(self).core().accepted()
                && final(self).history()==old(self).history().append(final(self).core(),r::Event::Refresh),
    {
        let result=self.inner.refresh(current);
        if result.is_ok() {
            proof {reveal(r::step);old(self).core().state_facts();self.inner.state_facts();}
            self.record(Ghost(r::Event::Refresh));
        }
        result
    }
    pub fn sources(&self)->(out:&Source<P,V>) ensures *out==self.source(), {&self.sources}
    fn record_sources(&mut self,Ghost(event):Ghost<sources::Event<P,V>>)
        requires old(self).configuration_wf(),old(self).sources.wf(),old(self).source_ledger.wf(),
            old(self).source_ledger.journal()==old(self).journal(),old(self).source_ledger.configuration()==old(self).key(),
            old(self).sources.history()==old(self).source_ledger.history().append(old(self).sources.observation(),event),
            source_history::reviewed(event,old(self).ledger.record()),
        ensures final(self).wf(),final(self).core()==old(self).core(),final(self).history()==old(self).history(),
            final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),final(self).source_key()==old(self).source_key(),
            final(self).source()==old(self).source(),
    {
        proof {
            let i=self.source_ledger.history().events.len() as int;
            assert(sources::step(self.sources.history().states[i],self.sources.history().states[i+1],self.sources.history().events[i]));
        }
        self.source_ledger.advance(&self.ledger,Ghost(self.sources.observation()),Ghost(event));
    }
    pub fn clear_sources(&mut self)->(out:Result<(),TransactionError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).core()==old(self).core(),final(self).history()==old(self).history(),
            final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),final(self).source_key()==old(self).source_key(),
            out.is_ok()==old(self).core().staged().is_none(),out.is_err() ==> *final(self)==*old(self) && out->Err_0==TransactionError::Pending,
            out.is_ok() ==> final(self).source().observation()==sources::Observation::<P,V>::empty()
                && final(self).source().history()==old(self).source().history().append(final(self).source().observation(),sources::Event::Clear),
    {
        if self.inner.pending().is_some() {return Err(TransactionError::Pending);}
        self.sources.clear();self.record_sources(Ghost(sources::Event::Clear));Ok(())
    }
    pub fn load_sources(&mut self,input:Load<P,V>)->(out:Result<(),Load<P,V>>)
        requires old(self).wf(),key_obeys_cmp_spec::<P>(),
        ensures final(self).wf(),final(self).core()==old(self).core(),final(self).history()==old(self).history(),
            final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),final(self).source_key()==old(self).source_key(),
            out.is_ok()==old(self).core().staged().is_none(),out.is_err() ==> *final(self)==*old(self) && out->Err_0==input,
            out.is_ok() ==> final(self).source().observation()==(sources::Observation {root:Some(input.root),contents:input.contents@,
                checkpoints:sources::loaded(old(self).source().observation().checkpoints,input.checkpoints@),resolutions:input.resolutions@})
                && final(self).source().history()==old(self).source().history().append(final(self).source().observation(),
                    sources::Event::Load {root:input.root,contents:input.contents@,checkpoints:input.checkpoints@,resolutions:input.resolutions@}),
    {
        if self.inner.pending().is_some() {return Err(input);}
        let ghost event=sources::Event::Load {root:input.root,contents:input.contents@,checkpoints:input.checkpoints@,resolutions:input.resolutions@};
        self.sources.load(input.root,input.contents,input.checkpoints,input.resolutions);self.record_sources(Ghost(event));Ok(())
    }
    pub fn accept_saved_sources<M>(&mut self,domain:u64,save:Save<Target<P,V,M>>)->(out:Result<(),Save<Target<P,V,M>>>)
        requires old(self).wf(),save.wf(),key_obeys_cmp_spec::<P>(),
        ensures final(self).wf(),final(self).core()==old(self).core(),final(self).history()==old(self).history(),
            final(self).journal()==old(self).journal(),final(self).key()==old(self).key(),final(self).source_key()==old(self).source_key(),
            out.is_ok()==(old(self).core().staged().is_none() && save.review().is_some() && domain==save.review().unwrap().domain() && old(self).core().version()==save.review().unwrap().revision()),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==save,
            out.is_ok() ==> final(self).source().observation()==(sources::Observation {checkpoints:sources::advanced(old(self).source().observation().checkpoints,sources::saved(save)),..old(self).source().observation()})
                && final(self).source().history()==old(self).source().history().append(final(self).source().observation(),sources::Event::Save {domain,revision:old(self).core().version(),entries:sources::saved(save)}),
    {
        let ghost event=sources::Event::Save {domain,revision:self.core().version(),entries:sources::saved(save)};
        let result=self.inner.accept_saved_sources(domain,save,&mut self.sources);
        if result.is_ok() {self.record_sources(Ghost(event));}
        result
    }
    pub(crate) fn source_snapshot_with(&self,native:&joint::Member)->(out:source_history::Snapshot<S,R,K,U,P,V>)
        requires self.wf(),native.wf(),native.journal()==self.journal(),
        ensures out.certified(),out.history()==self.source().history(),out.key()==self.source_key(),
            out.configuration().history()==self.history(),out.configuration().key()==self.key(),out.joint_spec().journal_spec()==self.journal(),
            out.joint_spec().certified(),out.joint_spec().last().contains_pair(native.key(),native.record()),
            native.events().len()<=out.joint_spec().events().len(),out.joint_spec().events().take(native.events().len() as int)==native.events(),
    {self.source_ledger.snapshot_with(&self.ledger,native)}
    pub fn source_snapshot(&self)->(out:source_history::Snapshot<S,R,K,U,P,V>)
        requires self.wf(),ensures out.certified(),out.history()==self.source().history(),out.key()==self.source_key(),
            out.configuration().history()==self.history(),out.configuration().key()==self.key(),out.joint_spec().journal_spec()==self.journal(),
    {self.source_ledger.snapshot(&self.ledger)}
    pub fn snapshot(&self)->(out:Snapshot<S,R,K,U>)
        requires self.wf(),ensures out.certified(),out.history()==self.history(),out.key()==self.key(),out.joint_spec().journal_spec()==self.journal(),
    {self.ledger.snapshot()}
}
}
