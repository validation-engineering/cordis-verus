//! Strict restoration domains and actual conflicting writes for typed owners.
use super::Attempt;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, managed::recovery::quiet};
use vstd::prelude::*;

verus! {
impl<T:?Sized> Attempt<T> {
    /// This is the real locked read's semantic domain. A newer monotone
    /// revision does not prevent success after a foreign inverse restores head.
    pub proof fn strict_domain(&self)
        requires self.wf(),
        ensures self.result().is_ok()==(self.read().value().is_some() && self.read().value().unwrap().state()==self.inverse().after().state()),
            self.result().is_ok()==(self.read().value().is_some() && self.read().value().unwrap().state().head==self.inverse().after().state().head),
            self.read().value().is_some() ==> self.read().value().unwrap().extends(self.inverse().after()),
    {
        self.facts();
        if self.read().value().is_some() {
            let observed=self.read().value().unwrap();let original=self.inverse().after();
            if observed.state().head==original.state().head {
                assert(observed.states[original.state().head as int]==original.states[original.state().head as int]);
                assert(observed.state()==original.state());
            }
        }
    }
    /// A live conflict is explained by a real later write to this allocation,
    /// not a guessed port-name conflict or a caller-provided failed inverse.
    pub proof fn conflicting_write(&self)->(index:nat)
        requires self.wf(),self.result().is_err(),self.read().value().is_some(),
        ensures self.inverse().after().commit.at()<index<self.read().checkpoint().events().len(),
            self.read().checkpoint().events()[index as int].event.key==self.inverse().owner().key(),
            joint::payload::mutation(self.read().checkpoint().events()[index as int].event.change),
    {
        hide(joint::valid);hide(joint::step);
        self.facts();self.strict_domain();
        let read=self.read().checkpoint();let frames=read.events();let current=self.read().value().unwrap();
        let origin=self.inverse().after().commit;let key=self.inverse().owner().key();let write=current.commit;
        read.included(&origin);read.included(&write);
        crate::reversible_value::managed::recovery::frame_update(frames,origin.at());
        crate::reversible_value::managed::recovery::frame_update(frames,write.at());
        assert(current.revision>self.inverse().after().revision) by {
            if current.revision==self.inverse().after().revision {assert(current.states =~= self.inverse().after().states);}
        }
        if write.at()<=origin.at() {joint::payload::retained(frames,write.at()+1,origin.at()+1,key);}
        assert(origin.at()<write.at());
        joint::payload::retained(frames,origin.at()+1,write.at(),key);joint::payload::edge(frames,write.at(),key);
        write.at()
    }
    pub proof fn retirement_write(&self)->(index:nat)
        requires self.wf(),self.read().value().is_none(),
        ensures self.inverse().after().commit.at()<index<self.read().checkpoint().events().len(),
            self.read().checkpoint().events()[index as int].event.key==self.inverse().owner().key(),
            self.read().checkpoint().events()[index as int].event.change==joint::Change::PayloadRetire,
    {
        hide(joint::valid);hide(joint::step);
        self.facts();let read=self.read().checkpoint();let frames=read.events();let key=self.inverse().owner().key();let origin=self.inverse().after().commit;
        read.included(&origin);crate::reversible_value::managed::recovery::frame_update(frames,origin.at());
        let index=joint::record_origin(frames,frames.len(),key);
        crate::reversible_value::managed::recovery::frame_update(frames,index);
        if index<=origin.at() {joint::payload::retained(frames,index+1,origin.at()+1,key);}
        assert(origin.at()<index);
        joint::payload::retained(frames,origin.at()+1,index,key);joint::payload::edge(frames,index,key);index
    }
    pub proof fn quiet_recovery(&self)
        requires self.wf(),quiet(self.read().checkpoint().events(),self.inverse().after().commit.at()+1,self.read().checkpoint().events().len(),self.inverse().owner().key()),
        ensures self.result().is_ok(),self.result()->Ok_0.after().state()==self.inverse().before().state(),
    {
        hide(joint::valid);hide(joint::step);
        self.facts();self.strict_domain();let read=self.read().checkpoint();let origin=self.inverse().after().commit;let key=self.inverse().owner().key();
        read.included(&origin);crate::reversible_value::managed::recovery::frame_update(read.events(),origin.at());
        crate::reversible_value::managed::recovery::quiet_record(read.events(),origin.at()+1,read.events().len(),key);
        assert(self.read().value().is_some());let current=self.read().value().unwrap();
        assert(current.revision==self.inverse().after().revision);
        assert(current.states =~= self.inverse().after().states);
    }
    /// A successful attempt at a newer revision is explained by an actual
    /// preceding Restore. It does not treat equal payload contents as recovery.
    pub proof fn resumed_origin(&self)->(index:nat)
        requires self.wf(),self.result().is_ok(),
            self.read().value().is_some(),self.read().value().unwrap().revision>self.inverse().after().revision,
        ensures self.inverse().after().commit.at()<index<self.read().checkpoint().events().len(),
            self.read().checkpoint().events()[index as int].event.key==self.inverse().owner().key(),
            self.read().checkpoint().events()[index as int].event.change==joint::Change::PayloadRestore,
    {
        hide(joint::valid);hide(joint::step);
        self.facts();self.strict_domain();self.inverse().source_history();
        let read=self.read().checkpoint();let frames=read.events();let observed=self.read().value().unwrap();
        let original=self.inverse().after();let positions=observed.positions;let revision=observed.revision as int;
        let key=self.inverse().owner().key();let source=self.inverse().owner().source();
        assert(observed.states[revision]==observed.state());
        assert(observed.states[revision].head==original.revision);
        crate::reversible_value::payload::semantic_history::restored(observed.states,positions,observed.commit.events(),revision);
        read.included(&original.commit);read.included(&observed.commit);
        joint::payload::extend_indexed(observed.history.len(),positions,observed.commit.events(),frames,key,source);
        joint::payload::unique_revision(frames,original.commit.at(),positions[original.revision as int],key);
        assert(positions[original.revision as int]<positions[revision]);
        assert(frames[positions[revision] as int]==observed.commit.events()[positions[revision] as int]);
        positions[revision]
    }
    #[verifier::opaque]
    pub open spec fn recovered(&self)->bool {
        let frames=self.read().checkpoint().events();let origin=self.inverse().after().commit.at();let key=self.inverse().owner().key();
        &&& self.result().is_ok()==(self.read().value().is_some() && self.read().value().unwrap().state()==self.inverse().after().state())
        &&& self.result().is_ok()==(self.read().value().is_some() && self.read().value().unwrap().state().head==self.inverse().after().state().head)
        &&& quiet(frames,origin+1,frames.len(),key) ==> self.result().is_ok()
        &&& self.result().is_ok() && self.read().value().unwrap().revision>self.inverse().after().revision ==>
            exists|i:nat|origin<i<frames.len() && frames[i as int].event.key==key && frames[i as int].event.change==joint::Change::PayloadRestore
        &&& self.result().is_err() ==> exists|i:nat|origin<i<frames.len() && frames[i as int].event.key==key
            && if self.read().value().is_some() {joint::payload::mutation(frames[i as int].event.change)} else {frames[i as int].event.change==joint::Change::PayloadRetire}
    }
    /// The actual restore and cleanup dispatcher call this establishment path.
    pub proof fn establish_recovery(&self)
        requires self.wf(),ensures self.recovered(),
    {
        self.strict_domain();
        let frames=self.read().checkpoint().events();let origin=self.inverse().after().commit.at();let key=self.inverse().owner().key();
        if quiet(frames,origin+1,frames.len(),key) {self.quiet_recovery();}
        if self.result().is_err() {
            let index=if self.read().value().is_some() {self.conflicting_write()} else {self.retirement_write()};
            assert(origin<index<frames.len());
        } else if self.read().value().unwrap().revision>self.inverse().after().revision {
            let index=self.resumed_origin();
            assert(origin<index<frames.len());
        }
        reveal(Attempt::recovered);
    }
}
}
