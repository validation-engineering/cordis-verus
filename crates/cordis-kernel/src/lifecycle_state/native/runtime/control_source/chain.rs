//! Source commands, typed publication payloads, inverse registration and host
//! cleanup use one actual Journal. These are source facts, not reconstructed
//! target work tickets or a claim to execute arbitrary retained callbacks.
#[cfg(verus_keep_ghost)]
use super::history;
use super::Source;
#[cfg(verus_keep_ghost)]
use crate::{refinement::Rule, reversible_value::joint};
use vstd::prelude::*;
verus! {
impl<V> Source<V> {
    /// Both directions are indexed: every command has its real native commit,
    /// and every native mutation in this full Journal has exactly one command.
    pub proof fn command_at(&self,i:int)->(at:nat)
        requires self.certified(),0<=i<self.commands_spec().len(),
        ensures at==self.cut().positions()[i+1],at<self.cut().joint_spec().events().len(),
            self.cut().joint_spec().events()[at as int].event.key==self.cut().key(),
            self.cut().joint_spec().events()[at as int].event.change==
                (joint::Change::Native {actor:self.commands_spec()[i].actor(),rule:self.commands_spec()[i].rule()}),
            joint::native::at(self.cut().joint_spec().events(),at,self.cut().key())==self.cut().history().states[i].project(i as nat),
            self.cut().joint_spec().events()[at as int].event.after==
                (joint::Record::Native {state:self.cut().history().states[i+1].project((i+1) as nat)}),
            super::super::production::classified(self.cut().joint_spec().events(),at as int,self.cut().key()),
    {
        reveal(Source::certified);self.cut().valid_history();
        let at=self.cut().positions()[i+1];
        self.cut().joint_spec().valid_history();
        self.cut().history().interval(self.cut().positions(),self.cut().joint_spec().events(),self.cut().key(),i);
        self.cut().production_step(at as int);at
    }
    pub proof fn command_for(&self,at:nat)->(i:int)
        requires self.certified(),at<self.cut().joint_spec().events().len(),
            self.cut().joint_spec().events()[at as int].event.key==self.cut().key(),
            self.cut().joint_spec().events()[at as int].event.change is Native,
        ensures 0<=i<self.commands_spec().len(),self.cut().positions()[i+1]==at,
            self.cut().joint_spec().events()[at as int].event.change==
                (joint::Change::Native {actor:self.commands_spec()[i].actor(),rule:self.commands_spec()[i].rule()}),
            forall|k:int|0<=k<self.commands_spec().len() && #[trigger] self.cut().positions()[k+1]==at ==> k==i,
    {
        reveal(Source::certified);self.cut().valid_history();
        self.cut().complete_projection();
        let index=choose|index:int|0<=index<self.cut().history().states.len() && self.cut().positions()[index]==at;
        assert(index>0);
        assert forall|k:int|0<=k<self.commands_spec().len() && #[trigger] self.cut().positions()[k+1]==at implies k==index-1 by {
            if k+1<index {assert(self.cut().positions()[k+1]<self.cut().positions()[index]);}
            if index<k+1 {assert(self.cut().positions()[index]<self.cut().positions()[k+1]);}
        }
        index-1
    }
    /// Finish's exact typed values and capture (including the action origin,
    /// work domain and committed providers) belong to this indexed commit.
    pub proof fn publication_at(&self,i:int)
        requires self.certified(),0<=i<self.commands_spec().len(),self.commands_spec()[i].rule()==Rule::Finish,
        ensures {
            let id=self.commands_spec()[i].actor();let h=self.cut().history();let at=self.cut().positions()[i+1];
            &&& !h.states[i].publications.contains_key(id) && h.states[i+1].publications.contains_key(id)
            &&& h.states[i+1].publications==h.states[i].publications.insert(id,h.states[i+1].publications[id])
            &&& self.cut().joint_spec().events()[at as int].event.after->Native_state.publications.contains_pair(id,history::publication(h.states[i+1].publications[id]))
        },
    {
        reveal(Source::certified);self.cut().valid_history();self.command_at(i);self.cut().history().transition_at(i);
    }
    /// An actual inverse-registration event has one actual managed forward in
    /// this same complete Journal; no other registration consumes it again.
    pub proof fn inverse_source(&self,at:nat)->(write:nat)
        requires self.certified(),at<self.cut().joint_spec().events().len(),self.cut().joint_spec().events()[at as int].event.settled.is_some(),
        ensures write==self.cut().joint_spec().events()[at as int].event.settled.unwrap(),write<at,
            self.cut().joint_spec().events()[write as int].event.pending,
            joint::forward(self.cut().joint_spec().events()[write as int].event),
            self.cut().joint_spec().events()[at as int].event.change==(joint::Change::RegisterInverse {write}),
            forall|other:nat|joint::pending_recovery::settles(self.cut().joint_spec().events(),write,other) ==> other==at,
    {
        reveal(Source::certified);self.cut().valid_history();self.cut().joint_spec().valid_history();
        let frames=self.cut().joint_spec().events();let write=frames[at as int].event.settled.unwrap();
        joint::pending_recovery::settlement_source(frames,write,at);
        assert forall|other:nat|joint::pending_recovery::settles(frames,write,other) implies other==at by {
            joint::pending_recovery::unique_settlement(frames,write,at,other);
        }write
    }
}
}
