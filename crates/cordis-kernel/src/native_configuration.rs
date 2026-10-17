//! One checkpoint for the actual native lifecycle, configuration and sources.
//! Only the shared Journal handle remains at runtime; typed histories erase.
use super::{history, NativeRuntime};
use crate::configuration_recorded::Recorded;
#[cfg(verus_keep_ghost)]
use crate::configuration_save::sources;
use crate::configuration_source_history as source_history;
use crate::reversible_value::joint;
use vstd::prelude::*;
verus! {
#[allow(dead_code)]
pub struct Snapshot<S,C,K,U,P,T,V> {
    native:history::Snapshot<V>,sources:Ghost<source_history::Snapshot<S,C,K,U,P,T>>,
}
impl<S,C,K,U,P,T,V> Snapshot<S,C,K,U,P,T,V> {
    pub closed spec fn native(&self)->history::Snapshot<V> {self.native}
    pub closed spec fn sources(&self)->source_history::Snapshot<S,C,K,U,P,T> {self.sources@}
    pub open spec fn joint_spec(&self)->joint::Snapshot {self.native().joint_spec()}
    pub closed spec fn certified(&self)->bool {
        self.native().certified() && self.sources().certified() && self.sources().joint_spec()==self.joint_spec()
    }
    pub proof fn valid_history(&self)
        requires self.certified(),
        ensures self.native().certified(),self.sources().certified(),self.joint_spec().certified(),
            self.sources().joint_spec()==self.joint_spec(),
    {self.native.valid_history();}
    fn new(sources:source_history::Snapshot<S,C,K,U,P,T>,Ghost(history):Ghost<history::History<V>>,Ghost(positions):Ghost<Seq<nat>>,Ghost(key):Ghost<nat>)->(out:Self)
        requires sources.certified(),sources.joint_spec().certified(),history.valid(),history.indexed(positions,sources.joint_spec().events(),key),
            sources.joint_spec().last().contains_pair(key,joint::Record::Native {state:history.states.last().project(history.labels.len())}),
        ensures out.certified(),out.sources()==sources,out.native().history()==history,out.native().positions()==positions,out.native().key()==key,
            out.joint_spec()==sources.joint_spec(),
    {
        let ghost original=sources;
        let native=history::Snapshot::new(sources.into_joint(),Ghost(history),Ghost(positions),Ghost(key));
        Self {native,sources:Ghost(original)}
    }
    /// Completeness of both typed projections uses the same captured frames,
    /// even if other owners appended events between their last modifications.
    pub proof fn complete_projection(&self)
        requires self.certified(),
        ensures forall|n:int|0<=n<self.joint_spec().events().len() && #[trigger] self.joint_spec().events()[n].event.key==self.native().key() ==>
                exists|i:int|0<=i<self.native().positions().len() && i<self.native().history().states.len() && self.native().positions()[i]==n,
            forall|n:int|0<=n<self.joint_spec().events().len() && #[trigger] self.joint_spec().events()[n].event.key==self.sources().key() ==>
                exists|i:int|0<=i<self.sources().positions().len() && i<self.sources().history().states.len() && self.sources().positions()[i]==n,
            forall|n:int|0<=n<self.joint_spec().events().len() && #[trigger] self.joint_spec().events()[n].event.key==self.sources().configuration().key() ==>
                exists|i:int|0<=i<self.sources().configuration().positions().len() && i<self.sources().configuration().history().states.len() && self.sources().configuration().positions()[i]==n,
    {
        self.native.valid_history();self.native.complete_projection();self.sources@.valid_history();self.sources@.complete_projection();
        self.sources@.configuration().valid_history();
        self.sources@.configuration().complete_projection();
    }
    pub fn joint(&self)->(out:&joint::Snapshot) ensures *out==self.joint_spec(), {self.native.joint()}
    pub fn into_joint(self)->(out:joint::Snapshot) ensures out==self.joint_spec(), {self.native.into_joint()}
}
impl<R,H,V> NativeRuntime<R,H,V> {
    /// Construct from this runtime's actual Journal, with no caller-supplied
    /// identity or unrelated state history.
    pub fn configuration<S,C,K,U,P:Ord,T>(&self,current:S)->(out:Recorded<S,C,K,U,P,T>)
        ensures out.wf(),out.journal()==self.journal_spec(),out.core().accepted()==current,out.core().version()==0,out.core().staged().is_none(),
            out.history().events.len()==0,out.source().history().events.len()==0,out.source().observation()==sources::Observation::<P,T>::empty(),
    {Recorded::new_in(&self.execution_journal(),current)}
    /// The ordinary host must retain the constructor's association. In Loader
    /// both fields are private and the runtime control view cannot replace it.
    pub fn configuration_snapshot<S,C,K,U,P:Ord,T>(&self,configuration:&Recorded<S,C,K,U,P,T>)->(out:Snapshot<S,C,K,U,P,T,V>)
        requires self.wf(),configuration.wf(),configuration.journal()==self.journal_spec(),
        ensures out.certified(),out.joint_spec().certified(),out.joint_spec().journal_spec()==self.journal_spec(),
            out.native().history()==self.execution_history(),out.native().positions()==self.history_positions(),out.native().key()==self.joint_key(),
            out.sources().history()==configuration.source().history(),out.sources().key()==configuration.source_key(),
            out.sources().configuration().history()==configuration.history(),out.sources().configuration().key()==configuration.key(),
            out.joint_spec().last().contains_pair(self.joint_key(),joint::Record::Native {state:self.observation().project(self.execution_history().labels.len())}),
    {
        let sources=configuration.source_snapshot_with(&self.joint);
        proof {self.execution_history().extend_indexed(self.history_positions(),self.joint.events(),sources.joint_spec().events(),self.joint_key());}
        Snapshot::new(sources,Ghost(self.execution_history()),Ghost(self.history_positions()),Ghost(self.joint_key()))
    }
}
}
