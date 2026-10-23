//! Value/Child recovery and native episode deletion share one actual cut.
//! Keeping both results visible prevents a value-only success from being
//! mistaken for legal deletion (for example while a Child is still registered).
use super::unload_capture::RecoveryCapture;
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::native::runtime::history::deletion::joint::Selection;
use crate::lifecycle_state::native::runtime::history::{
    deletion::{
        trace::{Issue, Window},
        Region,
    },
    History,
};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint;
use crate::reversible_value::managed::Slot;
use vstd::prelude::*;

verus! {
pub struct WithDeletion<A,R,T:?Sized,M,X> {
    pub recovery:RecoveryCapture<A,R,T,M,X>,
    pub window:Ghost<Window>,
    pub deletion:Ghost<Result<History<Slot<T,M>>,Issue>>,
}
pub struct WithEffects<A,R,T:?Sized,M,X> {
    pub native:WithDeletion<A,R,T,M,X>,
    pub effects:Ghost<Seq<bool>>,
    pub result:Ghost<Result<Seq<crate::reversible_value::joint::Frame>,crate::lifecycle_state::native::runtime::history::deletion::joint::Issue>>,
}
/// Actual Kernel execution and full Journal deletion evidence share the same
/// original source. The Journal result remains a proved effect trajectory; this
/// type does not claim to have executed those effects on new host resources.
pub struct WithControlReplay<A,R,T:?Sized,M,X> {
    pub effects:WithEffects<A,R,T,M,X>,
    pub replay:crate::lifecycle_state::native::runtime::history::deletion::replay::Replay,
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum ReplayError {
    Source(crate::lifecycle_state::native::runtime::control_source::Error),
    Control(crate::lifecycle_state::native::runtime::history::deletion::replay::Error),
}
impl<A,R,T:?Sized,M,X> WithEffects<A,R,T,M,X> {
    pub open spec fn selection(&self)->Selection<Slot<T,M>> {
        Selection {source:self.native.recovery.cut,window:self.native.window@,effects:self.effects@}
    }
    pub open spec fn certified(&self)->bool {
        self.native.recovery.cut.certified() && self.result@.is_ok()==self.selection().admissible()
            && (self.result@.is_ok() ==> self.result@->Ok_0==self.selection().plan().prefix(self.selection().frames(),self.selection().frames().len())
                && joint::valid(self.result@->Ok_0))
            && (self.result@.is_err() ==> self.selection().diagnosed(self.result@->Err_0))
    }
    /// Reuse the automatically bound commands from the actual release capture.
    /// No independently supplied source transcript, allocation bound or snapshot.
    pub fn replay_control(self,keep:&[bool])->(out:Result<WithControlReplay<A,R,T,M,X>,ReplayError>)
        requires self.certified(),self.native.recovery.source_bound(),self.native.recovery.cut.certified(),
            self.native.window@.admissible(self.native.recovery.cut.history()),
            crate::lifecycle_state::native::runtime::history::deletion::replay::mask(self.native.recovery.cut.history(),keep@,self.native.window@),
        ensures out.is_ok()==self.native.recovery.control.is_ok(),out.is_ok() ==> out->Ok_0.effects==self
            && out->Ok_0.replay.plan.matches(self.native.recovery.control->Ok_0.commands_spec(),keep@)
            && out->Ok_0.replay.execution.states()==crate::lifecycle_state::native::runtime::history::deletion::replay::states(
                self.native.recovery.cut.history(),self.native.window@,out->Ok_0.replay.plan.names.renaming())
            && out->Ok_0.replay.execution.control().paper()==crate::alpha::rename(out->Ok_0.replay.plan.names.renaming(),self.native.recovery.cut.history().states.last().control)
            && (self.result@.is_ok() ==> joint::state_at(self.result@->Ok_0,self.result@->Ok_0.len()).contains_key(self.native.recovery.cut.key())
                && joint::state_at(self.result@->Ok_0,self.result@->Ok_0.len())[self.native.recovery.cut.key()] is Native
                && out->Ok_0.replay.execution.control().paper()==crate::alpha::rename(out->Ok_0.replay.plan.names.renaming(),
                    joint::state_at(self.result@->Ok_0,self.result@->Ok_0.len())[self.native.recovery.cut.key()]->Native_state.control)),
    {
        let source=match &self.native.recovery.control {Ok(source)=>source,Err(e)=>return Err(ReplayError::Source(*e))};
        let replay=match source.replay(&self.native.recovery.cut,keep,self.native.window) {
            Ok(replay)=>replay,Err(e)=>return Err(ReplayError::Control(e)),
        };
        proof {if self.result@.is_ok() {
            self.selection().construct();self.selection().endpoint();
        }}
        Ok(WithControlReplay {effects:self,replay})
    }
}
impl<A,R,T:?Sized,M,X> WithDeletion<A,R,T,M,X> {
    /// Keep the value, Child and native certificates at exactly the same real
    /// cut. Success additionally constructs all retained Journal effects.
    pub fn with_effects(self,Ghost(effects):Ghost<Seq<bool>>)->(out:WithEffects<A,R,T,M,X>)
        requires self.recovery.cut.certified(),
        ensures out.certified(),out.native==self,out.effects@==effects,
            out.result@.is_ok()==(crate::lifecycle_state::native::runtime::history::deletion::joint::Selection {
                source:self.recovery.cut,window:self.window@,effects}).admissible(),
            out.result@.is_ok() ==> crate::reversible_value::joint::valid(out.result@->Ok_0)
                && crate::reversible_value::joint::erasure::scalar_sources(out.result@->Ok_0)
                && crate::reversible_value::joint::classification::history(out.result@->Ok_0)
                && crate::reversible_value::joint::references::history(out.result@->Ok_0,self.recovery.cut.joint_spec().domain()),
            out.result@.is_err() ==> (crate::lifecycle_state::native::runtime::history::deletion::joint::Selection {
                source:self.recovery.cut,window:self.window@,effects}).diagnosed(out.result@->Err_0),
    {
        let ghost result=self.recovery.cut.delete_effect_window(self.window@,effects);
        WithEffects {native:self,effects:Ghost(effects),result:Ghost(result)}
    }
}
impl<A,R,T:?Sized,M,X> RecoveryCapture<A,R,T,M,X> {
    /// Reuse the producer/Child recovery snapshot already captured by the real
    /// release path. The start is its authentic invocation's pre-Begin state.
    /// This adds no Journal read, history buffer or callback execution.
    pub fn with_deletion(self,Ghost(region):Ghost<Region>)->(out:WithDeletion<A,R,T,M,X>)
        requires self.cut.certified(),self.observations@.wf(),self.observations@.source==self.cut,
        ensures out.recovery==self,out.window@.region==region,
            out.window@.start==self.observations@.first,out.window@.end==self.cut.history().labels.len(),
            out.deletion@.is_ok()==out.window@.admissible(self.cut.history()),
            out.deletion@.is_ok() ==> out.deletion@->Ok_0.valid() && out.deletion@->Ok_0.fresh_insertions()
                && out.deletion@->Ok_0==out.window@.target(self.cut.history())
                && out.deletion@->Ok_0.states.last()==self.cut.history().states.last(),
            out.deletion@.is_err() ==> out.window@.diagnosed(self.cut.history(),out.deletion@->Err_0),
    {
        let ghost window=Window {start:self.observations@.first,end:self.cut.history().labels.len() as int,region};
        let ghost deletion=self.cut.delete_window(window);
        WithDeletion {recovery:self,window:Ghost(window),deletion:Ghost(deletion)}
    }
}
}
