//! Opt-in, bounded commands recorded by the actual native transition boundary.
//! A source is certified against one complete shared Journal cut; callers do
//! not reconstruct labels, insertion arguments, IDs or command correspondence.
#[path = "native_source_chain.rs"]
pub mod chain;
#[path = "native_source_cleanup.rs"]
pub mod cleanup;
use super::{
    history::{
        self,
        deletion::{replay, trace::Window},
    },
    NativeRuntime,
};
#[cfg(verus_keep_ghost)]
use crate::kernel_replay;
use crate::kernel_replay::Command;
#[cfg(verus_keep_ghost)]
use crate::refinement as r;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Status {Disabled,Recording,Exhausted}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Error {Disabled,Exhausted}
pub(crate) struct Recorder {pub(crate) commands:Vec<Command>,pub(crate) limit:usize,pub(crate) status:Status}
impl Recorder {
    pub(crate) open spec fn matches<V>(&self,h:history::History<V>)->bool {
        self.status==Status::Recording ==> replay::corresponds(h,self.commands@)
    }
    pub(crate) fn disabled()->(out:Self) ensures out.status==Status::Disabled,
    {Self {commands:Vec::new(),limit:0,status:Status::Disabled}}
    fn new(limit:usize)->(out:Self) ensures out.status==Status::Recording,out.commands@==Seq::<Command>::empty(),
    {Self {commands:Vec::new(),limit,status:Status::Recording}}
    pub(crate) fn active(&self)->(out:bool) ensures out==(self.status==Status::Recording),
    {self.status==Status::Recording}
    pub(crate) fn append<V>(&mut self,c:Command,Ghost(h):Ghost<history::History<V>>,Ghost(state):Ghost<history::Observation<V>>)
        requires old(self).matches(h),h.valid(),c.shape(),c.payload(state.control),
        ensures final(self).matches(h.append(state,c.actor(),c.rule())),final(self).limit==old(self).limit,
            final(self).status==if old(self).status!=Status::Recording {old(self).status}
                else if old(self).commands.len()>=old(self).limit || old(self).commands.len()>=u64::MAX-1 {Status::Exhausted} else {Status::Recording},
            final(self).commands@==if old(self).status==Status::Recording && old(self).commands.len()<old(self).limit && old(self).commands.len()<u64::MAX-1
                {old(self).commands@.push(c)} else {old(self).commands@},
    {
        if self.active() {
            if self.commands.len()>=self.limit || self.commands.len() as u64>=u64::MAX-1 {
                self.status=Status::Exhausted;
            } else {
                let ghost before=self.commands@;self.commands.push(c);
                proof {
                    let next=h.append(state,c.actor(),c.rule());
                    assert(self.commands.len()==next.labels.len());
                    assert forall|i:int|0<=i<self.commands.len() implies (#[trigger] self.commands@[i]).shape() && self.commands@[i].payload(next.states[i+1].control)
                        && (self.commands@[i].actor(),self.commands@[i].rule())==next.labels[i] by {
                        if i<before.len() {assert(self.commands@[i]==before[i]);} else {assert(i==before.len());}
                    }
                }
            }
        }
    }
    fn copy(&self)->(out:Result<Vec<Command>,Error>)
        ensures out.is_ok()==(self.status==Status::Recording),out.is_ok() ==> kernel_replay::same_commands(out->Ok_0@,self.commands@),
    {
        match self.status {Status::Disabled=>return Err(Error::Disabled),Status::Exhausted=>return Err(Error::Exhausted),Status::Recording=>{}}
        let mut out=Vec::new();let mut i=0;
        while i<self.commands.len()
            invariant i<=self.commands.len(),kernel_replay::same_commands(out@,self.commands@.take(i as int)),
            decreases self.commands.len()-i,
        {out.push(self.commands[i].duplicate());i+=1;}
        Ok(out)
    }
}
/// Commands are private and cannot be replaced after their source is certified.
/// The typed checkpoint includes publications, owners and every Journal record.
#[allow(dead_code)] // Snapshot and source ledger are erased proof evidence.
pub struct Source<V> {commands:Vec<Command>,bound:usize,cut:Ghost<history::Snapshot<V>>,ledger:Ghost<super::child_history::Ledger>}
impl<V> Source<V> {
    pub closed spec fn commands_spec(&self)->Seq<Command> {self.commands@}
    pub closed spec fn bound_spec(&self)->usize {self.bound}
    pub closed spec fn cut(&self)->history::Snapshot<V> {self.cut@}
    pub closed spec fn ledger(&self)->super::child_history::Ledger {self.ledger@}
    pub closed spec fn certified(&self)->bool {
        self.cut().certified() && self.ledger().cut_source(&self.cut())
            && cleanup::complete(self.ledger(),self.cut().history(),self.cut().positions()) && replay::corresponds(self.cut().history(),self.commands_spec())
            && self.cut().history().allocated_below(self.bound_spec() as nat)
    }
    pub fn commands(&self)->(out:&[Command]) ensures out@==self.commands_spec(), {self.commands.as_slice()}
    pub fn allocation_bound(&self)->(out:usize) ensures out==self.bound_spec(), {self.bound}
    pub proof fn source_for(&self,keep:Seq<bool>,w:Window)
        requires self.certified(),replay::mask(self.cut().history(),keep,w),
        ensures replay::source(self.cut().history(),self.commands_spec(),keep,self.bound_spec(),w),
    {
        self.cut().valid_history();reveal(history::History::allocated_below);
        assert forall|i:int|0<=i<self.commands_spec().len() && self.commands_spec()[i] is Insert implies self.commands_spec()[i].actor()<self.bound_spec() by {
            let c=self.commands_spec()[i];assert(c.shape());
            self.cut().history().transition_at(i);
            assert(r::registered(self.cut().history().states[i+1].control,c.actor()));
        }
    }
    /// Reuses this exact cut, including when it came from managed recovery.
    pub fn replay(&self,cut:&history::Snapshot<V>,keep:&[bool],Ghost(window):Ghost<Window>)->(out:Result<replay::Replay,replay::Error>)
        requires self.certified(),*cut==self.cut(),window.admissible(cut.history()),replay::mask(cut.history(),keep@,window),
        ensures out.is_ok(),out.unwrap().plan.matches(self.commands_spec(),keep@),
            out.unwrap().execution.states()==replay::states(cut.history(),window,out.unwrap().plan.names.renaming()),
            out.unwrap().execution.control().paper()==crate::alpha::rename(out.unwrap().plan.names.renaming(),cut.history().states.last().control),
            out.unwrap().execution.control().next_id()==kernel_replay::allocations(out.unwrap().plan.commands@),
            kernel_replay::represented_generations(out.unwrap().execution.control(),kernel_replay::generations(out.unwrap().plan.commands@)),
    {
        proof {self.source_for(keep@,window);}
        cut.replay_control_window(self.commands.as_slice(),keep,self.bound,Ghost(window))
    }
}
pub struct Capture<V> {pub cut:history::Snapshot<V>,pub source:Source<V>}
impl<R,H,V> NativeRuntime<R,H,V> {
    pub closed spec fn recording_status(&self)->Status {self.control_source.status}
    pub fn control_recording_status(&self)->(out:Status) ensures out==self.recording_status(), {self.control_source.status}
    /// Retains at most `limit` commands; the first excess step marks the record
    /// exhausted. It never changes whether a lifecycle operation is accepted.
    pub fn new_recorded(domain:u64,limit:usize)->(out:Self)
        ensures out.wf(),out.recording_status()==Status::Recording,out.execution_history().labels.len()==0,
            out.state().protocol().domain_id()==domain,out.registry().entries()==Map::empty(),out.publications().entries()==Map::empty(),
    {
        let mut out=Self::new(domain);out.control_source=Recorder::new(limit);proof {reveal(NativeRuntime::control_source_valid);}out
    }
    pub(crate) proof fn control_source_payload(&self,c:&Command,id:usize)
        requires self.registry().wf(),self.registry().entries().contains_key(id),c is Insert,c.actor()==id,
            c->Insert_parent==self.registry().entries()[id].recipe().parent_id(),
            kernel_replay::ports(c->Insert_dependencies@)==kernel_replay::ports(self.registry().entries()[id].recipe().dependencies_spec()),
            kernel_replay::ports(c->Insert_provisions@)==kernel_replay::ports(self.registry().entries()[id].recipe().provisions_spec().push(self.registry().entries()[id].recipe().anchor_port())),
        ensures c.payload(self.observation().control),
    {
        assert(self.registry().recipe_matches(id));
        assert(self.observation().control.fibers[id].dependencies =~= kernel_replay::ports(c->Insert_dependencies@));
        assert(self.observation().control.fibers[id].provisions =~= kernel_replay::ports(c->Insert_provisions@));
    }
    /// Bind to an already captured cut. This adds no second Journal read and
    /// cannot accidentally use a newer snapshot than the recovery certificate.
    pub fn bind_control_source(&self,_cut:&history::Snapshot<V>)->(out:Result<Source<V>,Error>)
        requires self.wf(),_cut.certified(),_cut.history()==self.execution_history(),_cut.positions()==self.history_positions(),_cut.key()==self.joint_key(),
            _cut.joint_spec().journal_spec()==self.journal_spec(),self.child_records().cut_source(_cut),
        ensures out.is_ok()==(self.recording_status()==Status::Recording),out.is_ok() ==> out->Ok_0.certified() && out->Ok_0.cut()==*_cut,
    {
        let commands=self.control_source.copy()?;
        let bound=self.host.kernel().identity_slots();
        proof {reveal(NativeRuntime::control_source_valid);reveal(NativeRuntime::unload_sources);replay::copy_correspondence(_cut.history(),self.control_source.commands@,commands@);}
        Ok(Source {commands,bound,cut:Ghost(*_cut),ledger:Ghost(self.child_records())})
    }
    pub fn control_source_snapshot(&self)->(out:Result<Capture<V>,Error>)
        requires self.wf(),
        ensures out.is_ok()==(self.recording_status()==Status::Recording),out.is_ok() ==> out->Ok_0.source.certified()
            && out->Ok_0.source.cut()==out->Ok_0.cut && out->Ok_0.cut.history()==self.execution_history()
            && out->Ok_0.cut.key()==self.joint_key() && self.child_records().cut_source(&out->Ok_0.cut),
    {
        let cut=self.publication_snapshot();
        let source=self.bind_control_source(&cut)?;
        Ok(Capture {cut,source})
    }
}
}
