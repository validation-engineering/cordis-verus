//! An owned verified driver for concrete resource episodes. The kernel and all
//! journals are private, so callers cannot bypass the provider cleanup guard.
//! This path uses witnessed cell effects; arbitrary closure execution belongs
//! to the separate ordinary-Rust host.
#[cfg(verus_keep_ghost)]
use crate::refinement as paper;
use crate::witnessed::{EpisodeError, ResourceEpisode};
use crate::{Error, Kernel, Phase, Port};
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum DriverError { Kernel(Error), Effect(EpisodeError), Pending }

pub struct Driver { kernel: Kernel, episodes: Vec<ResourceEpisode> }
impl Default for Driver {
    fn default() -> Self { Self::new() }
}
impl Driver {
    pub closed spec fn control(&self) -> paper::State { self.kernel.paper() }
    pub closed spec fn resource(&self, id: usize) -> Seq<crate::resources::Cell> { self.episodes[id as int].view() }
    pub closed spec fn initial(&self, id: usize) -> Seq<crate::resources::Cell> { self.episodes[id as int].initial() }
    pub closed spec fn pending(&self, id: usize) -> bool { self.episodes[id as int].pending() }
    pub open spec fn good(s: paper::State, e: &ResourceEpisode, id: usize) -> bool {
        &&& e.wf()
        &&& (!paper::registered(s, id) || s.fibers[id].phase == Phase::Inactive ==> e.depth() == 0 && !e.pending())
        &&& (paper::registered(s, id) && s.fibers[id].phase == Phase::Active ==> e.settled())
        &&& (paper::registered(s, id) && s.fibers[id].phase != Phase::Inactive
            ==> s.fibers[id].committed == ISet::new(|b: crate::Binding| e.committed().contains(b)))
    }
    pub closed spec fn wf(&self) -> bool {
        self.kernel.wf() && self.episodes.len() == self.kernel.next_id()
            && forall|i: int| 0 <= i < self.episodes.len() ==> Self::good(self.control(), &self.episodes[i], i as usize)
    }
    proof fn framed(&self, prior: &Self, actor: usize)
        requires prior.wf(), self.kernel.wf(), self.episodes.len() == self.kernel.next_id(),
            paper::frame(prior.control(), self.control(), actor),
            forall|i: int| 0 <= i < self.episodes.len() && i != actor ==> i < prior.episodes.len() && self.episodes[i] == prior.episodes[i],
            actor < self.episodes.len() ==> Self::good(self.control(), &self.episodes[actor as int], actor),
        ensures self.wf(),
    {
        assert forall|i: int| 0 <= i < self.episodes.len() implies Self::good(self.control(), &self.episodes[i], i as usize) by {
            if i != actor {
                assert(i as usize != actor);
                assert(paper::registered(prior.control(), i as usize) == paper::registered(self.control(), i as usize));
                if paper::registered(prior.control(), i as usize) { assert(prior.control().fibers[i as usize] == self.control().fibers[i as usize]); }
            }
        }
    }

    pub fn new() -> (out: Self)
        ensures out.wf(), out.control().fibers.dom().is_empty(),
    { Self { kernel: Kernel::new(), episodes: Vec::new() } }

    /// Insert an empty resource environment. Use `insert_with_resources` to
    /// configure the private resource cells before any activation begins.
    pub fn insert(&mut self, parent: Option<usize>, dependencies: Vec<Port>, provisions: Vec<Port>) -> (r: Result<usize, DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), r.unwrap(), paper::Rule::Insert),
    { self.insert_with_resources(parent, dependencies, provisions, Vec::new()) }

    pub fn insert_with_resources(&mut self, parent: Option<usize>, dependencies: Vec<Port>, provisions: Vec<Port>, values: Vec<u64>) -> (r: Result<usize, DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), r.unwrap(), paper::Rule::Insert),
    {
        let ghost prior = *self;
        match self.kernel.insert(parent, dependencies, provisions) {
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(DriverError::Kernel(e)) },
            Ok(id) => {
                self.episodes.push(ResourceEpisode::new(values, Vec::new()));
                proof { self.framed(&prior, id); }
                Ok(id)
            },
        }
    }

    /// L-Begin changes only control and iterator metadata; resource values are
    /// preserved from the previous complete recovery (or initial insertion).
    pub fn begin(&mut self, id: usize) -> (r: Result<(), DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id, paper::Rule::Begin)
                && final(self).resource(id) == final(self).initial(id)
                && final(self).resource(id) == old(self).resource(id),
    {
        let ghost prior = *self;
        match self.kernel.begin(id) {
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(DriverError::Kernel(e)) },
            Ok(()) => {
                proof { self.kernel.paper_observations(id); }
                let bindings = self.kernel.committed(id);
                let _restarted = self.episodes[id].restart(bindings);
                assert(_restarted);
                proof { self.episodes[id as int].complete_recovery(); self.framed(&prior, id); }
                Ok(())
            },
        }
    }

    /// New admission observes the live kernel target; outstanding stages remain
    /// admitted across target drift, exactly as the witnessed protocol requires.
    pub fn admit(&mut self, id: usize) -> (r: Result<bool, DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).control() == old(self).control(),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if self.kernel.phase(id) != Some(Phase::Loading) { return Err(DriverError::Kernel(Error::InvalidState)); }
        let target = self.kernel.target(id);
        let result = match target { Some(target) => self.episodes[id].admit(Some(target.as_slice())), None => self.episodes[id].admit(None) };
        proof { self.framed(&prior, id); }
        Ok(result)
    }

    pub fn land_write(&mut self, id: usize, owner: u64, index: usize, value: u64) -> (r: Result<(), DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).control() == old(self).control(),
            r.is_ok() ==> !final(self).pending(id) && final(self).resource(id)[index as int].value == value,
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if self.kernel.phase(id) != Some(Phase::Loading) { return Err(DriverError::Kernel(Error::InvalidState)); }
        let result = match self.episodes[id].land_write(owner, index, value) {
            Ok(()) => Ok(()), Err(e) => Err(DriverError::Effect(e)),
        };
        proof { self.framed(&prior, id); }
        result
    }

    pub fn end(&mut self, id: usize) -> (r: Result<(), DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).control() == old(self).control(),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if self.kernel.phase(id) != Some(Phase::Loading) { return Err(DriverError::Kernel(Error::InvalidState)); }
        let accepted = self.episodes[id].end();
        proof { self.framed(&prior, id); }
        if !accepted { return Err(DriverError::Kernel(Error::InvalidState)); }
        Ok(())
    }

    pub fn finish(&mut self, id: usize) -> (r: Result<(), DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id, paper::Rule::Finish),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if !self.kernel.contains(id) { return Err(DriverError::Kernel(Error::Unknown)); }
        if !self.episodes[id].is_settled() { return Err(DriverError::Pending); }
        match self.kernel.finish(id) {
            Ok(()) => { proof { self.framed(&prior, id); } Ok(()) },
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(DriverError::Kernel(e)) },
        }
    }

    /// Retirement is a control request, preserving pending stages and resources.
    pub fn retire(&mut self, id: usize) -> (r: Result<(), DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id, paper::Rule::Retire),
    {
        let ghost prior = *self;
        match self.kernel.retire(id) {
            Ok(()) => { proof { self.framed(&prior, id); } Ok(()) },
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(DriverError::Kernel(e)) },
        }
    }

    /// Delay diversion until the admitted stage has landed. The kernel stays
    /// Loading during that interval; it publishes no new provider bindings.
    pub fn depart(&mut self, id: usize) -> (r: Result<(), DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id,
                if old(self).control().fibers[id].phase == Phase::Loading { paper::Rule::Divert } else { paper::Rule::Leave }),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if !self.kernel.contains(id) { return Err(DriverError::Kernel(Error::Unknown)); }
        if self.episodes[id].is_pending() { return Err(DriverError::Pending); }
        match self.kernel.leave_if_changed(id) {
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(DriverError::Kernel(e)) },
            Ok(()) => { self.episodes[id].cancel(); proof { self.framed(&prior, id); } Ok(()) },
        }
    }

    /// Guard, real inverse execution and committed-view release are one verified
    /// method. There is no public access to an unguarded journal rollback.
    pub fn unload(&mut self, id: usize) -> (r: Result<(), DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id, paper::Rule::Unload)
                && final(self).resource(id) == old(self).initial(id),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if !self.kernel.contains(id) { return Err(DriverError::Kernel(Error::Unknown)); }
        if !self.episodes[id].is_settled() || self.episodes[id].is_pending() { return Err(DriverError::Pending); }
        if let Err(e) = self.kernel.begin_cleanup(id) {
            proof { self.kernel.unchanged_observations(&prior.kernel); }
            return Err(DriverError::Kernel(e));
        }
        let _restored = self.episodes[id].rollback();
        assert(_restored);
        let ghost middle = self.kernel;
        match self.kernel.finish_cleanup(id) {
            Ok(()) => { proof { self.framed(&prior, id); } Ok(()) },
            Err(e) => { proof { self.kernel.unchanged_observations(&middle); self.framed(&prior, id); } Err(DriverError::Kernel(e)) },
        }
    }

    pub fn remove(&mut self, id: usize) -> (r: Result<(), DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            r.is_ok() ==> paper::step(old(self).control(), final(self).control(), id, paper::Rule::Remove),
    {
        let ghost prior = *self;
        match self.kernel.remove(id) {
            Ok(()) => { proof { self.framed(&prior, id); } Ok(()) },
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(DriverError::Kernel(e)) },
        }
    }

    pub fn phase(&self, id: usize) -> (phase: Option<Phase>)
        ensures phase == if paper::registered(self.control(), id) { Some(self.control().fibers[id].phase) } else {None},
    { proof { self.kernel.paper_observations(id); } self.kernel.phase(id) }

    pub fn read(&self, id: usize, index: usize) -> (value: Option<u64>)
        requires self.wf(),
        ensures paper::registered(self.control(), id) && index < self.resource(id).len() ==> value == Some(self.resource(id)[index as int].value),
    {
        proof { self.kernel.paper_observations(id); }
        if !self.kernel.contains(id) { return None; }
        self.episodes[id].read(index)
    }
}
} // verus!
