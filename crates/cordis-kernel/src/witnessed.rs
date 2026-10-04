//! A concrete composition of the stage protocol with real inverse witnesses.
//!
//! Each successful stage writes one cell of an owned Journal. Its cleanup token
//! is exactly that journal entry's position, so a token cannot name an unrelated
//! inverse. This is a verified resource episode, not an arbitrary-closure host.
use crate::episode::StageProtocol;
use crate::history::Journal;
#[cfg(verus_keep_ghost)]
use crate::resources::Cell;
use crate::resources::ResourceError;
use crate::Binding;
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum EpisodeError { NotAdmitted, Resource(ResourceError) }

pub struct ResourceEpisode {
    journal: Journal,
    protocol: StageProtocol,
}
impl ResourceEpisode {
    pub closed spec fn wf(&self) -> bool {
        &&& self.journal.wf() && self.protocol.wf()
        &&& self.protocol.inverse_view().len() == self.journal.depth()
        &&& forall|i: int| 0 <= i < self.protocol.inverse_view().len()
            ==> self.protocol.inverse_view()[i] == i
    }
    pub closed spec fn view(&self) -> Seq<Cell> { self.journal.view() }
    pub closed spec fn initial(&self) -> Seq<Cell> { self.journal.initial() }
    pub closed spec fn history(&self) -> Seq<Seq<Cell>> { self.journal.snapshots() }
    pub closed spec fn depth(&self) -> nat { self.journal.depth() }
    pub closed spec fn pending(&self) -> bool { self.protocol.pending() }
    pub closed spec fn settled(&self) -> bool { self.protocol.settled() }
    pub closed spec fn committed(&self) -> Seq<Binding> { self.protocol.committed_view() }

    pub fn new(values: Vec<u64>, committed: Vec<Binding>) -> (out: Self)
        ensures out.wf(), out.depth() == 0, out.initial() == out.view(),
            !out.pending(), !out.settled(), out.committed() == committed@,
            out.view().len() == values.len(),
            forall|i: int| 0 <= i < values.len() ==> out.view()[i]
                == (Cell { value: values[i], owner: None, depth: 0 }),
    {
        Self { journal: Journal::new(values), protocol: StageProtocol::iterator(committed) }
    }

    /// Start another activation after exact recovery, preserving the concrete
    /// context. Only the continuation and committed provider identities change.
    pub fn restart(&mut self, committed: Vec<Binding>) -> (accepted: bool)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).view() == old(self).view(),
            final(self).initial() == old(self).initial(), final(self).history() == old(self).history(),
            final(self).depth() == old(self).depth(),
            accepted == (old(self).depth() == 0 && !old(self).pending()),
            accepted ==> final(self).committed() == committed@ && !final(self).pending() && !final(self).settled(),
            !accepted ==> final(self).committed() == old(self).committed()
                && final(self).pending() == old(self).pending() && final(self).settled() == old(self).settled(),
    {
        if !self.journal.is_empty() || self.protocol.is_pending() { return false; }
        self.protocol = StageProtocol::iterator(committed);
        true
    }

    pub fn admit(&mut self, target: Option<&[Binding]>) -> (accepted: bool)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).initial() == old(self).initial(),
            final(self).history() == old(self).history(), final(self).depth() == old(self).depth(),
            final(self).view() == old(self).view(), final(self).committed() == old(self).committed(),
            accepted == final(self).pending(), old(self).pending() ==> accepted,
            accepted ==> old(self).pending() || (!old(self).settled() && target.is_some() && target.unwrap()@ == old(self).committed()),
            !accepted ==> final(self).settled(),
    { self.protocol.admit(target) }

    pub fn cancel(&mut self)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).initial() == old(self).initial(),
            final(self).history() == old(self).history(), final(self).depth() == old(self).depth(),
            final(self).view() == old(self).view(), final(self).committed() == old(self).committed(),
            final(self).pending() == old(self).pending(), final(self).settled() == !old(self).pending(),
    { self.protocol.cancel(); }

    /// One landed stage: the actual Store inverse and protocol token are created
    /// together. A failed write changes neither the context nor its witnesses.
    pub fn land_write(&mut self, owner: u64, index: usize, value: u64) -> (result: Result<(), EpisodeError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).initial() == old(self).initial(),
            final(self).committed() == old(self).committed(),
            (old(self).pending() && old(self).depth() < usize::MAX && index < old(self).view().len()
                && (old(self).view()[index as int].owner.is_none() || old(self).view()[index as int].owner == Some(owner))
                && old(self).view()[index as int].depth < u64::MAX) ==> result.is_ok(),
            result.is_ok() ==> old(self).pending() && !final(self).pending()
                && final(self).depth() == old(self).depth() + 1
                && final(self).history() == old(self).history().push(final(self).view())
                && index < old(self).view().len()
                && final(self).view() == old(self).view().update(index as int,
                    Cell {value,owner:Some(owner),depth:(old(self).view()[index as int].depth+1) as u64})
                && final(self).view()[index as int].value == value,
            result.is_err() ==> final(self).view() == old(self).view()
                && final(self).history() == old(self).history()
                && final(self).depth() == old(self).depth()
                && final(self).pending() == old(self).pending()
                && final(self).settled() == old(self).settled(),
    {
        if !self.protocol.is_pending() { return Err(EpisodeError::NotAdmitted); }
        let token = self.journal.len();
        match self.journal.write(owner, index, value) {
            Err(error) => Err(EpisodeError::Resource(error)),
            Ok(()) => {
                let _accepted = self.protocol.land(token);
                assert(_accepted);
                Ok(())
            },
        }
    }

    pub fn end(&mut self) -> (accepted: bool)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).initial() == old(self).initial(),
            final(self).history() == old(self).history(), final(self).depth() == old(self).depth(),
            final(self).view() == old(self).view(), final(self).committed() == old(self).committed(),
            accepted == old(self).pending(), accepted ==> final(self).settled() && !final(self).pending(),
    { self.protocol.end() }

    /// Unlike a host callback token, this pop invokes the corresponding proved
    /// inverse. Cleanup is blocked until every admitted stage has landed/ended.
    pub fn rollback_one(&mut self) -> (removed: bool)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).initial() == old(self).initial(),
            final(self).committed() == old(self).committed(),
            final(self).pending() == old(self).pending(), final(self).settled() == old(self).settled(),
            removed == (old(self).settled() && old(self).depth() > 0),
            removed ==> final(self).depth() + 1 == old(self).depth()
                && final(self).history() == old(self).history().drop_last()
                && final(self).view() == old(self).history()[old(self).depth() - 1],
            !removed ==> final(self).view() == old(self).view()
                && final(self).depth() == old(self).depth() && final(self).history() == old(self).history(),
    {
        let token = self.protocol.pop();
        if token.is_none() { return false; }
        assert(token.unwrap() == self.journal.depth() - 1);
        let _removed = self.journal.rollback_one();
        assert(_removed);
        true
    }

    /// Complete recovery of a settled episode, or leave an open stage intact.
    pub fn rollback(&mut self) -> (completed: bool)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).initial() == old(self).initial(),
            final(self).committed() == old(self).committed(),
            final(self).pending() == old(self).pending(), final(self).settled() == old(self).settled(),
            completed == old(self).settled(),
            completed ==> final(self).depth() == 0 && final(self).view() == old(self).initial(),
            !completed ==> final(self).view() == old(self).view()
                && final(self).depth() == old(self).depth() && final(self).history() == old(self).history(),
    {
        if !self.protocol.is_settled() { return false; }
        while !self.journal.is_empty()
            invariant self.wf(), self.settled(),
                self.initial() == old(self).initial(), self.committed() == old(self).committed(),
                self.pending() == old(self).pending(), self.settled() == old(self).settled(),
            decreases self.depth(),
        {
            let _removed = self.rollback_one();
            assert(_removed);
        }
        proof { self.journal.empty_restored(); }
        true
    }

    pub fn is_pending(&self) -> (pending: bool)
        ensures pending == self.pending(),
    { self.protocol.is_pending() }

    pub fn is_settled(&self) -> (settled: bool)
        ensures settled == self.settled(),
    { self.protocol.is_settled() }

    pub fn resource_len(&self) -> (length:usize)
        ensures length == self.view().len(),
    { self.journal.resource_len() }
    pub fn written(&self,index:usize) -> (yes:bool)
        ensures yes == (index < self.view().len() && self.view()[index as int].depth > 0),
    { self.journal.written(index) }
    pub fn read(&self, index: usize) -> (value: Option<u64>)
        ensures value == if index < self.view().len() { Some(self.view()[index as int].value) } else { None },
    { self.journal.read(index) }

    pub fn len(&self) -> (count: usize)
        ensures count == self.depth(),
    { self.journal.len() }

    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.depth() == 0),
    { self.journal.is_empty() }

    pub proof fn complete_recovery(&self)
        requires self.wf(), self.depth() == 0,
        ensures self.view() == self.initial(),
    { self.journal.empty_restored(); }
}
} // verus!
