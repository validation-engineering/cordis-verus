//! Stable publications and cleanup leases for native compatibility hosts.
//!
//! A publication identifies one logical owner's service slot. Revocation hides
//! that slot from new lookup without invalidating existing cleanup leases.
//! Values and callbacks stay in the host; replacing a value in a slot does not
//! replace its publication identity. This registry proves its own lifetime
//! invariant, not correspondence with a host or the paper's fixed interfaces.
use crate::Port;
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct PublicationId(pub usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct LeaseId(pub usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum PublicationError { Unknown, Revoked, Conflict, Relied, Visible, Released, Capacity, InvalidState }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct Publication {
    pub owner: usize,
    pub generation: u64,
    pub port: Port,
    pub slot: usize,
    pub visible: bool,
    pub retained: bool,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct Lease {
    pub publication: PublicationId,
    pub live: bool,
}

/// IDs are monotonic indices and never reused. Tombstones make stale handles
/// unambiguous; compaction/reuse is intentionally absent from this foundation.
pub struct PublicationRegistry {
    entries: Vec<Publication>,
    leases: Vec<Lease>,
}

impl Default for PublicationRegistry {
    fn default() -> Self { Self::new() }
}

impl PublicationRegistry {
    pub closed spec fn publications(&self) -> Seq<Publication> { self.entries@ }
    pub closed spec fn lease_records(&self) -> Seq<Lease> { self.leases@ }
    pub closed spec fn unchanged(&self, prior: &Self) -> bool {
        self.entries@ == prior.entries@ && self.leases@ == prior.leases@
    }
    pub closed spec fn wf(&self) -> bool {
        &&& forall|i: int| 0 <= i < self.entries.len()
            ==> (self.entries[i].visible ==> self.entries[i].retained)
        &&& forall|i: int, j: int| 0 <= i < j < self.entries.len()
            ==> (!(self.entries[i].visible && self.entries[j].visible)
                || self.entries[i].port != self.entries[j].port)
                && (!(self.entries[i].retained && self.entries[j].retained)
                || self.entries[i].slot != self.entries[j].slot)
        &&& forall|i: int| 0 <= i < self.leases.len() && self.leases[i].live
            ==> self.leases[i].publication.0 < self.entries.len()
                && self.entries[self.leases[i].publication.0 as int].retained
    }
    pub closed spec fn unleased(&self, id: PublicationId) -> bool {
        forall|i: int| 0 <= i < self.leases.len()
            ==> !(self.leases[i].live && self.leases[i].publication == id)
    }

    pub fn new() -> (out: Self)
        ensures out.wf(), out.publications().len() == 0, out.lease_records().len() == 0,
    { Self { entries: Vec::new(), leases: Vec::new() } }

    pub fn entry(&self, id: PublicationId) -> (out: Option<Publication>)
        ensures out == if id.0 < self.publications().len() {
            Some(self.publications()[id.0 as int])
        } else { None },
    {
        if id.0 < self.entries.len() { Some(self.entries[id.0]) } else { None }
    }

    pub fn lease(&self, id: LeaseId) -> (out: Option<Lease>)
        ensures out == if id.0 < self.lease_records().len() {
            Some(self.lease_records()[id.0 as int])
        } else { None },
    {
        if id.0 < self.leases.len() { Some(self.leases[id.0]) } else { None }
    }

    /// Lookup sees only publications that still admit new consumers.
    pub fn resolve(&self, port: Port) -> (out: Option<PublicationId>)
        ensures out.is_some() ==> out.unwrap().0 < self.publications().len()
            && self.publications()[out.unwrap().0 as int].visible
            && self.publications()[out.unwrap().0 as int].port == port,
            out.is_none() ==> (forall|i: int| 0 <= i < self.publications().len()
                ==> !self.publications()[i].visible || self.publications()[i].port != port),
    {
        let mut i = 0;
        while i < self.entries.len()
            invariant i <= self.entries.len(),
                forall|j: int| 0 <= j < i ==> !self.entries[j].visible || self.entries[j].port != port,
            decreases self.entries.len() - i,
        {
            if self.entries[i].visible && self.entries[i].port == port {
                return Some(PublicationId(i));
            }
            i += 1;
        }
        None
    }

    /// Reserve a fresh identity. The host is responsible for checking owner
    /// generation and kernel admission before calling this operation.
    pub fn publish(&mut self, owner: usize, generation: u64, port: Port, slot: usize)
        -> (out: Result<PublicationId, PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).lease_records() == old(self).lease_records(),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> out.unwrap().0 == old(self).publications().len()
                && final(self).publications() == old(self).publications().push(Publication {
                    owner, generation, port, slot, visible: true, retained: true }),
    {
        if self.entries.len() == usize::MAX { return Err(PublicationError::Capacity); }
        let mut i = 0;
        while i < self.entries.len()
            invariant i <= self.entries.len(), self.wf(), self == old(self),
                forall|j: int| 0 <= j < i
                    ==> (!self.entries[j].visible || self.entries[j].port != port)
                        && (!self.entries[j].retained || self.entries[j].slot != slot),
            decreases self.entries.len() - i,
        {
            let entry = self.entries[i];
            if (entry.visible && entry.port == port) || (entry.retained && entry.slot == slot) {
                return Err(PublicationError::Conflict);
            }
            i += 1;
        }
        let id = PublicationId(self.entries.len());
        self.entries.push(Publication { owner, generation, port, slot, visible: true, retained: true });
        Ok(id)
    }

    /// A host may move initial reservation publications into the first episode
    /// only before any consumer has leased them. This is not a paper Step.
    pub fn can_adopt(&self, id: PublicationId, owner: usize, generation: u64)
        -> (out: Result<(), PublicationError>)
        ensures out.is_ok() ==> id.0 < self.publications().len()
            && self.publications()[id.0 as int].retained
            && self.publications()[id.0 as int].owner == owner
            && self.publications()[id.0 as int].generation == 0
            && generation == 1 && self.unleased(id),
    {
        if id.0 >= self.entries.len() { return Err(PublicationError::Unknown); }
        let entry = self.entries[id.0];
        if !entry.retained { return Err(PublicationError::Released); }
        if entry.owner != owner || entry.generation != 0 || generation != 1 {
            return Err(PublicationError::InvalidState);
        }
        let mut i = 0;
        while i < self.leases.len()
            invariant i <= self.leases.len(),
                forall|j: int| 0 <= j < i ==> !(self.leases[j].live && self.leases[j].publication == id),
            decreases self.leases.len() - i,
        {
            if self.leases[i].live && self.leases[i].publication == id {
                return Err(PublicationError::Relied);
            }
            i += 1;
        }
        Ok(())
    }

    /// Preserve the publication identity, owner, port, slot, visibility and
    /// leases while the host absorbs generation zero into its first episode.
    pub fn adopt(&mut self, id: PublicationId, owner: usize, generation: u64)
        -> (out: Result<(), PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).lease_records() == old(self).lease_records(),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> id.0 < old(self).publications().len()
                && old(self).publications()[id.0 as int].owner == owner
                && old(self).publications()[id.0 as int].generation == 0
                && old(self).publications()[id.0 as int].retained
                && generation == 1 && old(self).unleased(id)
                && final(self).publications() == old(self).publications().update(id.0 as int,
                    Publication { generation, ..old(self).publications()[id.0 as int] }),
    {
        self.can_adopt(id, owner, generation)?;
        let entry = self.entries[id.0];
        self.entries.set(id.0, Publication { generation, ..entry });
        Ok(())
    }

    /// Capture a publication for an admitted consumer episode. Each acquisition
    /// has its own token, so a duplicate release cannot release another user.
    pub fn acquire(&mut self, id: PublicationId) -> (out: Result<LeaseId, PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).publications() == old(self).publications(),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> out.unwrap().0 == old(self).lease_records().len()
                && final(self).lease_records() == old(self).lease_records().push(Lease { publication: id, live: true }),
    {
        if id.0 >= self.entries.len() { return Err(PublicationError::Unknown); }
        if !self.entries[id.0].visible { return Err(PublicationError::Revoked); }
        if self.leases.len() == usize::MAX { return Err(PublicationError::Capacity); }
        let token = LeaseId(self.leases.len());
        self.leases.push(Lease { publication: id, live: true });
        Ok(token)
    }

    /// Read the captured slot even after revocation, until this lease releases.
    pub fn leased_slot(&self, token: LeaseId) -> (out: Result<usize, PublicationError>)
        requires self.wf(),
        ensures out.is_ok() ==> token.0 < self.lease_records().len()
            && self.lease_records()[token.0 as int].live
            && self.publications()[self.lease_records()[token.0 as int].publication.0 as int].retained
            && out.unwrap() == self.publications()[self.lease_records()[token.0 as int].publication.0 as int].slot,
    {
        if token.0 >= self.leases.len() { return Err(PublicationError::Unknown); }
        let lease = self.leases[token.0];
        if !lease.live { return Err(PublicationError::Released); }
        Ok(self.entries[lease.publication.0].slot)
    }

    pub fn release(&mut self, token: LeaseId) -> (out: Result<(), PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).publications() == old(self).publications(),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> token.0 < old(self).lease_records().len()
                && final(self).lease_records() == old(self).lease_records().update(token.0 as int,
                    Lease { publication: old(self).lease_records()[token.0 as int].publication, live: false }),
    {
        if token.0 >= self.leases.len() { return Err(PublicationError::Unknown); }
        let lease = self.leases[token.0];
        if !lease.live { return Err(PublicationError::Released); }
        self.leases.set(token.0, Lease { publication: lease.publication, live: false });
        Ok(())
    }

    /// Idempotently remove from new lookup, retaining identity and value slot.
    pub fn revoke(&mut self, id: PublicationId) -> (out: Result<(), PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).lease_records() == old(self).lease_records(),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> id.0 < old(self).publications().len()
                && final(self).publications() == old(self).publications().update(id.0 as int,
                    Publication { visible: false, ..old(self).publications()[id.0 as int] }),
    {
        if id.0 >= self.entries.len() { return Err(PublicationError::Unknown); }
        let entry = self.entries[id.0];
        self.entries.set(id.0, Publication { visible: false, ..entry });
        Ok(())
    }

    /// Permission to destroy a revoked slot. Cleanup leases must have drained.
    pub fn reclaim(&mut self, id: PublicationId) -> (out: Result<usize, PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).lease_records() == old(self).lease_records(),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> id.0 < old(self).publications().len() && old(self).unleased(id)
                && !old(self).publications()[id.0 as int].visible
                && old(self).publications()[id.0 as int].retained
                && out.unwrap() == old(self).publications()[id.0 as int].slot
                && final(self).publications() == old(self).publications().update(id.0 as int,
                    Publication { retained: false, ..old(self).publications()[id.0 as int] }),
    {
        if id.0 >= self.entries.len() { return Err(PublicationError::Unknown); }
        let entry = self.entries[id.0];
        if entry.visible { return Err(PublicationError::Visible); }
        if !entry.retained { return Err(PublicationError::Released); }
        let mut i = 0;
        while i < self.leases.len()
            invariant i <= self.leases.len(), self.wf(), self == old(self),
                id.0 < self.entries.len(), entry == self.entries[id.0 as int], !entry.visible, entry.retained,
                forall|j: int| 0 <= j < i ==> !(self.leases[j].live && self.leases[j].publication == id),
            decreases self.leases.len() - i,
        {
            if self.leases[i].live && self.leases[i].publication == id {
                return Err(PublicationError::Relied);
            }
            i += 1;
        }
        self.entries.set(id.0, Publication { retained: false, ..entry });
        Ok(entry.slot)
    }
}

}
