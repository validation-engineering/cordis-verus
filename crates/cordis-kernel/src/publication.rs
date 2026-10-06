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

/// A stored lease carries its stable identity independently of its position.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct LeaseRecord {
    pub id: LeaseId,
    pub lease: Lease,
}

/// Publication IDs remain monotonic indices with tombstones. Lease IDs are
/// monotonically allocated too, but only active leases occupy physical records.
/// The allocation high-water mark distinguishes released and unknown tokens
/// without retaining one tombstone per historical acquisition.
pub struct PublicationRegistry {
    entries: Vec<Publication>,
    leases: Vec<LeaseRecord>,
    next_lease: usize,
}

impl Default for PublicationRegistry {
    fn default() -> Self { Self::new() }
}

impl PublicationRegistry {
    pub closed spec fn publications(&self) -> Seq<Publication> { self.entries@ }
    pub closed spec fn lease_records(&self) -> Seq<LeaseRecord> { self.leases@ }
    pub closed spec fn lease_allocations(&self) -> nat { self.next_lease as nat }
    pub closed spec fn active_lease(&self, id: LeaseId) -> Option<Lease> {
        if exists|i: int| 0 <= i < self.leases.len() && self.leases[i].id == id {
            let i = choose|i: int| 0 <= i < self.leases.len() && self.leases[i].id == id;
            Some(self.leases[i].lease)
        } else { None }
    }
    pub closed spec fn unchanged(&self, prior: &Self) -> bool {
        self.entries@ == prior.entries@ && self.leases@ == prior.leases@
            && self.next_lease == prior.next_lease
    }
    pub closed spec fn wf(&self) -> bool {
        &&& forall|i: int| 0 <= i < self.entries.len()
            ==> (self.entries[i].visible ==> self.entries[i].retained)
        &&& forall|i: int, j: int| 0 <= i < j < self.entries.len()
            ==> (!(self.entries[i].visible && self.entries[j].visible)
                || self.entries[i].port != self.entries[j].port)
                && (!(self.entries[i].retained && self.entries[j].retained)
                || self.entries[i].slot != self.entries[j].slot)
        &&& self.leases.len() <= self.next_lease
        &&& forall|i: int| 0 <= i < self.leases.len()
            ==> self.leases[i].id.0 < self.next_lease
                && self.leases[i].lease.live
                && self.leases[i].lease.publication.0 < self.entries.len()
                && self.entries[self.leases[i].lease.publication.0 as int].retained
        &&& forall|i: int, j: int| 0 <= i < j < self.leases.len()
            ==> self.leases[i].id.0 < self.leases[j].id.0
    }
    pub closed spec fn unleased(&self, id: PublicationId) -> bool {
        forall|i: int| 0 <= i < self.leases.len()
            ==> !(self.leases[i].lease.publication == id)
    }

    pub fn new() -> (out: Self)
        ensures out.wf(), out.publications().len() == 0, out.lease_records().len() == 0,
            out.lease_allocations() == 0,
    { Self { entries: Vec::new(), leases: Vec::new(), next_lease: 0 } }

    /// Stored identities, including reclaimed publication tombstones.
    pub fn publication_records(&self) -> (count: usize)
        ensures count == self.publications().len(),
    { self.entries.len() }

    /// Physical active lease records. Released leases occupy no record.
    pub fn lease_record_count(&self) -> (count: usize)
        ensures count == self.lease_records().len(),
    { self.leases.len() }

    /// Cumulative successful lease allocations; never decreases or reuses IDs.
    pub fn lease_allocation_count(&self) -> (count: usize)
        ensures count == self.lease_allocations(),
    { self.next_lease }

    pub fn entry(&self, id: PublicationId) -> (out: Option<Publication>)
        ensures out == if id.0 < self.publications().len() {
            Some(self.publications()[id.0 as int])
        } else { None },
    {
        if id.0 < self.entries.len() { Some(self.entries[id.0]) } else { None }
    }

    fn lease_index(&self, id: LeaseId) -> (out: Option<usize>)
        ensures out.is_some() ==> out.unwrap() < self.lease_records().len()
            && self.lease_records()[out.unwrap() as int].id == id,
            out.is_none() ==> (forall|i: int| 0 <= i < self.lease_records().len()
                ==> self.lease_records()[i].id != id),
    {
        let mut i = 0;
        while i < self.leases.len()
            invariant i <= self.leases.len(),
                forall|j: int| 0 <= j < i ==> self.leases[j].id != id,
            decreases self.leases.len() - i,
        {
            if self.leases[i].id == id { return Some(i); }
            i += 1;
        }
        None
    }

    proof fn lease_at_position(&self, i: int)
        requires self.wf(), 0 <= i < self.leases.len(),
        ensures self.active_lease(self.leases[i].id) == Some(self.leases[i].lease),
    {
        let id = self.leases[i].id;
        assert(exists|j: int| 0 <= j < self.leases.len() && self.leases[j].id == id);
        let j = choose|j: int| 0 <= j < self.leases.len() && self.leases[j].id == id;
        assert(i == j);
    }

    /// Query an active lease by stable ID. Released and unknown IDs return None;
    /// use release/leased_slot when the distinction is needed.
    // The explicit branch carries the uniqueness proof erased in Cargo builds.
    #[allow(clippy::manual_map)]
    pub fn lease(&self, id: LeaseId) -> (out: Option<Lease>)
        requires self.wf(),
        ensures out == self.active_lease(id),
    {
        match self.lease_index(id) {
            Some(i) => {
                proof {
                    self.lease_at_position(i as int);
                    assert(self.active_lease(id) == Some(self.leases[i as int].lease));
                }
                Some(self.leases[i].lease)
            },
            None => {
                proof {
                    if exists|j: int| 0 <= j < self.leases.len() && self.leases[j].id == id {
                        let j = choose|j: int| 0 <= j < self.leases.len() && self.leases[j].id == id;
                        assert(self.lease_records()[j].id != id);
                    }
                    assert(self.active_lease(id).is_none());
                }
                None
            },
        }
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
            final(self).lease_allocations() == old(self).lease_allocations(),
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
                forall|j: int| 0 <= j < i ==> !(self.leases[j].lease.publication == id),
            decreases self.leases.len() - i,
        {
            if self.leases[i].lease.publication == id {
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
            final(self).lease_allocations() == old(self).lease_allocations(),
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
    /// has a fresh logical token, regardless of earlier physical record removal.
    pub fn acquire(&mut self, id: PublicationId) -> (out: Result<LeaseId, PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).publications() == old(self).publications(),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> out.unwrap().0 == old(self).lease_allocations()
                && final(self).lease_allocations() == old(self).lease_allocations() + 1
                && final(self).lease_records() == old(self).lease_records().push(LeaseRecord {
                    id: out.unwrap(), lease: Lease { publication: id, live: true } }),
    {
        if id.0 >= self.entries.len() { return Err(PublicationError::Unknown); }
        if !self.entries[id.0].visible { return Err(PublicationError::Revoked); }
        if self.next_lease == usize::MAX { return Err(PublicationError::Capacity); }
        let token = LeaseId(self.next_lease);
        self.next_lease += 1;
        self.leases.push(LeaseRecord { id: token, lease: Lease { publication: id, live: true } });
        Ok(token)
    }

    /// Read the captured slot even after revocation, until this lease releases.
    pub fn leased_slot(&self, token: LeaseId) -> (out: Result<usize, PublicationError>)
        requires self.wf(),
        ensures out == if token.0 >= self.lease_allocations() {
            Err(PublicationError::Unknown)
        } else { match self.active_lease(token) {
            Some(lease) => Ok(self.publications()[lease.publication.0 as int].slot),
            None => Err(PublicationError::Released),
        } },
    {
        if token.0 >= self.next_lease { return Err(PublicationError::Unknown); }
        match self.lease(token) {
            Some(lease) => Ok(self.entries[lease.publication.0].slot),
            None => Err(PublicationError::Released),
        }
    }

    /// Remove only the matching active record. Retaining the allocation counter
    /// makes duplicate release unable to affect any later acquisition.
    pub fn release(&mut self, token: LeaseId) -> (out: Result<(), PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).publications() == old(self).publications(),
            final(self).lease_allocations() == old(self).lease_allocations(),
            out == if token.0 >= old(self).lease_allocations() { Err(PublicationError::Unknown) }
                else if old(self).active_lease(token).is_none() { Err(PublicationError::Released) }
                else { Ok(()) },
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> final(self).active_lease(token).is_none()
                && final(self).lease_records().len() + 1 == old(self).lease_records().len()
                && (exists|i: int| 0 <= i < old(self).lease_records().len()
                    && old(self).lease_records()[i].id == token
                    && final(self).lease_records() == old(self).lease_records().remove(i)),
            forall|id: LeaseId| id != token ==> final(self).active_lease(id) == old(self).active_lease(id),
    {
        if token.0 >= self.next_lease { return Err(PublicationError::Unknown); }
        match self.lease_index(token) {
            Some(i) => {
                let ghost prior = *self;
                self.leases.remove(i);
                proof {
                    assert(self.wf());
                    assert forall|id: LeaseId| id != token implies
                        self.active_lease(id) == prior.active_lease(id) by {
                        if prior.active_lease(id).is_some() {
                            let j = choose|j: int| 0 <= j < prior.leases.len() && prior.leases[j].id == id;
                            prior.lease_at_position(j);
                            assert(j != i);
                            let k = if j < i { j } else { j - 1 };
                            assert(0 <= k < self.leases.len());
                            assert(self.leases[k] == prior.leases[j]);
                            self.lease_at_position(k);
                        } else {
                            assert forall|k: int| 0 <= k < self.leases.len() implies self.leases[k].id != id by {
                                let j = if k < i { k } else { k + 1 };
                                assert(0 <= j < prior.leases.len());
                                assert(self.leases[k] == prior.leases[j]);
                                assert(prior.leases[j].id != id);
                            }
                        }
                    }
                }
                Ok(())
            }
            None => Err(PublicationError::Released),
        }
    }

    /// Idempotently remove from new lookup, retaining identity and value slot.
    pub fn revoke(&mut self, id: PublicationId) -> (out: Result<(), PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).lease_records() == old(self).lease_records(),
            final(self).lease_allocations() == old(self).lease_allocations(),
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
            final(self).lease_allocations() == old(self).lease_allocations(),
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
                forall|j: int| 0 <= j < i ==> !(self.leases[j].lease.publication == id),
            decreases self.leases.len() - i,
        {
            if self.leases[i].lease.publication == id {
                return Err(PublicationError::Relied);
            }
            i += 1;
        }
        self.entries.set(id.0, Publication { retained: false, ..entry });
        Ok(entry.slot)
    }
}

}

#[cfg(test)]
mod lease_storage_tests {
    use super::*;

    #[test]
    fn allocation_exhaustion_never_reuses_a_released_identity() {
        let mut registry = PublicationRegistry {
            entries: Vec::new(),
            leases: Vec::new(),
            next_lease: usize::MAX - 1,
        };
        let publication = registry
            .publish(0, 1, Port { key: 1, realm: 0 }, 7)
            .unwrap();
        let last = registry.acquire(publication).unwrap();
        assert_eq!(last, LeaseId(usize::MAX - 1));
        assert_eq!(registry.lease_allocation_count(), usize::MAX);
        assert_eq!(
            registry.acquire(publication),
            Err(PublicationError::Capacity)
        );
        assert_eq!(registry.leased_slot(last), Ok(7));
        registry.release(last).unwrap();
        assert_eq!(registry.lease_record_count(), 0);
        assert_eq!(
            registry.acquire(publication),
            Err(PublicationError::Capacity)
        );
        assert_eq!(registry.lease_allocation_count(), usize::MAX);
        assert_eq!(registry.release(last), Err(PublicationError::Released));
        assert_eq!(
            registry.release(LeaseId(usize::MAX)),
            Err(PublicationError::Unknown)
        );
        assert_eq!(
            registry.leased_slot(LeaseId(usize::MAX)),
            Err(PublicationError::Unknown)
        );
    }

    #[test]
    fn retained_capacity_tracks_active_peak_not_acquisition_history() {
        let mut registry = PublicationRegistry::new();
        let publication = registry
            .publish(0, 1, Port { key: 1, realm: 0 }, 7)
            .unwrap();
        let pinned = registry.acquire(publication).unwrap();
        let temporary = registry.acquire(publication).unwrap();
        registry.release(temporary).unwrap();
        let capacity = registry.leases.capacity();
        for _ in 0..10_000 {
            let temporary = registry.acquire(publication).unwrap();
            registry.release(temporary).unwrap();
            assert_eq!(registry.leases.len(), 1);
            assert_eq!(registry.leases.capacity(), capacity);
        }
        assert_eq!(registry.leased_slot(pinned), Ok(7));
        registry.release(pinned).unwrap();
        assert!(registry.leases.is_empty());
        assert_eq!(registry.lease_allocation_count(), 10_002);
    }
}
