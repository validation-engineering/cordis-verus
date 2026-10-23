//! Real slot ownership for an execution scope. Captures use the original Cell;
//! ordinary replacements must acquire this same slot lock.
use super::{Capture, Cell, Predicate, Slot};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::ReversibleValue;
#[cfg(verus_keep_ghost)]
use std::sync::Arc;
use vstd::prelude::*;
use vstd::rwlock::WriteHandle;

verus! {
pub(crate) struct Exclusive<'a> {slot:&'a Slot,cell:Cell,guard:WriteHandle<'a,Cell,Predicate>}
impl Slot {
    pub(crate) fn acquire_exclusive(&self)->(out:Exclusive<'_>)
        ensures out.wf(),out.slot()==*self,
    {let (cell,guard)=self.inner.acquire_write();Exclusive {slot:self,cell,guard}}
}
impl<'a> Exclusive<'a> {
    pub(crate) closed spec fn slot(&self)->Slot {*self.slot}
    pub(crate) closed spec fn value(&self)->Arc<ReversibleValue> {self.cell.value.value()}
    pub(crate) closed spec fn revision(&self)->u64 {self.cell.value.revision_spec()}
    pub(crate) closed spec fn wf(&self)->bool {self.guard.rwlock()==*self.slot.inner && self.slot.inner.inv(self.cell)}
    pub(crate) fn capture(&self)->(out:Capture)
        requires self.wf(),ensures out.wf(),out.slot()==self.slot(),out.value_spec()==self.value(),out.revision_spec()==self.revision(),
    {self.cell.capture(self.slot)}
    pub(crate) fn release(self) requires self.wf(), {self.guard.release_write(self.cell)}
}
}
