//! A real typed allocation held across execution and restoration. Ordinary
//! writers and cleanup use the same storage, lock and checked mutation cores.
#[cfg(verus_keep_ghost)]
use super::State;
use super::{restoration, Capture, Predicate, SharedPayload, Storage};
use crate::reversible_value::registration;
use std::sync::Arc;
use vstd::prelude::*;
use vstd::rwlock::WriteHandle;

verus! {
pub(crate) struct Exclusive<'a,T:?Sized> {
    target:&'a SharedPayload<T>,storage:Storage<T>,guard:WriteHandle<'a,Storage<T>,Predicate<T>>,
}
impl<T:?Sized> SharedPayload<T> {
    pub(crate) fn acquire_exclusive(&self)->(out:Exclusive<'_,T>)
        ensures out.wf(),out.target()==*self,
    {let (storage,guard)=self.inner.acquire_write();Exclusive {target:self,storage,guard}}
}
impl<'a,T:?Sized> Exclusive<'a,T> {
    pub(crate) closed spec fn target(&self)->SharedPayload<T> {*self.target}
    pub(crate) closed spec fn state(&self)->Option<State<T>> {self.storage.state()}
    pub(crate) closed spec fn revision(&self)->Option<u64> {self.storage.revision()}
    pub(crate) closed spec fn wf(&self)->bool {
        self.guard.rwlock()==*self.target.inner && self.storage.belongs(*self.target)
    }
    pub(crate) fn capture(&self)->(out:Option<Capture<T>>)
        requires self.wf(),ensures out.is_some()==self.state().is_some(),
            out.is_some() ==> out.unwrap().wf() && out.unwrap().observation().wf() && out.unwrap().owner()==self.target()
                && Some(out.unwrap().observation().state())==self.state() && Some(out.unwrap().revision_spec())==self.revision(),
    {match &self.storage.live {Some(cell)=>Some(cell.capture(self.target)),None=>None}}
    pub(crate) fn apply(&mut self,value:Arc<T>,expected:Option<&Capture<T>>,Ghost(managed):Ghost<bool>,Tracked(causes):Tracked<&registration::ReceiptMap>)
        ->(out:restoration::CapturedApply<T>)
        requires old(self).wf(),registration::witnesses(*causes),
            expected.is_some() ==> expected.unwrap().wf() && expected.unwrap().owner()==old(self).target(),
        ensures final(self).wf(),final(self).target()==old(self).target(),
            out.0.is_err() ==> final(self).state()==old(self).state() && final(self).revision()==old(self).revision(),
            old(self).state().is_some()
                && (expected.is_none() || expected.unwrap().revision_spec()==old(self).revision().unwrap())
                && old(self).revision().unwrap() as int+old(self).state().unwrap().depth as int+2<=u64::MAX ==> out.0.is_ok(),
            expected.is_some() && expected.unwrap().revision_spec() as int+expected.unwrap().observation().state().depth as int+2<=u64::MAX
                ==> !(out.0.is_err() && out.0->Err_0.error==crate::versioned_value::ReplaceError::Capacity),
            out.0.is_ok() ==> out.0->Ok_0.0.wf(managed) && out.0->Ok_0.0.inverse.owner()==old(self).target()
                && out.0->Ok_0.0.inverse.after().value==value
                && old(self).state()==Some(out.0->Ok_0.0.inverse.before().state())
                && old(self).revision()==Some(out.0->Ok_0.0.inverse.before().revision)
                && final(self).state()==Some(out.0->Ok_0.0.inverse.after().state())
                && final(self).revision()==Some(out.0->Ok_0.0.inverse.after().revision)
                && out.0->Ok_0.1.wf() && out.0->Ok_0.1.owner()==old(self).target()
                && out.0->Ok_0.1.observes(out.0->Ok_0.0.inverse.after()),
            out.0.is_ok() ==> forall|k:(int,bool)|causes.contains_key(k) && #[trigger] causes[k].journal()==old(self).target().journal_spec() ==> out.0->Ok_0.0.inverse.after().commit.follows(&causes[k]),
            out.0.is_ok() && expected.is_some() ==> out.0->Ok_0.0.inverse.before().state()==expected.unwrap().observation().state()
                && out.0->Ok_0.0.inverse.before().revision==expected.unwrap().revision_spec(),
            out.0.is_err() ==> out.0->Err_0.value==value && out.1@.is_some() && out.1@.unwrap().owner()==old(self).target()
                && out.1@.unwrap().explains(out.0->Err_0.error),
    {self.target.apply_captured_in(&mut self.storage,value,expected,Ghost(managed),Tracked(causes))}
    /// vstd's write handle needs an explicit release on every ordinary exit.
    pub(crate) fn release(self) requires self.wf(), {self.guard.release_write(self.storage)}
}
}
