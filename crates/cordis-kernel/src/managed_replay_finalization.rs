//! Bind post-root own services to the actual successful native Finish. The
//! retained typed publication snapshot includes the real episode and values;
//! no caller-supplied expected publication is accepted.
use super::{environment::Environment, Source};
use crate::lifecycle_state::{
    native::runtime::{history, NativeRuntime},
    services::NativeEpisode,
};
use crate::reversible_value::{
    effect::ScalarEffect,
    managed::{interleaving::history::lifecycle::RecordedExecution, Slot},
};
use crate::Error;
#[cfg(verus_keep_ghost)]
use crate::{action_ledger::ActionTicket, Port};
use vstd::prelude::*;

verus! {
#[allow(dead_code)] // The authentic typed episode and cut are retained proof evidence.
pub struct Publication<T:?Sized,M> {environment:Environment<T>,episode:Ghost<NativeEpisode<Slot<T,M>>>,cut:history::Snapshot<Slot<T,M>>}
impl<T:?Sized,M> Publication<T,M> {
    pub closed spec fn environment(&self)->Environment<T> {self.environment}
    pub closed spec fn cut(&self)->history::Snapshot<Slot<T,M>> {self.cut}
    pub closed spec fn certified(&self,origin:ActionTicket,ports:Seq<Port>)->bool {
        self.cut.certified() && self.episode@.wf() && self.episode@.origin()==origin
            && self.environment.captured(self.episode@,ports)
            && self.cut.history().states.last().publications.contains_key(origin.id)
            && self.cut.history().states.last().publications[origin.id].origin()==origin
            && self.cut.history().states.last().publications[origin.id].values()==self.episode@.owned()
    }
    pub fn observations(&self)->(out:&Environment<T>) ensures *out==self.environment(), {&self.environment}
    pub proof fn facts(&self,origin:ActionTicket,ports:Seq<Port>)
        requires self.certified(origin,ports),
        ensures self.environment().wf(),self.environment().declarations(ports),self.cut().certified(),
            self.cut().history().states.last().publications.contains_key(origin.id),
    {}
}
impl<E:ScalarEffect,T:?Sized,M> Source<E,T,M> {
    /// Finish the actual recorded owner and retain its exact native publication.
    /// Failure preserves the source certificate, so the same owner can retry.
    pub fn finish<P,H,C,G,A,R,X>(&mut self,runtime:&mut NativeRuntime<P,H,Slot<T,M>>,owner:&mut RecordedExecution<C,G,A,R,T,M,X>)->(out:Result<(),Error>)
        requires old(self).wf(),old(runtime).wf(),old(owner).wf(),old(runtime).journal_spec()==old(self).original().completion().journal(),
        ensures final(self).wf(),final(runtime).wf(),final(owner).wf(),
            final(owner).same_inverse_word(old(owner)),old(owner).conserved() ==> final(owner).conserved(),
            final(self).original()==old(self).original(),final(self).program()==old(self).program(),final(self).input_spec()==old(self).input_spec(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> final(self).final_publication().is_some()
                && final(self).final_publication().unwrap().certified(final(self).original().origin,final(self).provision_ports()),
    {
        proof {owner.facts();}
        let episode=match owner.execution().native() {Some(e)=>e,None=>return Err(Error::InvalidState)};
        if episode.ticket()!=self.source_origin() {return Err(Error::InvalidState);}
        let environment=Environment::capture(episode,self.provisions.as_slice());
        let ghost captured=*episode;
        owner.finish(runtime,self.origin.id)?;
        proof {owner.facts();}
        let cut=runtime.publication_snapshot_following(Tracked(self.completion.borrow()));
        proof {
            runtime.history_correspondence();runtime.publication_facts();
            assert(cut.certified());
            assert(captured.wf() && captured.origin()==self.original().origin);
            assert(environment.captured(captured,self.provisions@));
            assert(cut.history().states.last().publications.contains_key(self.origin.id));
            assert(cut.history().states.last().publications[self.origin.id].origin()==self.origin);
            assert(cut.history().states.last().publications[self.origin.id].values()==captured.owned());
        }
        let publication=Publication {environment,episode:Ghost(captured),cut};
        assert(publication.certified(self.original().origin,self.provisions@));
        self.finalized=Some(publication);
        Ok(())
    }
}
}
