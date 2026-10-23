//! Executable producer census for a declared root/Child value scope. Captures
//! are taken after an authentic endpoint and retain only erased proof evidence.
use super::RecordedExecution;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::interleaving::sources::interval;
use crate::reversible_value::managed::interleaving::sources::interval::{Census, Interval};
use crate::reversible_value::{self as scalar, joint, payload};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    managed::interleaving::sources::producer::Producer, service_composition::Address,
};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn scalar_addresses(values:Seq<scalar::ReversibleValue>)->Set<Address>
    decreases values.len(),
{if values.len()==0 {Set::empty()} else {scalar_addresses(values.drop_last()).insert(Address {journal:values.last().journal_spec(),key:values.last().object().key})}}
pub open spec fn payload_addresses<T:?Sized>(values:Seq<payload::SharedPayload<T>>)->Set<Address>
    decreases values.len(),
{if values.len()==0 {Set::empty()} else {payload_addresses(values.drop_last()).insert(Address {journal:values.last().journal_spec(),key:values.last().key()})}}
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    /// Capture the common endpoint and discharge the registered root/Child
    /// census in one real host call. The returned proof diagnostic is erased;
    /// it does not promise automatic rollback or a runtime error indicator.
    pub fn capture_invocation_census<E:crate::reversible_value::effect::ScalarEffect>(&mut self,journal:&joint::Journal,
        _report:&crate::reversible_value::managed::root::RegisteredReport<E,T>,_id:usize,_offset:usize,
        scalars:&[scalar::ReversibleValue],payloads:&[payload::SharedPayload<T>])
        ->(out:Ghost<Census<A,R,T,M,X>>)
        requires old(self).wf(),old(self).histories().contains_key(_id),old(self).baseline().cleanup_state().live(_id),
            _report.completed(),_report.effects_before_return(),_report.episode_interval(),_report.endpoint_source(),
            _report.result->Ok_0.witnessed(),_report.result->Ok_0.recovery_history(),_report.completion().journal()==*journal,
            _report.retained_recovery(old(self).baseline(),_id,_offset as nat),crate::reversible_value::managed::retained(_report.result->Ok_0.steps@,old(self).baseline(),_id,_offset as nat),
            forall|i:int|0<=i<_report.result->Ok_0.steps.len() ==> (#[trigger] _report.result->Ok_0.steps@[i]).carrier().covered(old(self).value_sources()),
            scalar_addresses(scalars@).union(payload_addresses(payloads@))==_report.return_values().dom(),
            forall|i:int|0<=i<scalars.len() ==> (#[trigger] scalars@[i]).journal_spec()==*journal,
            forall|i:int|0<=i<payloads.len() ==> (#[trigger] payloads@[i]).journal_spec()==*journal,
        ensures final(self).wf(),final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),
            final(self).histories()==old(self).histories(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),final(self).value_sources().extends(old(self).value_sources()),
            out@.interval.wf(),out@.interval.start==_report.completion(),out@.interval.producers.dom()==_report.return_values().dom(),
            out@.issue.is_some() ==> out@.interval.diagnosed(out@.issue.unwrap(),_report.obligations(final(self).baseline(),_id,_offset as nat)),
            out@.issue.is_none() ==> {
                let events=out@.interval.events;let initial=_report.obligations(final(self).baseline(),_id,_offset as nat);
                crate::reversible_value::managed::interleaving::obligations::recover(
                    crate::reversible_value::managed::interleaving::outstanding(events,initial,_report.return_values().dom(),events.len()),
                    crate::reversible_value::managed::interleaving::endpoint::observe(_report.result->Ok_0.steps@,events,out@.interval.end))==Some(_report.begin_values())
            },
    {
        let tracked start=_report.completion_witness();
        let tracked mut receipts=Map::<u8,joint::Receipt>::tracked_empty();
        proof {receipts.tracked_insert(0,start.duplicate());}
        let view=journal.read();view.certify_receipts::<u8>(Tracked(&receipts));
        proof {assert(receipts[0].journal()==view.journal_spec());assert(receipts[0].wf());assert(view.events().len()>0);}
        let snapshot=view.finish();let _end=snapshot.checkpoint_receipt();
        let _interval=self.capture_recovery_interval(journal,scalars,payloads,Tracked(start),Tracked(_end.borrow()));
        let ghost issue=_report.recorded_census(self,_id,_offset as nat,_interval@);
        Ghost(Census {interval:_interval@,issue})
    }
    /// Capture all producers in the supplied actual scope, including raw
    /// operations and retired typed owners. Existing execution/cleanup state
    /// is unchanged. All journal scans and projection storage erase at runtime.
    pub fn capture_recovery_interval(&mut self,journal:&joint::Journal,scalars:&[scalar::ReversibleValue],payloads:&[payload::SharedPayload<T>],
        Tracked(start):Tracked<&joint::Receipt>,Tracked(end):Tracked<&joint::Receipt>)->(out:Ghost<Interval<A,R,T,M,X>>)
        requires old(self).wf(),start.wf(),end.wf(),end.covers(start),end.journal()==*journal,
            forall|i:int|0<=i<scalars.len() ==> (#[trigger] scalars@[i]).journal_spec()==*journal,
            forall|i:int|0<=i<payloads.len() ==> (#[trigger] payloads@[i]).journal_spec()==*journal,
        ensures final(self).wf(),final(self).core()==old(self).core(),final(self).baseline()==old(self).baseline(),
            final(self).histories()==old(self).histories(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).source_order_extends(old(self)),final(self).value_sources().extends(old(self).value_sources()),
            out@.wf(),out@.start==*start,out@.end==*end,
            out@.producers.dom()==scalar_addresses(scalars@).union(payload_addresses(payloads@)),
            forall|key:Address|#[trigger] out@.producers.contains_key(key) ==> out@.producers[key].carrier().covered(final(self).value_sources()),
    {
        proof {self.facts();}
        let ghost prior=*self;
        let ghost mut producers=Map::<Address,Producer<T>>::empty();
        let mut i=0;
        while i<scalars.len()
            invariant i<=scalars.len(),self.wf(),*self==prior,start.wf(),end.wf(),end.covers(start),end.journal()==*journal,
                forall|k:int|0<=k<scalars.len() ==> (#[trigger] scalars@[k]).journal_spec()==*journal,
                interval::captured(producers,*end),
                producers.dom()==scalar_addresses(scalars@.take(i as int)),
                forall|key:Address|#[trigger] producers.contains_key(key) ==> producers[key].carrier().covered(self.value_sources()),
            decreases scalars.len()-i,
        {
            let value=&scalars[i];let _snapshot=value.snapshot_caused(Tracked(Some(end)));
            proof {
                let p=Producer::<T>::Scalar(_snapshot);p.certify();let key=p.address();
                producers=producers.insert(key,p);
                assert(scalars@.take(i as int+1).drop_last() =~= scalars@.take(i as int));
                assert(producers.dom() =~= scalar_addresses(scalars@.take(i as int+1)));

            }
            i+=1;
        }
        proof {assert(scalars@.take(scalars.len() as int) =~= scalars@);}
        let mut j=0;
        while j<payloads.len()
            invariant j<=payloads.len(),self.wf(),self.core()==prior.core(),self.baseline()==prior.baseline(),self.histories()==prior.histories(),
                self.origins()==prior.origins(),self.terminal()==prior.terminal(),self.recovery_boundary()==prior.recovery_boundary(),self.value_sources().extends(prior.value_sources()),
                start.wf(),end.wf(),end.covers(start),end.journal()==*journal,
                forall|k:int|0<=k<payloads.len() ==> (#[trigger] payloads@[k]).journal_spec()==*journal,
                interval::captured(producers,*end),
                producers.dom()==scalar_addresses(scalars@).union(payload_addresses(payloads@.take(j as int))),
                forall|key:Address|#[trigger] producers.contains_key(key) ==> producers[key].carrier().covered(self.value_sources()),
            decreases payloads.len()-j,
        {
            let value=&payloads[j];let _source=value.source_snapshot_in(journal,Tracked(Some(end)));
            proof {
                self.facts();self.value_sources.borrow_mut().retain(_source.borrow().witness());reveal(RecordedExecution::wf);
                let p=Producer::Payload(_source@);p.certify();_source@.facts();let key=p.address();
                producers=producers.insert(key,p);
                assert(payloads@.take(j as int+1).drop_last() =~= payloads@.take(j as int));
                assert(producers.dom() =~= scalar_addresses(scalars@).union(payload_addresses(payloads@.take(j as int+1))));

            }
            j+=1;
        }
        proof {
            assert(payloads@.take(payloads.len() as int) =~= payloads@);
            reveal(RecordedExecution::source_order_extends);
        }
        let ghost out=Interval::new(producers,*start,end);Ghost(out)
    }
}
}
