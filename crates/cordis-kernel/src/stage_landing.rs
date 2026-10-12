//! Interpret the actual iterator result once, before selecting continuation.
//! This contracts ownership and accumulator control; an opaque callback still
//! needs its own effect law to claim restoration of the external world.
use super::CleanupQueue;
#[cfg(verus_keep_ghost)]
use crate::episode::{accumulator_step, AccumulatorRule};
use vstd::prelude::*;

verus! {

pub struct StageReport<E> {
    pub token:Option<usize>,
    pub continue_iteration:bool,
    pub error:Option<E>,
}

impl<T> CleanupQueue<T> {
    /// The input is the real poll result. No predicted token, continuation or
    /// inverse is accepted. Rejection returns that result without destroying it.
    #[allow(clippy::type_complexity)]
    pub fn land_result<E>(&mut self,result:Result<Option<T>,E>)
        ->(out:Result<StageReport<E>,Result<Option<T>,E>>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_ok()==old(self).protocol().stage().pending(),
            out.is_err() ==> out->Err_0==result && final(self).same(old(self)),
            out.is_ok() ==> {
                let report=out->Ok_0;
                &&& !final(self).protocol().stage().pending()
                &&& report.continue_iteration==!final(self).protocol().stage().settled()
                &&& report.error==match result {Err(error)=>Some(error),_=>None}
                &&& match result {
                    Ok(Some(payload))=>{
                        &&& report.token==Some(old(self).slots().len() as usize)
                        &&& final(self).slots()==old(self).slots().push(Some(payload))
                        &&& report.continue_iteration==!old(self).protocol().stage().cancellation()
                        &&& accumulator_step(old(self).protocol().stage().abstract_view(),final(self).protocol().stage().abstract_view(),
                            if old(self).protocol().stage().cancellation() {AccumulatorRule::Divert(report.token)}
                            else {AccumulatorRule::Iter(report.token.unwrap())})
                    },
                    _=>report.token.is_none() && !report.continue_iteration && final(self).slots()==old(self).slots()
                        && accumulator_step(old(self).protocol().stage().abstract_view(),final(self).protocol().stage().abstract_view(),
                            if old(self).protocol().stage().cancellation() {AccumulatorRule::Divert(None)} else {AccumulatorRule::Finish}),
                }
            },
    {
        if !self.is_pending() {return Err(result);}
        let token=match result {
            Ok(Some(payload))=>{
                let landed=self.land(payload);
                assert(landed.is_ok());
                match landed {Ok(token)=>Some(token),Err(_)=>{assert(false);panic!("admitted landing");}}
            },
            Ok(None)=>{let _ended=self.end();assert(_ended);None},
            Err(error)=>{
                let _ended=self.end();assert(_ended);
                return Ok(StageReport {token:None,continue_iteration:false,error:Some(error)});
            },
        };
        let continue_iteration=!self.journal.is_settled();
        Ok(StageReport {token,continue_iteration,error:None})
    }
}

}
