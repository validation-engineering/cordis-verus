//! Actual restoration admission and retry receipts around a StageProtocol.
//! A selected token stays owned until Succeeded/Drained. Failed retains it;
//! explicit retry replaces only its attempt identity, never pops another token.
//! CleanupQueue owns the real payloads; callback effects and report truth remain host obligations.
use crate::episode::StageProtocol;
use crate::Binding;
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct RestoreTicket { pub domain:u64, pub attempt:u64, pub token:usize }
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum RestoreOutcome { Succeeded, Failed, Drained }
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum RestoreError { InvalidState, Capacity }

pub struct CleanupJournal {
    stages:StageProtocol,
    domain:u64,
    next:u64,
    current:Option<RestoreTicket>,
    failed:bool,
}
impl CleanupJournal {
    pub closed spec fn stage(&self)->StageProtocol {self.stages}
    pub closed spec fn selected(&self)->Option<RestoreTicket> {self.current}
    pub closed spec fn waiting(&self)->Seq<usize> {self.stages.inverse_view()}
    pub closed spec fn failed_spec(&self)->bool {self.failed}
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn next_attempt(&self)->u64 {self.next}
    pub open spec fn wf(&self)->bool {
        &&& self.stage().wf()
        &&& self.failed_spec() ==> self.selected().is_some()
        &&& self.selected().is_some() ==> self.stage().settled() && !self.stage().pending()
            && self.selected().unwrap().domain==self.domain_id() && self.selected().unwrap().attempt<self.next_attempt()
    }
    pub open spec fn same(&self,prior:&Self)->bool {
        self.domain_id()==prior.domain_id() && self.next_attempt()==prior.next_attempt()
            && self.selected()==prior.selected() && self.failed_spec()==prior.failed_spec()
            && self.stage().committed_view()==prior.stage().committed_view()
            && self.waiting()==prior.waiting() && self.stage().pending()==prior.stage().pending()
            && self.stage().settled()==prior.stage().settled() && self.stage().cancellation()==prior.stage().cancellation()
    }
    pub fn scope(domain:u64)->(out:Self)
        ensures out.wf(),out.domain_id()==domain,out.waiting()==Seq::<usize>::empty(),out.selected().is_none(),
            !out.failed_spec(),out.next_attempt()==0,out.stage().settled(),!out.stage().pending(),
    {Self {stages:StageProtocol::scope(),domain,next:0,current:None,failed:false}}
    pub fn iterator(domain:u64,committed:Vec<Binding>)->(out:Self)
        ensures out.wf(),out.domain_id()==domain,out.waiting()==Seq::<usize>::empty(),out.selected().is_none(),
            !out.failed_spec(),out.next_attempt()==0,out.stage().committed_view()==committed@,
            !out.stage().settled(),!out.stage().pending(),
    {Self {stages:StageProtocol::iterator(committed),domain,next:0,current:None,failed:false}}

    pub fn register(&mut self,token:usize)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).waiting()==old(self).waiting().push(token),
            final(self).selected()==old(self).selected(),final(self).failed_spec()==old(self).failed_spec(),
    {self.stages.register(token);}
    pub fn land(&mut self,token:usize)->(out:bool)
        requires old(self).wf(),
        ensures final(self).wf(),out==old(self).stage().pending(),
            final(self).selected()==old(self).selected(),final(self).failed_spec()==old(self).failed_spec(),
            out ==> final(self).waiting()==old(self).waiting().push(token),
            !out ==> final(self).same(old(self)),
    {self.stages.land(token)}
    pub fn admit(&mut self,target:Option<&[Binding]>)->(out:bool)
        requires old(self).wf(),ensures final(self).wf(),final(self).selected()==old(self).selected(),
            final(self).waiting()==old(self).waiting(),final(self).failed_spec()==old(self).failed_spec(),
    {self.stages.admit(target)}
    pub fn end(&mut self)->(out:bool)
        requires old(self).wf(),ensures final(self).wf(),final(self).selected()==old(self).selected(),
            final(self).waiting()==old(self).waiting(),final(self).failed_spec()==old(self).failed_spec(),
    {self.stages.end()}
    pub fn cancel(&mut self)
        requires old(self).wf(),ensures final(self).wf(),final(self).selected()==old(self).selected(),
            final(self).waiting()==old(self).waiting(),final(self).failed_spec()==old(self).failed_spec(),
    {self.stages.cancel();}
    pub fn is_pending(&self)->(out:bool)
        ensures out==self.stage().pending(),
    {self.stages.is_pending()}
    pub fn can_finish(&self,target:&[Binding])->(out:bool)
        requires self.wf(),
        ensures out ==> self.selected().is_none() && !self.failed_spec(),
    {self.current.is_none() && self.stages.can_finish(target)}
    pub fn is_empty(&self)->(out:bool)
        ensures out==(self.waiting().len()==0 && self.selected().is_none()),
    {self.current.is_none() && self.stages.is_empty()}
    pub fn has_failed(&self)->(out:bool)
        ensures out==self.failed_spec(),
    {self.failed}
    pub fn current(&self)->(out:Option<RestoreTicket>)
        ensures out==if self.failed_spec() {None} else {self.selected()},
    {if self.failed {None} else {self.current}}
    pub fn receipt(&self)->(out:Option<RestoreTicket>)
        ensures out==self.selected(),
    {self.current}
    pub fn can_retry(&self)->(out:bool)
        requires self.wf(),
        ensures out==(self.failed_spec() && self.next_attempt()<u64::MAX),
    {self.failed && self.next<u64::MAX}

    /// Selecting work moves exactly the real StageProtocol's last token into
    /// the retained receipt. An occupied receipt blocks any second selection.
    pub fn begin_restore(&mut self)->(out:Result<Option<RestoreTicket>,RestoreError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).domain_id()==old(self).domain_id(),
            out.is_ok() && out.unwrap().is_some() ==> old(self).selected().is_none()
                && old(self).stage().settled() && !old(self).stage().pending()
                && old(self).waiting().len()>0
                && out.unwrap().unwrap()==(RestoreTicket {domain:old(self).domain_id(),attempt:old(self).next_attempt(),token:old(self).waiting().last()})
                && final(self).selected()==out.unwrap() && !final(self).failed_spec()
                && final(self).waiting()==old(self).waiting().drop_last()
                && final(self).next_attempt()==old(self).next_attempt()+1,
            out.is_err() || out.unwrap().is_none() ==> final(self).same(old(self)),
            out.is_err() ==> old(self).next_attempt()==u64::MAX,
            old(self).selected().is_none() && old(self).stage().settled()
                && old(self).waiting().len()>0 && old(self).next_attempt()<u64::MAX
                ==> out.is_ok() && out.unwrap().is_some(),
    {
        if self.current.is_some() || !self.stages.is_settled() || self.stages.is_empty() {return Ok(None);}
        if self.next==u64::MAX {return Err(RestoreError::Capacity);}
        let token=self.stages.pop().unwrap();
        let ticket=RestoreTicket {domain:self.domain,attempt:self.next,token};
        self.next+=1;self.current=Some(ticket);
        Ok(Some(ticket))
    }

    /// A matching live receipt is consumed once. Failed retains the exact
    /// selected token and blocks it until retry; no report mutates waiting work.
    pub fn complete(&mut self,ticket:RestoreTicket,outcome:RestoreOutcome)->(accepted:bool)
        requires old(self).wf(),
        ensures final(self).wf(),accepted==(old(self).selected()==Some(ticket) && !old(self).failed_spec()),
            final(self).waiting()==old(self).waiting(),final(self).next_attempt()==old(self).next_attempt(),
            final(self).domain_id()==old(self).domain_id(),
            !accepted ==> final(self).same(old(self)),
            accepted && outcome==RestoreOutcome::Failed ==> final(self).selected()==Some(ticket) && final(self).failed_spec(),
            accepted && outcome!=RestoreOutcome::Failed ==> final(self).selected().is_none() && !final(self).failed_spec(),
    {
        if self.current!=Some(ticket) || self.failed {return false;}
        if outcome==RestoreOutcome::Failed {self.failed=true;}
        else {self.current=None;}
        true
    }

    /// Retry retains the selected payload and the entire waiting stack. Its
    /// fresh identity rejects any late completion from the previous attempt.
    pub fn retry(&mut self)->(out:Result<RestoreTicket,RestoreError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_ok()==(old(self).failed_spec() && old(self).next_attempt()<u64::MAX),
            final(self).waiting()==old(self).waiting(),final(self).domain_id()==old(self).domain_id(),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> final(self).selected()==Some(out.unwrap()) && !final(self).failed_spec()
                && out.unwrap().domain==old(self).domain_id()
                && out.unwrap().token==old(self).selected().unwrap().token
                && out.unwrap().attempt==old(self).next_attempt()
                && out.unwrap().attempt>old(self).selected().unwrap().attempt
                && final(self).next_attempt()==old(self).next_attempt()+1,
    {
        if !self.failed {return Err(RestoreError::InvalidState);}
        if self.next==u64::MAX {return Err(RestoreError::Capacity);}
        let ticket=RestoreTicket {domain:self.domain,attempt:self.next,token:self.current.unwrap().token};
        self.next+=1;self.current=Some(ticket);self.failed=false;
        Ok(ticket)
    }
}
}
