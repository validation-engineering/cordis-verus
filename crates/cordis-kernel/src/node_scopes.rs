//! Actual callback receipts and wait decisions in the same Node execution history.
//! Raw scope-list callers supply their own ancestry. The production binding
//! uses `paths::Path` to preserve the complete selected native parent path.
//! Neither interface proves JavaScript parent selection or callback termination.
use super::*;
#[cfg(verus_keep_ghost)]
use crate::request_ledger::RequestTicket;

verus! {
pub open spec fn record(domain:u64,scope:u64,id:usize,generation:u64)->RequestTicket {
    RequestTicket {domain,id,generation,session:0,job:0,request:scope,restoring:false}
}
#[verifier::opaque]
pub open spec fn live_result(scopes:InvocationLedger,handles:Seq<ScopeHandle>,out:Result<bool,ScopeError>)->bool {
    out.is_ok()==(forall|i:int|0<=i<handles.len() ==> scopes.known(handles[i]))
        && (out.is_ok() ==> out->Ok_0==(exists|i:int|0<=i<handles.len() && scopes.live(handles[i])))
}
#[verifier::opaque]
pub open spec fn wait_result(scopes:InvocationLedger,kernel:crate::Kernel,handles:Seq<ScopeHandle>,target:usize,out:Result<Option<ScopeBlock>,ScopeError>)->bool {
    (out==Ok(None))==(forall|i:int|0<=i<handles.len() ==> scopes.safe(&kernel,handles[i],target))
        && (out.is_ok() && out->Ok_0.is_some() ==> handles.contains(out->Ok_0.unwrap().scope) && scopes.blocked(&kernel,out->Ok_0.unwrap(),target))
}
pub open spec fn step(a:Observation,b:Observation,event:Event)->bool {
    b.scopes.domain_id()==a.scopes.domain_id() && match event {
        Event::BeginScope {id,generation,out}=>
            out.is_ok()==(a.control.control().generation_of(id)==Some(generation)
                && a.scopes.next_id()<u64::MAX && a.scopes.records().len()<usize::MAX)
            && (out.is_err() ==> b.scopes.unchanged(&a.scopes))
            && (out.is_ok() ==> out->Ok_0==(ScopeHandle {domain:a.scopes.domain_id(),scope:a.scopes.next_id()})
                && b.scopes.next_id()==a.scopes.next_id()+1
                && b.scopes.records()==a.scopes.records().push(record(a.scopes.domain_id(),a.scopes.next_id(),id,generation))),
        Event::FinishScope {handle,out}=>b.scopes.next_id()==a.scopes.next_id() && out.is_ok()==a.scopes.live(handle)
            && (out.is_err() ==> b.scopes.unchanged(&a.scopes))
            && (out.is_ok() ==> !b.scopes.live(handle) && b.scopes.records().len()+1==a.scopes.records().len()
                && (forall|r:RequestTicket|b.scopes.records().contains(r)==(a.scopes.records().contains(r) && r.request!=handle.scope))),
        Event::ScopesLive {handles,out}=>b.scopes.unchanged(&a.scopes) && live_result(a.scopes,handles,out),
        Event::ScopeWait {handles,target,out}=>b.scopes.unchanged(&a.scopes) && wait_result(a.scopes,a.control.control(),handles,target,out),
        _=>b.scopes.unchanged(&a.scopes),
    }
}
impl NodeRuntime {
    pub fn invocation_count(&self)->(out:usize) ensures out==self.observation().scopes.records().len(),
    {self.scopes.live_count()}
    pub fn begin_scope(&mut self,id:usize,generation:u64)->(out:Result<ScopeHandle,ScopeError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::BeginScope {id,generation,out}),
    {
        let ghost before=self.observation();
        let out=self.scopes.begin(self.control.kernel(),id,generation);
        proof {self.scopes.unchanged_reflexive();reveal(history::operation);self.record(before,Event::BeginScope {id,generation,out});}
        out
    }
    pub fn finish_scope(&mut self,handle:ScopeHandle)->(out:Result<(),ScopeError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::FinishScope {handle,out}),
    {
        let ghost before=self.observation();
        let out=self.scopes.finish(handle);
        proof {self.scopes.unchanged_reflexive();reveal(history::operation);self.record(before,Event::FinishScope {handle,out});}
        out
    }
    pub fn scopes_live(&mut self,handles:&[ScopeHandle])->(out:Result<bool,ScopeError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),
            final(self).history()==old(self).history().append(final(self).observation(),Event::ScopesLive {handles:handles@,out}),
    {
        let ghost before=self.observation();let out=self.scopes.any_live(handles);
        proof {
            self.scopes.unchanged_reflexive();reveal(live_result);
            assert(live_result(before.scopes,handles@,out));
            reveal(history::operation);self.record(before,Event::ScopesLive {handles:handles@,out});
        }
        out
    }
    pub fn check_scope_wait(&mut self,handles:&[ScopeHandle],target:usize)->(out:Result<Option<ScopeBlock>,ScopeError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),
            final(self).history()==old(self).history().append(final(self).observation(),Event::ScopeWait {handles:handles@,target,out}),
    {
        let ghost before=self.observation();let out=self.scopes.check_wait(self.control.kernel(),handles,target);
        proof {
            self.scopes.unchanged_reflexive();reveal(wait_result);
            assert(wait_result(before.scopes,before.control.control(),handles@,target,out));
            reveal(history::operation);self.record(before,Event::ScopeWait {handles:handles@,target,out});
        }
        out
    }
}
impl History {
    pub open spec fn scope_issued_at(&self,index:int,r:RequestTicket)->bool {
        0<=index<self.events.len()
            && self.events[index]==(Event::BeginScope {id:r.id,generation:r.generation,out:Ok(ScopeHandle {domain:r.domain,scope:r.request})})
            && self.states[index].control.control().generation_of(r.id)==Some(r.generation)
            && r==record(self.states[index].scopes.domain_id(),self.states[index].scopes.next_id(),r.id,r.generation)
    }
    /// A live receipt originates in this owner's actual issuance history and
    /// current control generation, including preparation and cleanup callbacks.
    pub proof fn scope_origin(&self,end:int,r:RequestTicket)
        requires self.valid(),0<=end<self.states.len(),self.states[end].scopes.records().contains(r),
        ensures exists|issued:int|0<=issued<end && self.scope_issued_at(issued,r),
        decreases end,
    {
        assert(end>0);let i=end-1;
        assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
        let a=self.states[i];let b=self.states[i+1];
        match self.events[i] {
            Event::BeginScope {id,generation,out} if out.is_ok() && r==record(a.scopes.domain_id(),a.scopes.next_id(),id,generation)=>{
                assert(self.scope_issued_at(i,r));
            },
            _=>{
                if b.scopes.unchanged(&a.scopes) {b.scopes.unchanged_observations(&a.scopes);}
                assert(a.scopes.records().contains(r));self.scope_origin(i,r);
            },
        }
    }
    /// Cleanup/retry/release do not consume a callback receipt. Only its exact
    /// finish handle can remove it, even if the lifecycle moves meanwhile.
    pub proof fn scope_retained(&self,start:int,end:int,r:RequestTicket)
        requires self.valid(),0<=start<=end<self.states.len(),self.states[start].scopes.records().contains(r),
            forall|i:int|start<=i<end ==> !(self.events[i] is FinishScope
                && self.events[i]->FinishScope_out.is_ok() && self.events[i]->FinishScope_handle.scope==r.request),
        ensures self.states[end].scopes.records().contains(r),
        decreases end-start,
    {
        if start<end {
            self.scope_retained(start,end-1,r);let i=end-1;
            assert(!(self.events[i] is FinishScope && self.events[i]->FinishScope_out.is_ok() && self.events[i]->FinishScope_handle.scope==r.request));
            assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
            let a=self.states[i];let b=self.states[i+1];
            match self.events[i] {
                Event::BeginScope {out,..} if out.is_ok()=>{
                    let j=choose|j:int|0<=j<a.scopes.records().len() && a.scopes.records()[j]==r;
                    assert(b.scopes.records()[j]==r);assert(b.scopes.records().contains(r));
                },
                Event::FinishScope {handle,out} if out.is_ok()=>{
                    assert(r.request!=handle.scope);
                    assert(b.scopes.records().contains(r)==(a.scopes.records().contains(r) && r.request!=handle.scope));
                },
                _=>{b.scopes.unchanged_observations(&a.scopes);},
            }
        }
    }
    /// A reported blocker uses a real earlier callback receipt and the current
    /// committed dependency/ownership graph, never caller-supplied owner bits.
    pub proof fn scope_block_has_origin(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is ScopeWait,
            self.events[index]->ScopeWait_out.is_ok(),self.events[index]->ScopeWait_out->Ok_0.is_some(),
        ensures {
            let block=self.events[index]->ScopeWait_out->Ok_0.unwrap();let target=self.events[index]->ScopeWait_target;
            &&& exists|r:RequestTicket,issued:int|0<=issued<index && self.scope_issued_at(issued,r)
                && self.states[index].scopes.owns(block.scope,r) && r.id==block.id && r.generation==block.generation
            &&& self.states[index].control.control().generation_of(block.id)==Some(block.generation)
            &&& self.states[index].control.control().committed_reachable(block.id,block.retained)
            &&& self.states[index].control.control().owned_by(block.retained,target)
        },
    {
        assert(history::step(self.states[index],self.states[index+1],self.events[index]));reveal(history::operation);
        let block=self.events[index]->ScopeWait_out->Ok_0.unwrap();let a=self.states[index];reveal(wait_result);
        let r=choose|r:RequestTicket|a.scopes.owns(block.scope,r) && r.id==block.id && r.generation==block.generation
            && a.control.control().generation_of(r.id)==Some(r.generation)
            && a.control.control().committed_reachable(r.id,block.retained) && a.control.control().owned_by(block.retained,self.events[index]->ScopeWait_target);
        self.scope_origin(index,r);
    }
}
impl History {
    /// Once consumed, a scope stays inactive through later callbacks, failures,
    /// retries and new generations. Numeric identities are never reused.
    pub proof fn finished_scope_stays_inactive(&self,start:int,end:int,handle:ScopeHandle)
        requires self.valid(),0<=start<=end<self.states.len(),self.states[start].scopes.known(handle),!self.states[start].scopes.live(handle),
        ensures self.states[end].scopes.known(handle),!self.states[end].scopes.live(handle),
        decreases end-start,
    {
        if start<end {
            self.finished_scope_stays_inactive(start,end-1,handle);let i=end-1;
            assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
            let a=self.states[i];let b=self.states[i+1];
            if b.scopes.unchanged(&a.scopes) {b.scopes.unchanged_observations(&a.scopes);}
            assert(b.scopes.known(handle));
            if b.scopes.live(handle) {
                let r=choose|r:RequestTicket|b.scopes.owns(handle,r);
                match self.events[i] {
                    Event::BeginScope {out,id,generation} if out.is_ok()=>{
                        assert(r!=record(a.scopes.domain_id(),a.scopes.next_id(),id,generation));
                        assert(a.scopes.records().contains(r));
                    },
                    _=>{assert(a.scopes.records().contains(r));},
                }
                assert(a.scopes.owns(handle,r));assert(a.scopes.live(handle));
            }
        }
    }
}

}
