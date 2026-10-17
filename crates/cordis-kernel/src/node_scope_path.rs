//! Immutable callback ancestry captured once by the actual Node owner.
//! A query consumes this private path, not a caller-rebuilt list. Paths belong
//! to their callback contexts; the ledger still retains only live callbacks.
use super::*;
use crate::invocation_ledger::{ScopeBlock, ScopeError, ScopeHandle};
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
/// No mutable path/handle-list access is exported. Completed scopes remain in
/// an escaped callback's path without keeping a live ledger record allocated.
pub struct Path {handles:Vec<ScopeHandle>}
impl Path {
    pub closed spec fn chain(&self)->Seq<ScopeHandle> {self.handles@}
    pub open spec fn wf(&self)->bool {
        self.chain().len()>0 && forall|i:int|0<=i<self.chain().len() ==>
            self.chain()[i].domain==self.chain().last().domain && self.chain()[i].scope>0
    }
    pub fn own(&self)->(out:ScopeHandle)
        requires self.wf(),ensures out==self.chain().last(),
    {self.handles[self.handles.len()-1]}
}
pub open spec fn ancestors(parent:Option<&Path>)->Seq<ScopeHandle> {
    match parent {Some(path)=>path.chain(),None=>Seq::empty()}
}
pub open spec fn extends(a:History,b:History)->bool {
    a.events.len()<=b.events.len() && b.events.take(a.events.len() as int)==a.events
        && a.states.len()<=b.states.len() && b.states.take(a.states.len() as int)==a.states
}
proof fn appended(a:History,state:Observation,event:Event)
    ensures extends(a,a.append(state,event)),
{
    assert(a.append(state,event).events.take(a.events.len() as int) =~= a.events);
    assert(a.append(state,event).states.take(a.states.len() as int) =~= a.states);
}
proof fn transitive(a:History,b:History,c:History)
    requires extends(a,b),extends(b,c),ensures extends(a,c),
{
    assert(c.events.take(a.events.len() as int) =~= a.events);
    assert(c.states.take(a.states.len() as int) =~= a.states);
}
proof fn recorded_scope(before:NodeRuntime,after:NodeRuntime,event:Event)
    requires before.wf(),after.wf(),after.history()==before.history().append(after.observation(),event),
    ensures scopes::step(before.observation(),after.observation(),event),
{
    let index=before.history().events.len() as int;
    assert(after.history().events[index]==event);
    assert(after.history().states[index]==before.observation());
    assert(history::step(before.observation(),after.observation(),event));reveal(history::operation);
}
impl NodeRuntime {
    /// The selected parent's complete captured path is copied before issuing
    /// the new callback. Every subsequent check uses exactly this owned path.
    pub fn begin_invocation(&mut self,id:usize,generation:u64,parent:Option<&Path>)->(out:Result<Path,ScopeError>)
        requires old(self).wf(),parent.is_some() ==> parent.unwrap().wf(),
        ensures final(self).wf(),extends(old(self).history(),final(self).history()),
            out.is_ok() ==> out->Ok_0.wf()
                && out->Ok_0.chain()==ancestors(parent).push(out->Ok_0.chain().last())
                && final(self).history().events.last()==(Event::BeginScope {id,generation,out:Ok(out->Ok_0.chain().last())})
                && final(self).history().events.len()==old(self).history().events.len()+if parent.is_some() {2nat} else {1nat}
                && (forall|i:int|0<=i<out->Ok_0.chain().len() ==> final(self).observation().scopes.known(out->Ok_0.chain()[i]))
                && final(self).observation().scopes.live(out->Ok_0.chain().last())
                && (parent.is_some() ==> final(self).history().events[old(self).history().events.len() as int] is ScopesLive
                    && final(self).history().events[old(self).history().events.len() as int]->ScopesLive_handles==ancestors(parent)),
    {
        let ghost initial=self.history();let mut handles=Vec::new();
        if let Some(parent)=parent {
            if parent.handles.len()==usize::MAX {return Err(ScopeError::Capacity);}
            let ghost prior=*self;let checked=self.scopes_live(parent.handles.as_slice());
            proof {
                recorded_scope(prior,*self,Event::ScopesLive {handles:parent.chain(),out:checked});reveal(scopes::live_result);
                appended(initial,self.observation(),Event::ScopesLive {handles:parent.chain(),out:checked});
            }
            checked?;
            let ghost checked_history=self.history();let mut i=0;
            while i<parent.handles.len()
                invariant self.wf(),self.history()==checked_history,extends(initial,self.history()),handles@==parent.chain().take(i as int),i<=parent.handles.len(),parent.handles.len()<usize::MAX,
                    forall|j:int|0<=j<parent.chain().len() ==> self.observation().scopes.known(parent.chain()[j]),
                    checked_history.events==initial.events.push(Event::ScopesLive {handles:parent.chain(),out:checked}),
                decreases parent.handles.len()-i,
            {handles.push(parent.handles[i]);i+=1;}
        }
        proof {assert(handles@==ancestors(parent));}
        let ghost prior=*self;let ghost before=self.observation();let ghost prefix=handles@;
        proof {before.scopes.allocation_facts();}
        let issued=self.begin_scope(id,generation);
        proof {
            recorded_scope(prior,*self,Event::BeginScope {id,generation,out:issued});
            appended(prior.history(),self.observation(),Event::BeginScope {id,generation,out:issued});
            transitive(initial,prior.history(),self.history());
        }
        match issued {
            Err(error)=>Err(error),
            Ok(handle)=>{
                handles.push(handle);
                proof {
                    assert forall|i:int|0<=i<handles.len() implies self.observation().scopes.known(handles@[i]) by {
                        if i<prefix.len() {assert(before.scopes.known(prefix[i]));}
                    }
                }
                let path=Path {handles};
                proof {
                    assert(path.wf());
                    assert(path.chain()==ancestors(parent).push(handle));
                    let issued=scopes::record(handle.domain,handle.scope,id,generation);
                    assert(self.observation().scopes.records().last()==issued);
                    assert(self.observation().scopes.owns(handle,issued));
                    assert(self.observation().scopes.live(handle));
                    assert(self.history().events.len()==initial.events.len()+if parent.is_some() {2nat} else {1nat});
                    assert(parent.is_some() ==> self.history().events[initial.events.len() as int] is ScopesLive
                        && self.history().events[initial.events.len() as int]->ScopesLive_handles==ancestors(parent));
                }
                Ok(path)
            },
        }
    }
    pub fn finish_invocation(&mut self,path:&Path)->(out:Result<(),ScopeError>)
        requires old(self).wf(),path.wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::FinishScope {handle:path.chain().last(),out}),
    {self.finish_scope(path.own())}
    /// Query all captured ancestors, including a live ancestor of an already
    /// completed nested callback. No caller-selected subset can enter here.
    pub fn invocation_live(&mut self,path:&Path)->(out:Result<bool,ScopeError>)
        requires old(self).wf(),path.wf(),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),
            final(self).history()==old(self).history().append(final(self).observation(),Event::ScopesLive {handles:path.chain(),out}),
            scopes::live_result(old(self).observation().scopes,path.chain(),out),
    {
        let ghost prior=*self;let out=self.scopes_live(path.handles.as_slice());
        proof {recorded_scope(prior,*self,Event::ScopesLive {handles:path.chain(),out});}
        out
    }
    pub fn invocation_own_live(&mut self,path:&Path)->(out:Result<bool,ScopeError>)
        requires old(self).wf(),path.wf(),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),
            final(self).history()==old(self).history().append(final(self).observation(),Event::ScopesLive {handles:seq![path.chain().last()],out}),
            out.is_ok() ==> out->Ok_0==old(self).observation().scopes.live(path.chain().last()),
    {
        let ghost prior=*self;let own=vec![path.own()];
        proof {assert(own@ =~= seq![path.chain().last()]);}
        let out=self.scopes_live(own.as_slice());
        proof {recorded_scope(prior,*self,Event::ScopesLive {handles:own@,out});reveal(scopes::live_result);}
        out
    }
    pub fn check_invocation_wait(&mut self,path:&Path,target:usize)->(out:Result<Option<ScopeBlock>,ScopeError>)
        requires old(self).wf(),path.wf(),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),
            final(self).history()==old(self).history().append(final(self).observation(),Event::ScopeWait {handles:path.chain(),target,out}),
            (out==Ok(None))==(forall|i:int|0<=i<path.chain().len() ==> old(self).observation().scopes.safe(&old(self).observation().control.control(),path.chain()[i],target)),
            out.is_ok() && out->Ok_0.is_some() ==> path.chain().contains(out->Ok_0.unwrap().scope)
                && old(self).observation().scopes.blocked(&old(self).observation().control.control(),out->Ok_0.unwrap(),target),
    {
        let ghost prior=*self;let out=self.check_scope_wait(path.handles.as_slice(),target);
        proof {recorded_scope(prior,*self,Event::ScopeWait {handles:path.chain(),target,out});reveal(scopes::wait_result);}
        out
    }
}
impl History {
    /// Even a completed callback in an escaped path has a real issuance. No
    /// completed-record cache or caller-supplied origin witness is necessary.
    pub proof fn known_scope_origin(&self,end:int,handle:ScopeHandle)->(out:(int,crate::request_ledger::RequestTicket))
        requires self.valid(),0<=end<self.states.len(),self.states[end].scopes.known(handle),
        ensures 0<=out.0<end,self.scope_issued_at(out.0,out.1),out.1.domain==handle.domain,out.1.request==handle.scope,
        decreases end,
    {
        assert(end>0);let i=end-1;let a=self.states[i];let b=self.states[end];
        assert(history::step(self.states[i],self.states[i+1],self.events[i]));reveal(history::operation);
        match self.events[i] {
            Event::BeginScope {id,generation,out} if out==Ok(handle)=>{
                let ticket=scopes::record(handle.domain,handle.scope,id,generation);
                assert(self.scope_issued_at(i,ticket));(i,ticket)
            },
            _=>{
                if b.scopes.unchanged(&a.scopes) {b.scopes.unchanged_observations(&a.scopes);}
                assert(a.scopes.known(handle));self.known_scope_origin(i,handle)
            },
        }
    }
}

}
