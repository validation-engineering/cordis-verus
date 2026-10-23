//! Strict value recovery by the real mixed cleanup dispatcher.
//! Observations come from the guarded scalar commit or the locked typed read;
//! no expected heap or successful inverse is supplied by the host.
use super::Dispatch;
#[cfg(verus_keep_ghost)]
use super::{Action, Cleanup};
#[cfg(verus_keep_ghost)]
use crate::{
    cleanup_queue::completion::CleanupDispatch,
    lifecycle_state::registration::shared_child::ChildCleanup,
    reversible_value::{joint, managed::semantics::Value, service_composition::Address},
};
use vstd::prelude::*;

verus! {
pub open spec fn address<C,R,H,T:?Sized,X>(action:Action<C,R,H,T,X>)->Address {
    match action {
        ChildCleanup::Value(inverse)=>Address {journal:inverse.target().journal_spec(),key:inverse.target().object().key},
        ChildCleanup::Callback(Cleanup::Payload {inverse,..})=>Address {journal:inverse.owner().journal_spec(),key:inverse.owner().key()},
        _=>arbitrary(),
    }
}
pub open spec fn expected<C,R,H,T:?Sized,X>(action:Action<C,R,H,T,X>)->Value<T> {
    match action {
        ChildCleanup::Value(inverse)=>Value::Scalar(inverse.state().after),
        ChildCleanup::Callback(Cleanup::Payload {inverse,..})=>Value::Payload(inverse.after().state()),
        _=>arbitrary(),
    }
}
pub open spec fn original<C,R,H,T:?Sized,X>(action:Action<C,R,H,T,X>)->Value<T> {
    match action {
        ChildCleanup::Value(inverse)=>Value::Scalar(inverse.state().before),
        ChildCleanup::Callback(Cleanup::Payload {inverse,..})=>Value::Payload(inverse.before().state()),
        _=>arbitrary(),
    }
}
pub open spec fn managed<C,R,H,T:?Sized,X>(action:Action<C,R,H,T,X>)->bool {
    match action {ChildCleanup::Value(_)=>true,ChildCleanup::Callback(Cleanup::Payload {..})=>true,_=>false}
}
pub open spec fn undo<C,R,H,T:?Sized,X>(action:Action<C,R,H,T,X>,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>> {
    if managed(action) && heap.contains_key(address(action)) && heap[address(action)]==expected(action) {
        Some(heap.insert(address(action),original(action)))
    } else {None}
}
/// Completed slots remain in the actual Vec as None. They are not fabricated
/// inverses and must be skipped when interpreting the remaining obligation.
pub open spec fn pending<C,R,H,T:?Sized,X>(slots:Seq<Option<Action<C,R,H,T,X>>>,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>>
    decreases slots.len(),
{
    if slots.len()==0 {Some(heap)} else {match slots.last() {
        None=>pending(slots.drop_last(),heap),
        Some(action)=>match undo(action,heap) {None=>None,Some(previous)=>pending(slots.drop_last(),previous)},
    }}
}
pub open spec fn top<I>(slots:Seq<Option<I>>,token:usize)->bool {
    token<slots.len() && slots[token as int].is_some()
        && forall|i:int|token<i<slots.len() ==> (#[trigger] slots[i]).is_none()
}
impl<C,R,H,T:?Sized,X> Dispatch<C,R,H,T,X> {
    pub open spec fn boundaries(&self)->Option<(crate::cleanup_queue::CleanupQueue<Action<C,R,H,T,X>>,crate::cleanup_queue::CleanupQueue<Action<C,R,H,T,X>>)> {
        match self {Self::Payload(c)=>c.boundaries(),Self::Other(CleanupDispatch::Value {completion,..})=>completion.boundaries(),_=>None}
    }
    pub open spec fn queue_link(&self)->Option<(joint::Journal,nat)> {
        match self {Self::Payload(c)=>c.evidence().queue(),Self::Other(CleanupDispatch::Value {completion,..})=>completion.evidence().queue(),_=>None}
    }
    pub open spec fn issue(&self)->Option<joint::Receipt> {
        match self {Self::Payload(c)=>c.evidence().issue(),Self::Other(CleanupDispatch::Value {completion,..})=>completion.evidence().issue(),_=>None}
    }
    pub open spec fn follows_boundary(&self,cause:Option<joint::Receipt>)->bool {
        cause.is_some() && self.queue_link().is_some() && cause.unwrap().journal()==self.queue_link().unwrap().0 ==> {
            &&& self.acknowledgement().is_some() && self.acknowledgement().unwrap().follows(&cause.unwrap())
            &&& self.checkpoint().journal()==cause.unwrap().journal() ==>
                self.checkpoint().covers(&cause.unwrap()) && cause.unwrap().events().len()<=self.read_cut()
        }
    }
    /// The real Pop commit follows the supplied boundary. Both restorers
    /// already follow that issue, including failed attempts and typed reads.
    pub(crate) proof fn establish_boundary(&self,cause:Option<joint::Receipt>)
        requires self.authentic(),self.managed(),cause.is_some() ==> cause.unwrap().wf(),
            cause.is_some() && self.queue_link().is_some() && cause.unwrap().journal()==self.queue_link().unwrap().0 ==>
                self.issue().is_some() && self.issue().unwrap().follows(&cause.unwrap()),
        ensures self.follows_boundary(cause),
    {
        hide(joint::valid);hide(joint::step);
        if cause.is_some() && self.queue_link().is_some() && cause.unwrap().journal()==self.queue_link().unwrap().0 {
            self.acknowledgement_records();
            let prior=cause.unwrap();let issue=self.issue().unwrap();
            match self {
                Self::Payload(c)=>{
                    reveal(crate::reversible_value::payload::restoration::attempt::protocol::Evidence::certified);
                    let attempt=c.evidence().attempt();attempt.facts();attempt.boundaries();
                    if self.checkpoint().journal()==prior.journal() {
                        attempt.read().checkpoint().cover_through(&issue,&prior);
                        attempt.endpoint().cover_through(&attempt.read().checkpoint(),&prior);
                    }
                },
                Self::Other(CleanupDispatch::Value {..})=>{
                    if self.checkpoint().journal()==prior.journal() {self.checkpoint().after_cover(&issue,&prior);}
                },_=>{},
            }
            self.acknowledgement().unwrap().after_cover(&issue,&prior);
        }
    }
    pub open spec fn acknowledgement(&self)->Option<joint::Receipt> {
        match self {Self::Payload(c)=>c.evidence().acknowledgement(),Self::Other(CleanupDispatch::Value {completion,..})=>completion.evidence().acknowledgement(),_=>None}
    }
    pub proof fn acknowledgement_receipt(tracked &self)->(tracked out:Option<joint::Receipt>)
        requires self.authentic(),self.managed(),self.queue_link().is_some(),
        ensures out.is_some(),out.unwrap().wf(),out.unwrap().same(&self.acknowledgement().unwrap()),
    {
        self.acknowledgement_records();
        match self {
            Self::Payload(c)=>{let tracked evidence=c.trace.borrow();evidence.representation();match &evidence.acknowledgement {Some(r)=>Some(r.duplicate()),None=>None}},
            Self::Other(CleanupDispatch::Value {completion,..})=>{let tracked evidence=completion.trace.borrow();evidence.representation();match &evidence.acknowledgement {Some(r)=>Some(r.duplicate()),None=>None}},
            _=>None,
        }
    }
    pub proof fn selected_kind(&self,slots:Seq<Option<Action<C,R,H,T,X>>>)
        requires self.from_slot(slots),
        ensures self.ticket().token<slots.len(),slots[self.ticket().token as int].is_some(),
            managed(slots[self.ticket().token as int].unwrap())==self.managed(),
    {match self {Self::Other(d)=>{match d {CleanupDispatch::Host {action,..}=>{match action {ChildCleanup::Callback(c)=>{match c {Cleanup::Payload {..}=>{},_=>{}}},_=>{}}},_=>{}}},_=>{}}}
    /// Actual managed acknowledgements encode Succeeded or retained Failed.
    /// They cannot be confused with a host callback's nonretryable Drained.
    pub proof fn acknowledgement_records(&self)
        requires self.authentic(),self.managed(),self.queue_link().is_some(),
        ensures self.acknowledgement().is_some(),self.acknowledgement().unwrap().wf(),
            self.acknowledgement().unwrap().journal()==self.queue_link().unwrap().0,
            self.acknowledgement().unwrap().event().key==self.queue_link().unwrap().1,
            self.acknowledgement().unwrap().event().change==(joint::Change::Cleanup {event:joint::episode::CleanupChange::Complete {
                ticket:self.ticket(),outcome:if self.succeeded() {crate::cleanup_journal::RestoreOutcome::Succeeded} else {crate::cleanup_journal::RestoreOutcome::Failed},retained:!self.succeeded()}}),
    {
        match self {
            Self::Payload(c)=>{reveal(crate::reversible_value::payload::restoration::attempt::protocol::Evidence::certified);},
            Self::Other(CleanupDispatch::Value {..})=>{},_=>{},
        }
    }
    pub proof fn consuming_acknowledgement(&self)
        requires self.authentic(),self.managed(),self.queue_link().is_some(),self.succeeded(),
        ensures self.acknowledgement().unwrap().event().after is Cleanup,
            self.ticket().token<self.acknowledgement().unwrap().event().after->Cleanup_state.occupied.len(),
            joint::episode::release::completes(self.acknowledgement().unwrap().event(),self.queue_link().unwrap().1,self.ticket().token),
    {
        self.acknowledgement_records();self.after_queue().trace_record();
    }
    pub open spec fn before_queue(&self)->crate::cleanup_queue::CleanupQueue<Action<C,R,H,T,X>> {self.boundaries().unwrap().0}
    pub open spec fn after_queue(&self)->crate::cleanup_queue::CleanupQueue<Action<C,R,H,T,X>> {self.boundaries().unwrap().1}
    pub open spec fn authentic(&self)->bool {
        self.managed() ==> self.boundaries().is_some() && self.finished(self.before_queue(),self.after_queue())
    }
    /// The production entry point exports both scalar and typed transitions.
    pub open spec fn finished(&self,before:crate::cleanup_queue::CleanupQueue<Action<C,R,H,T,X>>,after:crate::cleanup_queue::CleanupQueue<Action<C,R,H,T,X>>)->bool {
        &&& before.wf() && after.wf() && before.link()==after.link() && before.protocol().domain_id()==after.protocol().domain_id()
        &&& !self.managed() ==> after.slots()==before.slots().update(self.ticket().token as int,None)
            && after.issued() && after.protocol().selected()==Some(self.ticket())
        &&& self.from_slot(before.slots()) && self.selected_from(before.protocol().selected(),before.protocol().waiting())
        &&& self.recovery(before.slots())
        &&& self.managed() ==> {
            &&& self.boundaries()==Some((before,after))
            &&& self.queue_link()==before.link()
            &&& before.link().is_some() ==> self.acknowledgement().is_some() && self.acknowledgement().unwrap().events()==after.trace()
            &&& after.slots()==before.slots().update(self.ticket().token as int,if self.succeeded() {None} else {before.slots()[self.ticket().token as int]})
            &&& !after.issued() && after.protocol().failed_spec()==!self.succeeded()
            &&& after.protocol().selected()==if self.succeeded() {None} else {Some(self.ticket())}
            &&& after.protocol().waiting()==if before.protocol().selected().is_some() {before.protocol().waiting()} else {before.protocol().waiting().drop_last()}
        }
    }
    pub open spec fn managed(&self)->bool {match self {Self::Payload(_)=>true,Self::Other(CleanupDispatch::Value {..})=>true,_=>false}}
    pub open spec fn succeeded(&self)->bool {match self {Self::Payload(c)=>c.restored.is_some(),Self::Other(CleanupDispatch::Value {completion,..})=>completion.restored.is_some(),_=>false}}
    pub open spec fn observed(&self)->Option<Value<T>> {
        match self {
            Self::Payload(c)=>match c.evidence().attempt().read().value() {Some(v)=>Some(Value::Payload(v.state())),None=>None},
            Self::Other(CleanupDispatch::Value {completion,..})=>Some(Value::Scalar(completion.evidence().attempt().event().change->Value_event.before())),
            _=>None,
        }
    }
    pub open spec fn landed(&self)->Option<Value<T>> {
        match self {
            Self::Payload(c)=>match c.restored {Some(v)=>Some(Value::Payload(v.after().state())),None=>self.observed()},
            Self::Other(CleanupDispatch::Value {completion,..})=>Some(Value::Scalar(completion.evidence().attempt().event().change->Value_event.after())),
            _=>None,
        }
    }
    pub open spec fn checkpoint(&self)->joint::Receipt {
        match self {Self::Payload(c)=>c.evidence().attempt().endpoint(),Self::Other(CleanupDispatch::Value {completion,..})=>completion.evidence().attempt(),_=>arbitrary()}
    }
    pub open spec fn read_cut(&self)->nat {
        match self {Self::Payload(c)=>c.evidence().attempt().read().checkpoint().events().len(),Self::Other(CleanupDispatch::Value {completion,..})=>completion.evidence().attempt().at(),_=>0}
    }
    /// The scalar record carries its value; typed decoding uses this actual
    /// attempt's authenticated source history at the recorded revision.
    pub open spec fn carrier(&self)->crate::reversible_value::managed::interleaving::sources::Carrier<T> {
        use crate::reversible_value::managed::interleaving::sources::Carrier;
        match self {Self::Payload(c)=>Carrier::Payload {source:c.evidence().attempt().inverse().owner().source(),states:c.evidence().attempt().states()},_=>Carrier::Scalar}
    }
    pub proof fn payload_history_witness(tracked &self)->(tracked out:Option<crate::reversible_value::history::Witness<crate::reversible_value::payload::State<T>>>)
        requires self.authentic(),self.managed(),
        ensures match self.carrier() {
            crate::reversible_value::managed::interleaving::sources::Carrier::Scalar=>out.is_none(),
            crate::reversible_value::managed::interleaving::sources::Carrier::Payload {source,states}=>
                if states.len()==0 {out.is_none()} else {out.is_some() && out.unwrap().wf() && out.unwrap().source()==source && out.unwrap().events()==states},
        },
    {
        hide(joint::valid);hide(joint::step);
        match self {
            Self::Payload(c)=>{
                reveal(crate::reversible_value::payload::restoration::attempt::protocol::Evidence::certified);
                let tracked evidence=c.trace.borrow();evidence.representation();evidence.attempt.facts();
                evidence.attempt.history_witness()
            },_=>None,
        }
    }
    pub open spec fn decode(&self,record:joint::Record)->Option<Value<T>> {
        match self {
            Self::Payload(c)=>{
                let a=c.evidence().attempt();
                let history=if a.result().is_ok() {a.result()->Ok_0.after().states}
                    else if a.read().value().is_some() {a.read().value().unwrap().states} else {Seq::empty()};
                match record {joint::Record::Payload {source,revision}=>
                    if source==a.inverse().owner().source() && revision<history.len() {Some(Value::Payload(history[revision as int]))} else {None},_=>None}
            },
            Self::Other(CleanupDispatch::Value {..})=>match record {joint::Record::Object {state,..}=>Some(Value::Scalar(state)),_=>None},
            _=>None,
        }
    }
    pub open spec fn value_at(&self,cut:nat,key:nat)->Option<Value<T>> {
        let state=joint::state_at(self.checkpoint().events(),cut);
        if state.contains_key(key) {self.decode(state[key])} else {None}
    }
    /// This is a local mutation/read observation. It does not assert that the
    /// whole interval from queue issue to acknowledgement was atomic.
    pub open spec fn recorded(&self,action:Action<C,R,H,T,X>)->bool {
        let end=self.checkpoint();let key=address(action);
        &&& end.wf() && end.journal()==key.journal && self.read_cut()<=end.events().len()
        &&& self.value_at(self.read_cut(),key.key)==self.observed()
        &&& self.value_at(end.events().len(),key.key)==self.landed()
    }
    #[verifier::opaque]
    pub open spec fn recovery(&self,slots:Seq<Option<Action<C,R,H,T,X>>>)->bool {
        self.managed() ==> {
            let action=slots[self.ticket().token as int].unwrap();
            &&& self.from_slot(slots) && managed(action) && self.recorded(action)
            &&& self.succeeded()==(self.observed()==Some(expected(action)))
            &&& self.landed()==if self.succeeded() {Some(original(action))} else {self.observed()}
        }
    }
    /// Executed as erased proof by the actual mixed dispatcher on every return.
    pub(crate) proof fn establish_recovery(&self,slots:Seq<Option<Action<C,R,H,T,X>>>)
        requires self.from_slot(slots),ensures self.recovery(slots),
    {
        hide(joint::valid);hide(joint::step);
        reveal(Dispatch::recovery);
        match self {
            Self::Payload(c)=>{
                reveal(crate::reversible_value::payload::restoration::attempt::protocol::Evidence::certified);
                let a=c.evidence().attempt();a.facts();a.strict_domain();a.boundaries();
                let read=a.read().checkpoint();let end=a.endpoint();let key=a.inverse().owner().key();
                crate::reversible_value::managed::recovery::frame_update(end.events(),end.at());
                assert(joint::state_at(end.events(),read.events().len())==read.events().last().state);
                if a.result().is_ok() {
                    let restored=a.result()->Ok_0;restored.source_history();
                    assert(restored.after().states.take(restored.before().states.len() as int)==restored.before().states);
                }
                let action=slots[self.ticket().token as int].unwrap();
                assert(self.checkpoint().journal()==address(action).journal);
                assert(self.value_at(self.read_cut(),address(action).key)==self.observed());
                assert(self.value_at(self.checkpoint().events().len(),address(action).key)==self.landed());
                assert(self.recorded(action));
                assert(self.succeeded()==(self.observed()==Some(expected(action))));
                assert(self.landed()==if self.succeeded() {Some(original(action))} else {self.observed()});
            },
            Self::Other(CleanupDispatch::Value {completion,..})=>{
                let receipt=completion.evidence().attempt();receipt.transition();
                crate::reversible_value::managed::recovery::frame_update(receipt.events(),receipt.at());
                reveal(joint::step);reveal(joint::changes);
                let action=slots[self.ticket().token as int].unwrap();
                assert(self.checkpoint().journal()==address(action).journal);
                assert(self.value_at(self.read_cut(),address(action).key)==self.observed());
                assert(self.value_at(self.checkpoint().events().len(),address(action).key)==self.landed());
                assert(self.recorded(action));
                assert(self.succeeded()==(self.observed()==Some(expected(action))));
                assert(self.landed()==if self.succeeded() {Some(original(action))} else {self.observed()});
            },_=>{},
        }
    }
    pub open spec fn observes(&self,action:Action<C,R,H,T,X>,heap:Map<Address,Value<T>>)->bool {
        self.observed()==if heap.contains_key(address(action)) {Some(heap[address(action)])} else {None}
    }
    pub open spec fn apply_observation(&self,action:Action<C,R,H,T,X>,heap:Map<Address,Value<T>>)->Map<Address,Value<T>> {
        match self.landed() {Some(value)=>heap.insert(address(action),value),None=>heap.remove(address(action))}
    }
    pub proof fn strict_step(&self,slots:Seq<Option<Action<C,R,H,T,X>>>,heap:Map<Address,Value<T>>)
        requires self.managed(),self.recovery(slots),self.observes(slots[self.ticket().token as int].unwrap(),heap),
        ensures {
            let action=slots[self.ticket().token as int].unwrap();let next=self.apply_observation(action,heap);
            &&& undo(action,heap).is_some()==self.succeeded()
            &&& self.succeeded() ==> undo(action,heap)==Some(next)
            &&& !self.succeeded() ==> next==heap
        },
    {
        reveal(Dispatch::recovery);
        let action=slots[self.ticket().token as int].unwrap();
        if !self.succeeded() {assert(self.apply_observation(action,heap) =~= heap);}
    }
}
proof fn enabled<C,R,H,T:?Sized,X>(slots:Seq<Option<Action<C,R,H,T,X>>>,token:usize,heap:Map<Address,Value<T>>)
    requires top(slots,token),pending(slots,heap).is_some(),
    ensures undo(slots[token as int].unwrap(),heap).is_some(),
    decreases slots.len(),
{
    if token<slots.len()-1 {assert(slots.last().is_none());enabled(slots.drop_last(),token,heap);}
}
/// Algebra over the actual slots, including holes left by prior successes.
proof fn consume<C,R,H,T:?Sized,X>(slots:Seq<Option<Action<C,R,H,T,X>>>,token:usize,heap:Map<Address,Value<T>>)
    requires top(slots,token),undo(slots[token as int].unwrap(),heap).is_some(),
    ensures pending(slots,heap)==pending(slots.update(token as int,None),undo(slots[token as int].unwrap(),heap).unwrap()),
    decreases slots.len(),
{
    if token<slots.len()-1 {
        assert(slots.last().is_none());consume(slots.drop_last(),token,heap);
        assert(slots.update(token as int,None).drop_last() =~= slots.drop_last().update(token as int,None));
    } else {assert(slots.update(token as int,None).drop_last() =~= slots.drop_last());}
}
impl<C,R,H,T:?Sized,X> Dispatch<C,R,H,T,X> {
    /// Checked directly against two emitted completions. The intermediate
    /// Execution::retry transition preserves slots and changes only its ticket.
    pub open spec fn resumes(&self,earlier:Self)->bool {
        &&& self.authentic() && self.managed() && earlier.authentic() && earlier.managed() && !earlier.succeeded()
        &&& self.before_queue().link()==earlier.after_queue().link()
        &&& self.before_queue().slots()==earlier.after_queue().slots()
        &&& self.before_queue().protocol().selected()==Some(self.ticket())
        &&& self.ticket().domain==earlier.ticket().domain && self.ticket().token==earlier.ticket().token
        &&& self.ticket().attempt>earlier.ticket().attempt
    }
    pub proof fn resumed_inverse(&self,earlier:Self)
        requires self.resumes(earlier),
        ensures self.before_queue().slots()[self.ticket().token as int]==earlier.before_queue().slots()[earlier.ticket().token as int],
            self.succeeded()==(self.observed()==Some(expected(earlier.before_queue().slots()[earlier.ticket().token as int].unwrap()))),
            self.succeeded() ==> self.landed()==Some(original(earlier.before_queue().slots()[earlier.ticket().token as int].unwrap())),
    {reveal(Dispatch::recovery);}
    /// Either kind of real managed completion retires the exact attempt. A
    /// later admitted retry cannot make this old reply active again.
    pub proof fn completed_attempt_stays_closed(&self,later:&joint::Snapshot)
        requires self.authentic(),self.managed(),self.queue_link().is_some(),later.certified(),
            later.journal_spec()==self.queue_link().unwrap().0,
            self.acknowledgement().unwrap().events().len()<=later.events().len(),
            later.events().take(self.acknowledgement().unwrap().events().len() as int)==self.acknowledgement().unwrap().events(),
        ensures joint::episode::interval::retired(later.events(),self.acknowledgement().unwrap().events().len(),self.queue_link().unwrap().1,self.ticket()),
    {
        match self {
            Self::Payload(c)=>c.evidence().completed_attempt_stays_closed(later),
            Self::Other(CleanupDispatch::Value {completion,..})=>completion.evidence().completed_attempt_stays_closed(later),_=>{},
        }
    }
    /// The same law restricted to an invocation's actual retained suffix.
    pub proof fn progress_suffix(&self,before:Seq<Option<Action<C,R,H,T,X>>>,after:Seq<Option<Action<C,R,H,T,X>>>,heap:Map<Address,Value<T>>,offset:nat)
        requires self.managed(),self.recovery(before),top(before,self.ticket().token),offset<=self.ticket().token,
            after==before.update(self.ticket().token as int,if self.succeeded() {None} else {before[self.ticket().token as int]}),
            self.observes(before[self.ticket().token as int].unwrap(),heap),
        ensures pending(after.subrange(offset as int,after.len() as int),self.apply_observation(before[self.ticket().token as int].unwrap(),heap))
            ==pending(before.subrange(offset as int,before.len() as int),heap),
            pending(before.subrange(offset as int,before.len() as int),heap).is_some() ==> self.succeeded(),
    {
        self.strict_step(before,heap);
        let token=self.ticket().token;let local=(token-offset) as usize;
        let suffix=before.subrange(offset as int,before.len() as int);
        assert(top(suffix,local));
        if pending(suffix,heap).is_some() {enabled(suffix,local,heap);}
        if self.succeeded() {
            assert(top(suffix,local));consume(suffix,local,heap);
            assert(after.subrange(offset as int,after.len() as int) =~= suffix.update(local as int,None));
        } else {assert(after =~= before);}
    }
    /// A failed real attempt keeps the same recovery obligation; success
    /// transfers it to the remaining stack and the actual restored value.
    pub proof fn progress(&self,before:Seq<Option<Action<C,R,H,T,X>>>,after:Seq<Option<Action<C,R,H,T,X>>>,heap:Map<Address,Value<T>>)
        requires self.managed(),self.recovery(before),top(before,self.ticket().token),
            after==before.update(self.ticket().token as int,if self.succeeded() {None} else {before[self.ticket().token as int]}),
            self.observes(before[self.ticket().token as int].unwrap(),heap),
        ensures pending(after,self.apply_observation(before[self.ticket().token as int].unwrap(),heap))==pending(before,heap),
    {
        self.strict_step(before,heap);
        if self.succeeded() {consume(before,self.ticket().token,heap);}
        else {assert(after =~= before);}
    }
}
}
