//! Local transport laws for the actual source and target interpreter reports.
//! Equal inputs are explicit: this does not assume a globally replayable heap.
#[cfg(verus_keep_ghost)]
use super::Source;
use super::TargetRun;
use crate::reversible_value::effect::ScalarEffect;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::{
    self as managed,
    semantics::{self as s, Value},
    Call, Step,
};
use vstd::prelude::*;
verus! {
pub open spec fn step<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,s:Step<T>)->bool {
    s.pc<code.len() && {
        let call=code[s.pc as int];let op=s::operation(s::code(call.effect,s.head()));
        &&& op(s.before()).is_some()
        &&& op(s.before()).unwrap().value==s.after()
        &&& op(s.before()).unwrap().outcome==s.outcome()
        &&& s::selected(call.branch,s.outcome())==s.next
        &&& s.write().wf()
        &&& forall|v:Value<T>| #[trigger] (op(s.before()).unwrap().undo)(v)==if v==s.after() {Some(s.before())} else {None}
    }
}
pub open spec fn steps<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,report:managed::Report<T>)->bool {
    forall|i:int|0<=i<report.steps.len() ==> step(code,#[trigger] report.steps@[i])
}
pub proof fn derive<E:ScalarEffect,T:?Sized,M>(code:Seq<Call<E,T>>,report:managed::Report<T>,ports:Seq<crate::Port>,episode:crate::lifecycle_state::services::NativeEpisode<managed::Slot<T,M>>)
    requires report.certified(code,ports,episode),
    ensures steps(code,report),
{
    assert forall|i:int|0<=i<report.steps.len() implies step(code,#[trigger] report.steps@[i]) by {
        let s=report.steps@[i];s.interpretation(code[s.pc as int],ports[s.pc as int],episode);
    }
}
/// Scalar depth is operational state. Opaque payload values agree while each
/// target object keeps its freshly issued head and its own strict inverse.
pub open spec fn values<T:?Sized>(a:Value<T>,b:Value<T>)->bool {
    match (a,b) {(Value::Scalar(x),Value::Scalar(y))=>x==y,(Value::Payload(x),Value::Payload(y))=>x.value==y.value,_=>false}
}
pub proof fn paired<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,a:Step<T>,b:Step<T>)
    requires step(code,a),step(code,b),a.pc==b.pc,values(a.before(),b.before()),
    ensures values(a.after(),b.after()),a.outcome()==b.outcome(),a.next==b.next,
{
    match code[a.pc as int].effect {
        managed::Effect::Scalar(_)|managed::Effect::Kernel(_)=>{assert(a.before() is Scalar);assert(b.before() is Scalar);},
        managed::Effect::Replace(_)=>{assert(a.before() is Payload);assert(b.before() is Payload);},
    }
}
impl<C,G,A,R,T:?Sized,M,X,E:ScalarEffect> TargetRun<C,G,A,R,T,M,X,E> {
    /// This relates actual writes and actual target inverses. The target is
    /// produced by instantiate; neither a desired outcome nor a target Journal
    /// frame was an executable input to it.
    pub proof fn pair_step(&self,source:&Source<E,T>,original:int,target:int)
        requires source.wf(),self.from_source(source),source.original().result.is_ok(),
            self.report.is_ok(),self.report->Ok_0.result.is_ok(),
            0<=original<source.original().result->Ok_0.steps.len(),0<=target<self.report->Ok_0.result->Ok_0.steps.len(),
            source.original().result->Ok_0.steps@[original].pc==self.report->Ok_0.result->Ok_0.steps@[target].pc,
            values(source.original().result->Ok_0.steps@[original].before(),self.report->Ok_0.result->Ok_0.steps@[target].before()),
        ensures values(source.original().result->Ok_0.steps@[original].after(),self.report->Ok_0.result->Ok_0.steps@[target].after()),
            source.original().result->Ok_0.steps@[original].next==self.report->Ok_0.result->Ok_0.steps@[target].next,
            self.report->Ok_0.result->Ok_0.steps@[target].registered(self.owner.baseline().cleanup_state().link(),0),
            self.report->Ok_0.result->Ok_0.steps@[target].in_slot(self.owner.baseline().cleanup_state().queues()[0].slots()[self.offset@+target]),
    {
        source.facts();paired(source.program().code(),source.original().result->Ok_0.steps@[original],self.report->Ok_0.result->Ok_0.steps@[target]);
    }
}
}
