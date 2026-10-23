//! Correspondence derived from the actual protected interpreter reports.
//! These lemmas never execute a replacement interpreter or compare target data
//! after a write. Runtime admission, selection and reserves establish the domain.
use super::super::Step;
#[cfg(verus_keep_ghost)]
use super::super::{protected_typed as held, Call};
#[cfg(verus_keep_ghost)]
use super::{transport, typed};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::effect::ScalarEffect;
use crate::reversible_value::payload::State;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn complete<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,steps:Seq<Step<T>>)->bool {
    super::super::next(code.len(),steps).is_none()
        && forall|i:int|0<=i<steps.len() ==> {
            let s=#[trigger] steps[i];
            &&& Some(s.pc)==super::super::next(code.len(),steps.take(i))
            &&& s.pc<code.len() && s.result is Payload
            &&& s.next==code[s.pc as int].branch.matched
            &&& s.after()->Payload_0.value==code[s.pc as int].effect->Replace_0
        }
}
#[verifier::opaque]
pub open spec fn allocations<T:?Sized>(bank:&super::bank::Bank<T>,source:Seq<Step<T>>,target:Seq<Step<T>>)->bool {
    source.len()==target.len() && forall|i:int|0<=i<source.len() ==> super::selection::mapped(bank,#[trigger] source[i],target[i])
}
pub open spec fn aligned<T:?Sized>(a:Seq<Step<T>>,b:Seq<Step<T>>)->bool {
    a.len()==b.len() && forall|i:int|0<=i<a.len() ==> {
        let x=#[trigger] a[i];let y=b[i];
        &&& x.result is Payload && y.result is Payload && x.pc==y.pc && x.next==y.next
        &&& x.after()->Payload_0.value==y.after()->Payload_0.value
    }
}
proof fn typed_step<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,s:Step<T>)
    requires held::typed_only(code),transport::step(code,s),
    ensures s.pc<code.len(),s.result is Payload,s.next==code[s.pc as int].branch.matched,
        s.after()->Payload_0.value==code[s.pc as int].effect->Replace_0,
{held::typed_at(code,s.pc);}
#[verifier::rlimit(16)]
#[verifier::spinoff_prover]
proof fn position<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,a:Seq<Step<T>>,b:Seq<Step<T>>,n:int)
    requires held::typed_only(code),complete(code,a),complete(code,b),0<=n<=a.len(),n<=b.len(),
    ensures aligned(a.take(n),b.take(n)),super::super::next(code.len(),a.take(n))==super::super::next(code.len(),b.take(n)),
    decreases n,
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
    if n>0 {
        position(code,a,b,n-1);
        let x=a[n-1];let y=b[n-1];
        assert(x.pc==y.pc);
        assert(x.after()->Payload_0.value==y.after()->Payload_0.value);
        assert(x.next==y.next);
        assert forall|i:int|0<=i<a.take(n).len() implies {
            let x=#[trigger] a.take(n)[i];let y=b.take(n)[i];
            &&& x.result is Payload && y.result is Payload && x.pc==y.pc && x.next==y.next
            &&& x.after()->Payload_0.value==y.after()->Payload_0.value
        } by {if i<n-1 {assert(a.take(n-1)[i]==a[i]);assert(b.take(n-1)[i]==b[i]);}}
    }
}
/// A successful typed call has the same complete path under the preserved
/// program. Payload replacement has no value-dependent branch.
pub proof fn align<E:ScalarEffect,T:?Sized>(code:Seq<Call<E,T>>,a:Seq<Step<T>>,b:Seq<Step<T>>)
    requires held::typed_only(code),complete(code,a),complete(code,b),
    ensures aligned(a,b),
{
    let n=if a.len()<b.len() {a.len()} else {b.len()};
    position(code,a,b,n as int);
    if a.len()<b.len() {assert(a.take(n as int) =~= a);assert(Some(b[n as int].pc)==super::super::next(code.len(),b.take(n as int)));}
    if b.len()<a.len() {assert(b.take(n as int) =~= b);assert(Some(a[n as int].pc)==super::super::next(code.len(),a.take(n as int)));}
    assert(a.take(n as int) =~= a);assert(b.take(n as int) =~= b);
}

pub open spec fn heaps<T:?Sized>(names:Seq<Map<u64,u64>>,a:Seq<State<T>>,b:Seq<State<T>>)->bool {
    names.len()==a.len() && a.len()==b.len() && forall|i:int|0<=i<names.len() ==> {
        let m=#[trigger] names[i];
        &&& typed::injective(m) && typed::bounded(m,a[i].head,b[i].head)
        &&& typed::related(m,a[i],b[i])
    }
}
pub open spec fn extends(after:Seq<Map<u64,u64>>,before:Seq<Map<u64,u64>>)->bool {
    after.len()==before.len() && forall|i:int,h:u64|0<=i<before.len() && #[trigger] before[i].contains_key(h)
        ==> after[i].contains_pair(h,before[i][h])
}
pub open spec fn fresh<T:?Sized>(s:Step<T>)->bool {
    s.result is Payload && s.before()->Payload_0.head<s.after()->Payload_0.head
        && s.after()->Payload_0.depth as nat==s.before()->Payload_0.depth as nat+1
}
pub(crate) proof fn fresh_step<T:?Sized>(s:Step<T>)
    requires s.result is Payload,s.result->Payload_0.inverse().wf(),ensures fresh(s),
{hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);s.result->Payload_0.inverse().source_history();}
pub(crate) open spec fn inputs<T:?Sized>(initial:Seq<State<T>>,routes:Seq<usize>,steps:Seq<Step<T>>)->bool {
    forall|i:int|0<=i<steps.len() ==> {
        let s=#[trigger] steps[i];
        &&& s.result is Payload && s.pc<routes.len() && routes[s.pc as int]<initial.len()
        &&& s.before()->Payload_0==held::after(initial,routes,steps.take(i))[routes[s.pc as int] as int]
        &&& fresh(s)
    }
}
pub open spec fn paired<T:?Sized>(names:Seq<Map<u64,u64>>,routes:Seq<usize>,a:Seq<Step<T>>,b:Seq<Step<T>>)->bool {
    aligned(a,b) && forall|i:int|0<=i<a.len() ==> {
        let x=#[trigger] a[i];let y=b[i];
        &&& x.pc<routes.len() && routes[x.pc as int]<names.len()
        &&& typed::related(names[routes[x.pc as int] as int],x.before()->Payload_0,y.before()->Payload_0)
        &&& typed::related(names[routes[x.pc as int] as int],x.after()->Payload_0,y.after()->Payload_0)
    }
}
pub open spec fn names_after<T:?Sized>(initial:Seq<Map<u64,u64>>,routes:Seq<usize>,a:Seq<Step<T>>,b:Seq<Step<T>>)->Seq<Map<u64,u64>>
    decreases a.len(),
{
    if a.len()==0 {initial} else {
        let previous=names_after(initial,routes,a.drop_last(),b.drop_last());let i=routes[a.last().pc as int] as int;
        previous.update(i,previous[i].insert(a.last().after()->Payload_0.head,b.last().after()->Payload_0.head))
    }
}
proof fn frame_related<T:?Sized>(after:Seq<Map<u64,u64>>,before:Seq<Map<u64,u64>>,i:int,a:State<T>,b:State<T>)
    requires extends(after,before),0<=i<before.len(),typed::related(before[i],a,b),
    ensures typed::related(after[i],a,b),
{assert(before[i].contains_key(a.head));}

proof fn input_prefix<T:?Sized>(initial:Seq<State<T>>,routes:Seq<usize>,steps:Seq<Step<T>>,n:int)
    requires inputs(initial,routes,steps),0<=n<=steps.len(),ensures inputs(initial,routes,steps.take(n)),
{
    assert forall|i:int|0<=i<steps.take(n).len() implies {
        let s=#[trigger] steps.take(n)[i];
        &&& s.result is Payload && s.pc<routes.len() && routes[s.pc as int]<initial.len()
        &&& s.before()->Payload_0==held::after(initial,routes,steps.take(n).take(i))[routes[s.pc as int] as int]
        &&& fresh(s)
    } by {assert(steps.take(n).take(i) =~= steps.take(i));}
}
proof fn extend_trans(a:Seq<Map<u64,u64>>,b:Seq<Map<u64,u64>>,c:Seq<Map<u64,u64>>)
    requires extends(a,b),extends(b,c),ensures extends(a,c),
{assert forall|i:int,h:u64|0<=i<c.len() && #[trigger] c[i].contains_key(h) implies a[i].contains_pair(h,c[i][h]) by {assert(b[i].contains_key(h));}}
proof fn step_heaps<T:?Sized>(names:Seq<Map<u64,u64>>,a:Seq<State<T>>,b:Seq<State<T>>,i:int,x:State<T>,y:State<T>)->(out:Seq<Map<u64,u64>>)
    requires heaps(names,a,b),0<=i<a.len(),a[i].head<x.head,b[i].head<y.head,
        x.value==y.value,x.depth as nat==a[i].depth as nat+1,y.depth as nat==b[i].depth as nat+1,
    ensures out==names.update(i,names[i].insert(x.head,y.head)),extends(out,names),
        heaps(out,a.update(i,x),b.update(i,y)),typed::related(out[i],a[i],b[i]),typed::related(out[i],x,y),
{
    typed::extend(names[i],a[i].head,b[i].head,x.head,y.head);
    let out=names.update(i,names[i].insert(x.head,y.head));
    assert(typed::related(out[i],a[i],b[i]));assert(typed::related(out[i],x,y));
    assert forall|j:int|0<=j<out.len() implies {
        let m=#[trigger] out[j];
        &&& typed::injective(m) && typed::bounded(m,a.update(i,x)[j].head,b.update(i,y)[j].head)
        &&& typed::related(m,a.update(i,x)[j],b.update(i,y)[j])
    } by {if j!=i {assert(out[j]==names[j]);}}
    out
}
proof fn append_pair<T:?Sized>(names:Seq<Map<u64,u64>>,previous:Seq<Map<u64,u64>>,routes:Seq<usize>,a:Seq<Step<T>>,b:Seq<Step<T>>,x:Step<T>,y:Step<T>)
    requires paired(previous,routes,a,b),extends(names,previous),aligned(a.push(x),b.push(y)),x.pc<routes.len(),routes[x.pc as int]<names.len(),
        typed::related(names[routes[x.pc as int] as int],x.before()->Payload_0,y.before()->Payload_0),
        typed::related(names[routes[x.pc as int] as int],x.after()->Payload_0,y.after()->Payload_0),
    ensures paired(names,routes,a.push(x),b.push(y)),
{
    assert forall|j:int|0<=j<a.push(x).len() implies {
        let s=#[trigger] a.push(x)[j];let t=b.push(y)[j];
        &&& s.pc<routes.len() && routes[s.pc as int]<names.len()
        &&& typed::related(names[routes[s.pc as int] as int],s.before()->Payload_0,t.before()->Payload_0)
        &&& typed::related(names[routes[s.pc as int] as int],s.after()->Payload_0,t.after()->Payload_0)
    } by {if j<a.len() {
        frame_related(names,previous,routes[a[j].pc as int] as int,a[j].before()->Payload_0,b[j].before()->Payload_0);
        frame_related(names,previous,routes[a[j].pc as int] as int,a[j].after()->Payload_0,b[j].after()->Payload_0);
    }}
}

/// Compose the primitive injective head law over both actual call histories.
/// Clocks remain target-issued; only the erased semantic name map is extended.
#[verifier::rlimit(24)]
#[verifier::spinoff_prover]
pub(crate) proof fn compose<T:?Sized>(initial:Seq<Map<u64,u64>>,a0:Seq<State<T>>,b0:Seq<State<T>>,routes:Seq<usize>,a:Seq<Step<T>>,b:Seq<Step<T>>)
    requires heaps(initial,a0,b0),aligned(a,b),inputs(a0,routes,a),inputs(b0,routes,b),
    ensures heaps(names_after(initial,routes,a,b),held::after(a0,routes,a),held::after(b0,routes,b)),
        extends(names_after(initial,routes,a,b),initial),paired(names_after(initial,routes,a,b),routes,a,b),
    decreases a.len(),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);reveal(held::after);
    if a.len()==0 {} else {
        let ap=a.drop_last();let bp=b.drop_last();
        input_prefix(a0,routes,a,a.len() as int-1);input_prefix(b0,routes,b,b.len() as int-1);
        assert(a.take(a.len() as int-1) =~= ap);assert(b.take(b.len() as int-1) =~= bp);
        compose(initial,a0,b0,routes,ap,bp);
        let x=a.last();let y=b.last();let i=routes[x.pc as int] as int;
        let left=held::after(a0,routes,ap);let right=held::after(b0,routes,bp);
        let old=names_after(initial,routes,ap,bp);let fresh=names_after(initial,routes,a,b);
        assert(a.take(a.len() as int-1) =~= ap);assert(b.take(b.len() as int-1) =~= bp);
        assert(x.before()->Payload_0==left[i] && y.before()->Payload_0==right[i]);
        let extended=step_heaps(old,left,right,i,x.after()->Payload_0,y.after()->Payload_0);
        assert(extended==fresh);extend_trans(fresh,old,initial);
        assert(a =~= ap.push(x));assert(b =~= bp.push(y));
        append_pair(fresh,old,routes,ap,bp,x,y);
    }
}

/// Erased evidence connecting real protected calls and their retained inverses.
pub ghost struct Certificate<T:?Sized> {
    pub source:Seq<Step<T>>,pub target:Seq<Step<T>>,pub routes:Seq<usize>,
    pub before_source:Seq<State<T>>,pub after_source:Seq<State<T>>,
    pub before_target:Seq<State<T>>,pub after_target:Seq<State<T>>,
    pub before_names:Seq<Map<u64,u64>>,pub after_names:Seq<Map<u64,u64>>,
}
impl<T:?Sized> Certificate<T> {
    pub proof fn facts(&self)
        requires self.wf(),ensures heaps(self.before_names,self.before_source,self.before_target),
            heaps(self.after_names,self.after_source,self.after_target),extends(self.after_names,self.before_names),
            paired(self.after_names,self.routes,self.source,self.target),aligned(self.source,self.target),
    {}

    pub closed spec fn wf(&self)->bool {
        heaps(self.before_names,self.before_source,self.before_target)
            && heaps(self.after_names,self.after_source,self.after_target)
            && extends(self.after_names,self.before_names)
            && paired(self.after_names,self.routes,self.source,self.target)
    }
    /// Source/target inverses have the same strict domain on every related
    /// state, not only at the successful runtime example's final state.
    pub proof fn inverse(&self,position:int,a:State<T>,b:State<T>)
        requires self.wf(),0<=position<self.source.len(),
            self.source[position].result->Payload_0.inverse().wf(),self.target[position].result->Payload_0.inverse().wf(),
            typed::related(self.after_names[self.routes[self.source[position].pc as int] as int],a,b),
        ensures self.source[position].result->Payload_0.inverse().undo(a).is_some()==self.target[position].result->Payload_0.inverse().undo(b).is_some(),
            self.source[position].result->Payload_0.inverse().undo(a).is_some() ==>
                typed::related(self.after_names[self.routes[self.source[position].pc as int] as int],
                    self.source[position].result->Payload_0.inverse().undo(a).unwrap(),self.target[position].result->Payload_0.inverse().undo(b).unwrap()),
    {
        let i=self.routes[self.source[position].pc as int] as int;
        typed::inverse(self.after_names[i],self.source[position].result->Payload_0.inverse(),self.target[position].result->Payload_0.inverse(),a,b);
    }
}
#[verifier::rlimit(12)]
#[verifier::spinoff_prover]
pub(crate) proof fn certify<E:ScalarEffect,T:?Sized>(source:&super::Source<E,T>,run:&super::batch::Run<E,T>,plan:&super::typed_tracker::Plan<T>,bank:&super::bank::Bank<T>,before:Seq<State<T>>,revisions:Seq<u64>,routes:Seq<usize>)->(out:Certificate<T>)
    requires source.wf(),source.original().succeeded(),held::typed_only(source.program().code()),run.from_source(source),run.report.is_ok(),
        run.report->Ok_0.result.is_ok(),run.report->Ok_0.result->Ok_0.failure.is_none(),bank.wf(),plan.wf(bank),
        plan.steps()==source.original().result->Ok_0.steps@,super::protected::mapped(bank,routes,plan.steps()),
        heaps(plan.prior_names(),plan.before(),before),held::execution(before,revisions,routes,run.report->Ok_0.result->Ok_0.steps@),
    ensures out.wf(),out.source==plan.steps(),out.target==run.report->Ok_0.result->Ok_0.steps@,out.routes==routes,
        out.before_source==plan.before(),out.after_source==plan.after(),out.before_target==before,
        out.after_target==held::after(before,routes,out.target),out.before_names==plan.prior_names(),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
    reveal(super::TargetRun::from_source);reveal(held::execution);
    source.facts();plan.routes(bank,routes);
    let a=source.original().result->Ok_0.steps@;let b=run.report->Ok_0.result->Ok_0.steps@;
    assert forall|i:int|0<=i<a.len() implies {
        let s=#[trigger] a[i];
        &&& Some(s.pc)==super::super::next(source.program().code().len(),a.take(i))
        &&& s.pc<source.program().code().len() && s.result is Payload
        &&& s.next==source.program().code()[s.pc as int].branch.matched
        &&& s.after()->Payload_0.value==source.program().code()[s.pc as int].effect->Replace_0
    } by {typed_step(source.program().code(),a[i]);}
    assert forall|i:int|0<=i<b.len() implies {
        let s=#[trigger] b[i];
        &&& Some(s.pc)==super::super::next(source.program().code().len(),b.take(i))
        &&& s.pc<source.program().code().len() && s.result is Payload
        &&& s.next==source.program().code()[s.pc as int].branch.matched
        &&& s.after()->Payload_0.value==source.program().code()[s.pc as int].effect->Replace_0
    } by {typed_step(source.program().code(),b[i]);}
    assert(complete(source.program().code(),a));assert(complete(source.program().code(),b));
    align(source.program().code(),a,b);
    assert forall|i:int|0<=i<b.len() implies {
        let s=#[trigger] b[i];
        &&& s.result is Payload && s.pc<routes.len() && routes[s.pc as int]<before.len()
        &&& s.before()->Payload_0==held::after(before,routes,b.take(i))[routes[s.pc as int] as int]
        &&& fresh(s)
    } by {
        b[i].record_values(source.program().code()[b[i].pc as int],run.report->Ok_0.ports@[b[i].pc as int],run.owner.baseline().value_state().unwrap());
        fresh_step(b[i]);
    }
    compose(plan.prior_names(),plan.before(),before,routes,a,b);
    Certificate {source:a,target:b,routes,before_source:plan.before(),after_source:plan.after(),before_target:before,
        after_target:held::after(before,routes,b),before_names:plan.prior_names(),after_names:names_after(plan.prior_names(),routes,a,b)}
}
}
verus! {
/// Shared composition for real typed projections of homogeneous or mixed
/// reports. Callers derive both input traces from authentic records/guards.
pub(crate) proof fn certify_steps<T:?Sized>(names:Seq<Map<u64,u64>>,a0:Seq<State<T>>,b0:Seq<State<T>>,routes:Seq<usize>,a:Seq<Step<T>>,b:Seq<Step<T>>)->(out:Certificate<T>)
    requires heaps(names,a0,b0),aligned(a,b),inputs(a0,routes,a),inputs(b0,routes,b),
    ensures out.wf(),out.source==a,out.target==b,out.routes==routes,out.before_source==a0,out.before_target==b0,
        out.after_source==held::after(a0,routes,a),out.after_target==held::after(b0,routes,b),out.before_names==names,
{
    compose(names,a0,b0,routes,a,b);
    Certificate {source:a,target:b,routes,before_source:a0,after_source:held::after(a0,routes,a),before_target:b0,
        after_target:held::after(b0,routes,b),before_names:names,after_names:names_after(names,routes,a,b)}
}
}

pub mod epochs;
