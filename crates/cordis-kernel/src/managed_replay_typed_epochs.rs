//! Head correspondence survives restoration. Semantic heads may go backwards;
//! the separately checked revision bounds only advance. Retained names are not
//! dropped when cleanup restores an older state.
#[cfg(verus_keep_ghost)]
use super::{held, typed};
use super::{State, Step};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
/// Strict order is part of the semantic name relation. It preserves forward
/// definedness on arbitrary test heads, in addition to strict inverse domains.
pub open spec fn ordered(names:Map<u64,u64>)->bool {
    forall|a:u64,b:u64|names.contains_key(a) && names.contains_key(b) ==> (a<b)==(#[trigger] names[a]<#[trigger] names[b])
}
pub proof fn ordered_extend(names:Map<u64,u64>,ac:u64,bc:u64,a:u64,b:u64)
    requires ordered(names),typed::bounded(names,ac,bc),ac<a,bc<b,
    ensures ordered(names.insert(a,b)),
{
    assert forall|x:u64,y:u64|names.insert(a,b).contains_key(x) && names.insert(a,b).contains_key(y)
        implies (x<y)==(#[trigger] names.insert(a,b)[x]<#[trigger] names.insert(a,b)[y]) by {
        if x==a && y!=a {assert(y<=ac);assert(names[y]<=bc);}
        else if y==a && x!=a {assert(x<=ac);assert(names[x]<=bc);}
    }
}
pub open spec fn heaps<T:?Sized>(names:Seq<Map<u64,u64>>,a:Seq<State<T>>,b:Seq<State<T>>,ac:Seq<u64>,bc:Seq<u64>)->bool {
    names.len()==a.len() && a.len()==b.len() && ac.len()==a.len() && bc.len()==b.len()
        && forall|i:int|0<=i<names.len() ==> {
            let m=#[trigger] names[i];
            &&& typed::injective(m) && ordered(m) && typed::bounded(m,ac[i],bc[i]) && typed::related(m,a[i],b[i])
        }
}
pub(crate) open spec fn inputs<T:?Sized>(initial:Seq<State<T>>,clocks:Seq<u64>,routes:Seq<usize>,steps:Seq<Step<T>>)->bool {
    initial.len()==clocks.len() && super::inputs(initial,routes,steps)
        && forall|i:int|0<=i<steps.len() ==> {
            let s=#[trigger] steps[i];let n=routes[s.pc as int] as int;
            &&& s.result->Payload_0.inverse().wf()
            &&& held::clocks(clocks,routes,steps.take(i))[n]<=s.result->Payload_0.inverse().before().revision
            &&& s.after()->Payload_0.head==s.result->Payload_0.inverse().after().revision
            &&& s.result->Payload_0.inverse().before().revision<s.result->Payload_0.inverse().after().revision
        }
}
pub(crate) proof fn protected_inputs<T:?Sized>(initial:Seq<State<T>>,clocks:Seq<u64>,routes:Seq<usize>,steps:Seq<Step<T>>)
    requires initial.len()==clocks.len(),held::execution(initial,clocks,routes,steps),
        forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).result is Payload && steps[i].result->Payload_0.inverse().wf(),
    ensures inputs(initial,clocks,routes,steps),
{
    reveal(held::execution);
    assert forall|i:int|0<=i<steps.len() implies {
        let s=#[trigger] steps[i];let n=routes[s.pc as int] as int;
        &&& s.result->Payload_0.inverse().wf()
        &&& held::clocks(clocks,routes,steps.take(i))[n]<=s.result->Payload_0.inverse().before().revision
        &&& s.after()->Payload_0.head==s.result->Payload_0.inverse().after().revision
        &&& s.result->Payload_0.inverse().before().revision<s.result->Payload_0.inverse().after().revision
    } by {steps[i].result->Payload_0.inverse().source_history();}
    assert forall|i:int|0<=i<steps.len() implies {
        let s=#[trigger] steps[i];
        &&& s.result is Payload && s.pc<routes.len() && routes[s.pc as int]<initial.len()
        &&& s.before()->Payload_0==held::after(initial,routes,steps.take(i))[routes[s.pc as int] as int]
        &&& super::fresh(s)
    } by {super::fresh_step(steps[i]);}
}
proof fn prefix<T:?Sized>(initial:Seq<State<T>>,clocks:Seq<u64>,routes:Seq<usize>,steps:Seq<Step<T>>,n:int)
    requires inputs(initial,clocks,routes,steps),0<=n<=steps.len(),ensures inputs(initial,clocks,routes,steps.take(n)),
{
    super::input_prefix(initial,routes,steps,n);
    assert forall|i:int|0<=i<steps.take(n).len() implies {
        let s=#[trigger] steps.take(n)[i];let k=routes[s.pc as int] as int;
        &&& s.result->Payload_0.inverse().wf()
        &&& held::clocks(clocks,routes,steps.take(n).take(i))[k]<=s.result->Payload_0.inverse().before().revision
        &&& s.after()->Payload_0.head==s.result->Payload_0.inverse().after().revision
        &&& s.result->Payload_0.inverse().before().revision<s.result->Payload_0.inverse().after().revision
    } by {assert(steps.take(n).take(i) =~= steps.take(i));}
}
proof fn extend<T:?Sized>(names:Seq<Map<u64,u64>>,a:Seq<State<T>>,b:Seq<State<T>>,ac:Seq<u64>,bc:Seq<u64>,i:int,x:State<T>,y:State<T>)->(out:Seq<Map<u64,u64>>)
    requires heaps(names,a,b,ac,bc),0<=i<a.len(),ac[i]<x.head,bc[i]<y.head,
        x.value==y.value,x.depth as nat==a[i].depth as nat+1,y.depth as nat==b[i].depth as nat+1,
    ensures out==names.update(i,names[i].insert(x.head,y.head)),super::extends(out,names),
        heaps(out,a.update(i,x),b.update(i,y),ac.update(i,x.head),bc.update(i,y.head)),
        typed::related(out[i],a[i],b[i]),typed::related(out[i],x,y),
{
    typed::extend(names[i],ac[i],bc[i],x.head,y.head);ordered_extend(names[i],ac[i],bc[i],x.head,y.head);
    let out=names.update(i,names[i].insert(x.head,y.head));
    assert forall|j:int|0<=j<out.len() implies {
        let m=#[trigger] out[j];
        &&& typed::injective(m) && ordered(m) && typed::bounded(m,ac.update(i,x.head)[j],bc.update(i,y.head)[j])
        &&& typed::related(m,a.update(i,x)[j],b.update(i,y)[j])
    } by {if j!=i {assert(out[j]==names[j]);}}
    out
}
#[verifier::rlimit(24)]
#[verifier::spinoff_prover]
pub(crate) proof fn compose<T:?Sized>(names:Seq<Map<u64,u64>>,a0:Seq<State<T>>,b0:Seq<State<T>>,ac:Seq<u64>,bc:Seq<u64>,routes:Seq<usize>,a:Seq<Step<T>>,b:Seq<Step<T>>)
    requires heaps(names,a0,b0,ac,bc),super::aligned(a,b),inputs(a0,ac,routes,a),inputs(b0,bc,routes,b),
    ensures heaps(super::names_after(names,routes,a,b),held::after(a0,routes,a),held::after(b0,routes,b),held::clocks(ac,routes,a),held::clocks(bc,routes,b)),
        super::extends(super::names_after(names,routes,a,b),names),super::paired(super::names_after(names,routes,a,b),routes,a,b),
    decreases a.len(),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);reveal(held::after);reveal(held::clocks);
    if a.len()>0 {
        let ap=a.drop_last();let bp=b.drop_last();
        prefix(a0,ac,routes,a,a.len() as int-1);prefix(b0,bc,routes,b,b.len() as int-1);
        assert(a.take(a.len() as int-1) =~= ap);assert(b.take(b.len() as int-1) =~= bp);
        compose(names,a0,b0,ac,bc,routes,ap,bp);
        let x=a.last();let y=b.last();let i=routes[x.pc as int] as int;
        let left=held::after(a0,routes,ap);let right=held::after(b0,routes,bp);
        let left_clock=held::clocks(ac,routes,ap);let right_clock=held::clocks(bc,routes,bp);
        let old=super::names_after(names,routes,ap,bp);let fresh=super::names_after(names,routes,a,b);
        assert(x.before()->Payload_0==left[i] && y.before()->Payload_0==right[i]);
        let updated=extend(old,left,right,left_clock,right_clock,i,x.after()->Payload_0,y.after()->Payload_0);
        assert(updated==fresh);super::extend_trans(fresh,old,names);
        assert(a =~= ap.push(x));assert(b =~= bp.push(y));super::append_pair(fresh,old,routes,ap,bp,x,y);
    }
}
pub ghost struct Certificate<T:?Sized> {
    pub source:Seq<Step<T>>,pub target:Seq<Step<T>>,pub routes:Seq<usize>,
    pub before_source:Seq<State<T>>,pub before_target:Seq<State<T>>,pub after_source:Seq<State<T>>,pub after_target:Seq<State<T>>,
    pub before_source_clocks:Seq<u64>,pub before_target_clocks:Seq<u64>,pub after_source_clocks:Seq<u64>,pub after_target_clocks:Seq<u64>,
    pub before_names:Seq<Map<u64,u64>>,pub after_names:Seq<Map<u64,u64>>,
}
impl<T:?Sized> Certificate<T> {
    pub closed spec fn wf(&self)->bool {
        heaps(self.before_names,self.before_source,self.before_target,self.before_source_clocks,self.before_target_clocks)
            && heaps(self.after_names,self.after_source,self.after_target,self.after_source_clocks,self.after_target_clocks)
            && super::extends(self.after_names,self.before_names) && super::paired(self.after_names,self.routes,self.source,self.target)
            && self.after_source==held::after(self.before_source,self.routes,self.source) && self.after_target==held::after(self.before_target,self.routes,self.target)
            && self.after_source_clocks==held::clocks(self.before_source_clocks,self.routes,self.source) && self.after_target_clocks==held::clocks(self.before_target_clocks,self.routes,self.target)
    }
    pub(crate) proof fn facts(&self)
        requires self.wf(),
        ensures heaps(self.before_names,self.before_source,self.before_target,self.before_source_clocks,self.before_target_clocks),
            heaps(self.after_names,self.after_source,self.after_target,self.after_source_clocks,self.after_target_clocks),
            super::extends(self.after_names,self.before_names),super::paired(self.after_names,self.routes,self.source,self.target),
            self.after_source==held::after(self.before_source,self.routes,self.source),self.after_target==held::after(self.before_target,self.routes,self.target),
            self.after_source_clocks==held::clocks(self.before_source_clocks,self.routes,self.source),self.after_target_clocks==held::clocks(self.before_target_clocks,self.routes,self.target),
    {}
    /// Historical inverse domains still agree after later writes and cleanup.
    pub proof fn inverse(&self,index:int,a:State<T>,b:State<T>)
        requires self.wf(),0<=index<self.source.len(),self.source[index].result->Payload_0.inverse().wf(),self.target[index].result->Payload_0.inverse().wf(),
            typed::related(self.after_names[self.routes[self.source[index].pc as int] as int],a,b),
        ensures self.source[index].result->Payload_0.inverse().undo(a).is_some()==self.target[index].result->Payload_0.inverse().undo(b).is_some(),
            self.source[index].result->Payload_0.inverse().undo(a).is_some() ==> typed::related(self.after_names[self.routes[self.source[index].pc as int] as int],self.source[index].result->Payload_0.inverse().undo(a).unwrap(),self.target[index].result->Payload_0.inverse().undo(b).unwrap()),
    {typed::inverse(self.after_names[self.routes[self.source[index].pc as int] as int],self.source[index].result->Payload_0.inverse(),self.target[index].result->Payload_0.inverse(),a,b);}
}
pub(crate) proof fn certify<T:?Sized>(names:Seq<Map<u64,u64>>,a0:Seq<State<T>>,b0:Seq<State<T>>,ac:Seq<u64>,bc:Seq<u64>,routes:Seq<usize>,a:Seq<Step<T>>,b:Seq<Step<T>>)->(out:Certificate<T>)
    requires heaps(names,a0,b0,ac,bc),super::aligned(a,b),inputs(a0,ac,routes,a),inputs(b0,bc,routes,b),
    ensures out.wf(),out.source==a,out.target==b,out.routes==routes,out.before_names==names,out.before_source==a0,out.before_target==b0,
        out.before_source_clocks==ac,out.before_target_clocks==bc,
{
    compose(names,a0,b0,ac,bc,routes,a,b);
    Certificate {source:a,target:b,routes,before_source:a0,before_target:b0,after_source:held::after(a0,routes,a),after_target:held::after(b0,routes,b),
        before_source_clocks:ac,before_target_clocks:bc,after_source_clocks:held::clocks(ac,routes,a),after_target_clocks:held::clocks(bc,routes,b),
        before_names:names,after_names:super::names_after(names,routes,a,b)}
}
}
