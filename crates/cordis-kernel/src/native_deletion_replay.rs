//! Source-certified native window -> real production Kernel execution.
//! Concrete insertion inputs are bound to the original snapshot. The adapter
//! constructs target legality; callers never provide a successful target run.
#[cfg(verus_keep_ghost)]
use super::super::History;
use super::super::Snapshot;
use super::trace::Window;
use crate::kernel_replay::{self as replay, names, Command};
#[cfg(verus_keep_ghost)]
use crate::{alpha, refinement as r};
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
/// Input evidence concerns only the actual source: its labels, original
/// insertion arguments, finite counter bounds and the selected native window.
pub open spec fn corresponds<V>(h:History<V>,commands:Seq<Command>)->bool {
    &&& commands.len()==h.labels.len() && commands.len()<u64::MAX
    &&& forall|i:int|0<=i<commands.len() ==> (#[trigger] commands[i]).shape() && commands[i].payload(h.states[i+1].control)
        && (commands[i].actor(),commands[i].rule())==h.labels[i]
}
pub open spec fn mask<V>(h:History<V>,keep:Seq<bool>,w:Window)->bool {
    keep.len()==h.labels.len() && forall|i:int|0<=i<keep.len() ==> keep[i]==w.keep(i,h.labels[i])
}
pub open spec fn source<V>(h:History<V>,commands:Seq<Command>,keep:Seq<bool>,bound:usize,w:Window)->bool {
    corresponds(h,commands) && mask(h,keep,w)
        && forall|i:int|0<=i<commands.len() && commands[i] is Insert ==> commands[i].actor()<bound
}
pub proof fn copy_correspondence<V>(h:History<V>,a:Seq<Command>,b:Seq<Command>)
    requires corresponds(h,a),replay::same_commands(b,a),ensures corresponds(h,b),
{
    assert forall|i:int|0<=i<b.len() implies (#[trigger] b[i]).shape() && b[i].payload(h.states[i+1].control)
        && (b[i].actor(),b[i].rule())==h.labels[i] by {assert(b[i].same(a[i]));}
}
proof fn source_at<V>(h:History<V>,commands:Seq<Command>,keep:Seq<bool>,bound:usize,w:Window,i:int)
    requires source(h,commands,keep,bound,w),0<=i<commands.len(),
    ensures commands[i].shape(),commands[i].payload(h.states[i+1].control),
        commands[i].actor()==h.labels[i].0,commands[i].rule()==h.labels[i].1,keep[i]==w.keep(i,h.labels[i]),
        commands[i] is Insert ==> commands[i].actor()<bound,
{assert(commands[i].shape());}
pub open spec fn states<V>(h:History<V>,w:Window,rho:alpha::Renaming)->Seq<r::State> {
    w.target(h).controls().map(|_:int,s:r::State|alpha::rename(rho,s))
}
proof fn source_shape<V>(h:History<V>,commands:Seq<Command>,keep:Seq<bool>,bound:usize,w:Window)
    requires h.valid(),h.fresh_insertions(),source(h,commands,keep,bound,w),
    ensures names::source_shape(commands,keep,bound),
{
    reveal(History::fresh_insertions);
    assert forall|i:int|0<=i<commands.len() && commands[i] is Insert implies commands[i].actor()<bound by {source_at(h,commands,keep,bound,w,i);}
    assert forall|i:int,j:int|0<=i<j<commands.len() && commands[i] is Insert && commands[j] is Insert implies commands[i].actor()!=commands[j].actor() by {
        source_at(h,commands,keep,bound,w,i);source_at(h,commands,keep,bound,w,j);
        assert(super::super::step(h.states[i],h.states[i+1],h.labels[i].0,h.labels[i].1));
        assert(r::registered(h.states[i+1].control,commands[i].actor()));
        assert(!r::registered(h.states[i+1].control,commands[j].actor()));
    }
}
proof fn selection<V>(h:History<V>,commands:Seq<Command>,keep:Seq<bool>,bound:usize,w:Window,n:nat)
    requires source(h,commands,keep,bound,w),n<=commands.len(),
    ensures names::selected(commands.take(n as int),keep.take(n as int)).len()==w.positions(h,n).len(),
        names::selected(commands.take(n as int),keep.take(n as int)).len()<=n,
    decreases n,
{
    if n>0 {
        selection(h,commands,keep,bound,w,(n-1) as nat);
        names::prefix(commands,keep,n as int-1);source_at(h,commands,keep,bound,w,n as int-1);
    }
}
proof fn selection_item<V>(h:History<V>,commands:Seq<Command>,keep:Seq<bool>,bound:usize,w:Window,n:nat,k:int)
    requires source(h,commands,keep,bound,w),n<=commands.len(),0<=k<names::selected(commands.take(n as int),keep.take(n as int)).len(),
    ensures 0<=w.positions(h,n)[k]<n,
        names::selected(commands.take(n as int),keep.take(n as int))[k]==commands[w.positions(h,n)[k]],
        names::selected(commands.take(n as int),keep.take(n as int)).take(k)==names::selected(commands.take(w.positions(h,n)[k]),keep.take(w.positions(h,n)[k])),
    decreases n,
{
    assert(n>0);selection(h,commands,keep,bound,w,(n-1) as nat);
    names::prefix(commands,keep,n as int-1);source_at(h,commands,keep,bound,w,n as int-1);
    let before=names::selected(commands.take(n as int-1),keep.take(n as int-1));
    let out=names::selected(commands.take(n as int),keep.take(n as int));let ps=w.positions(h,n);
    if k<before.len() {
        selection_item(h,commands,keep,bound,w,(n-1) as nat,k);
        assert(ps[k]==w.positions(h,(n-1) as nat)[k]);assert(out[k]==before[k]);assert(out.take(k)==before.take(k));
    } else {assert(k==before.len());assert(ps[k]==n-1);assert(out.take(k)==before);}
}
proof fn allocation_renaming(rho:alpha::Renaming,commands:Seq<Command>)
    ensures replay::allocations(commands.map(|_:int,c:Command|c.renamed(rho)))==replay::allocations(commands),
    decreases commands.len(),
{
    if commands.len()>0 {
        allocation_renaming(rho,commands.drop_last());
        assert(commands.map(|_:int,c:Command|c.renamed(rho)).drop_last()==commands.drop_last().map(|_:int,c:Command|c.renamed(rho)));
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
proof fn executable_step<V>(h:History<V>,commands:Seq<Command>,keep:Seq<bool>,bound:usize,w:Window,plan:names::Plan,k:int)
    requires h.valid(),w.admissible(h),source(h,commands,keep,bound,w),plan.matches(commands,keep),plan.names.size()==bound,0<=k<plan.commands.len(),
    ensures {
        let out=states(h,w,plan.names.renaming());let c=plan.commands[k];
        &&& c.shape() && c.payload(out[k+1]) && r::step(out[k],out[k+1],c.actor(),c.rule())
        &&& c is Insert ==> c.actor()==replay::allocations(plan.commands@.take(k)) && replay::allocations(plan.commands@.take(k))<usize::MAX
    },
{
    hide(Window::prefix);hide(names::selected);hide(replay::allocations);
    w.construct(h,h.labels.len());selection(h,commands,keep,bound,w,commands.len());
    let target=w.target(h);let selected=names::selected(commands,keep);let ps=w.positions(h,h.labels.len());
    let rho=plan.names.renaming();plan.names.bijection();let out=states(h,w,rho);
    selection_item(h,commands,keep,bound,w,commands.len(),k);
    let i=ps[k];source_at(h,commands,keep,bound,w,i);let c=commands[i];let next=target.states[k+1].control;
    assert(super::super::step(target.states[k],target.states[k+1],target.labels[k].0,target.labels[k].1));
    alpha::step_forward(rho,target.states[k].control,next,c.actor(),c.rule());
    assert(plan.commands[k].same(c.renamed(rho)));
    if c is Insert {
        assert(c.payload(next));alpha::observations(rho,next,c.actor());
        assert(plan.commands[k].payload(out[k+1]));
        assert(replay::same_commands(plan.commands@.take(k),selected.take(k).map(|_:int,c:Command|c.renamed(rho))));
        replay::allocation_equivalent(plan.commands@.take(k),selected.take(k).map(|_:int,c:Command|c.renamed(rho)));
        allocation_renaming(rho,selected.take(k));
        assert(plan.commands[k].actor()==replay::allocations(plan.commands@.take(k)));
        plan.names.name_bound(c.actor());
    }
}
/// The decisive bridge: all target guards, declarations and dense allocation
/// positions follow from the source window and the executable name preparer.
pub proof fn executable_path<V>(h:History<V>,commands:Seq<Command>,keep:Seq<bool>,bound:usize,w:Window,plan:names::Plan)
    requires h.valid(),w.admissible(h),source(h,commands,keep,bound,w),plan.matches(commands,keep),plan.names.size()==bound,
    ensures replay::path(plan.commands@,states(h,w,plan.names.renaming())),
{
    hide(Window::prefix);hide(names::selected);hide(replay::allocations);
    let target=w.delete(h);w.construct(h,h.labels.len());selection(h,commands,keep,bound,w,commands.len());
    plan.names.bijection();let out=states(h,w,plan.names.renaming());
    assert(out.first().fibers.dom().is_empty()) by {
        assert forall|n:usize|!out.first().fibers.dom().contains(n) by { }
    }
    assert(out.len()==plan.commands.len()+1);assert(plan.commands.len()<u64::MAX);
    assert forall|k:int|0<=k<plan.commands.len() implies plan.commands[k].shape() && plan.commands[k].payload(out[k+1])
        && r::step(out[k],out[k+1],plan.commands[k].actor(),plan.commands[k].rule())
        && (plan.commands[k] is Insert ==> plan.commands[k].actor()==replay::allocations(plan.commands@.take(k)) && replay::allocations(plan.commands@.take(k))<usize::MAX) by {
        executable_step(h,commands,keep,bound,w,plan,k);
    }
}
pub struct Replay {pub execution:replay::Execution,pub plan:names::Plan}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Error {Preparation(names::Error),Execution(crate::Error)}
impl<V> Snapshot<V> {
    /// Replay the control projection using production methods. Input vectors
    /// describe the source insertions and deletion choice, not expected results.
    pub fn replay_control_window(&self,commands:&[Command],keep:&[bool],bound:usize,Ghost(window):Ghost<Window>)->(out:Result<Replay,Error>)
        requires self.certified(),window.admissible(self.history()),source(self.history(),commands@,keep@,bound,window),
        ensures out.is_ok(),out.unwrap().plan.matches(commands@,keep@),out.unwrap().execution.control().wf(),
            out.unwrap().execution.states()==states(self.history(),window,out.unwrap().plan.names.renaming()),
            out.unwrap().execution.control().paper()==alpha::rename(out.unwrap().plan.names.renaming(),self.history().states.last().control),
            out.unwrap().execution.control().next_id()==replay::allocations(out.unwrap().plan.commands@),
            replay::represented_generations(out.unwrap().execution.control(),replay::generations(out.unwrap().plan.commands@)),
    {
        proof {self.valid_history();source_shape(self.history(),commands@,keep@,bound,window);}
        let plan=match names::compact(commands,keep,bound) {Ok(plan)=>plan,Err(e)=>return Err(Error::Preparation(e))};
        proof {executable_path(self.history(),commands@,keep@,bound,window,plan);}
        let execution=match replay::execute(plan.commands.as_slice(),Ghost(states(self.history(),window,plan.names.renaming()))) {Ok(run)=>run,Err(e)=>return Err(Error::Execution(e))};
        proof {let _=window.delete(self.history());}
        Ok(Replay {execution,plan})
    }
}
}
