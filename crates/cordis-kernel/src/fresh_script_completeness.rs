//! Completeness of the actual finite synchronous script runner.
//! The premise is an independent source execution with installed runtime shape;
//! it contains no successful runtime call or hypothetical replay result.
use super::{FreshDriver, ScriptReport};
#[cfg(verus_keep_ghost)]
use crate::{
    fresh_semantics as fs, mixed_driver as core,
    mixed_driver::fresh::{
        self as driver, allocation as a,
        dispatch::{exact, shape, source},
    },
    mixed_grammar as g, Port,
};
use vstd::prelude::*;
verus! {
pub open spec fn path(bank:Seq<core::Blueprint>,commands:Seq<core::Command>,states:Seq<g::Configuration<u64,core::Index>>,ts:Seq<core::Transition>)->bool {
    &&& fs::execution(core::library(),driver::programs(bank),states,driver::labels(ts)) && states.first()==g::empty::<u64,core::Index>()
    &&& shape::trace(bank,states) && exact::trace(states,ts) && a::payloads(ts,states) && a::history(ts,a::count(ts))
    &&& commands.len()==ts.len() && forall|i:int|0<=i<ts.len() ==> ts[i].command()==commands[i]
}
pub open spec fn admitted(bank:Seq<core::Blueprint>,commands:Seq<core::Command>)->bool {
    exists|target:(Seq<g::Configuration<u64,core::Index>>,Seq<core::Transition>)|path(bank,commands,target.0,target.1)
}
pub proof fn path_bounds(bank:Seq<core::Blueprint>,commands:Seq<core::Command>,states:Seq<g::Configuration<u64,core::Index>>,ts:Seq<core::Transition>)
    requires path(bank,commands,states,ts),
    ensures ts.len()==commands.len(),states.len()==commands.len()+1,states.first()==g::empty::<u64,core::Index>(),
{ }
pub proof fn path_step(bank:Seq<core::Blueprint>,commands:Seq<core::Command>,states:Seq<g::Configuration<u64,core::Index>>,ts:Seq<core::Transition>,i:int)
    requires path(bank,commands,states,ts),0<=i<ts.len(),
    ensures exact::step(bank,states[i],states[i+1],ts[i]),ts[i].command()==commands[i],
        crate::semantics::total_active(states[i].state),
        a::advance(a::count(ts.take(i)),ts[i],a::count(ts.take(i+1))),
{
    hide(fs::step);
    let label=driver::label(ts[i]);
    assert(driver::labels(ts)[i]==label);
    assert(fs::step(core::library(),driver::programs(bank),states[i],states[i+1],label.0,label.1,label.2));
    assert(shape::configuration(bank,states[i]));
    assert(shape::configuration(bank,states[i+1]));
    assert(ts[i].command()==commands[i]);
    assert(a::payload(ts[i],states[i+1]));
    assert(exact::plain(states[i],states[i+1],ts[i]));
}
pub proof fn well_formed(bank:Seq<core::Blueprint>,commands:Seq<core::Command>,states:Seq<g::Configuration<u64,core::Index>>,ts:Seq<core::Transition>)
    requires path(bank,commands,states,ts),
    ensures forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),driver::programs(bank),states[i]),
{driver::weak_theory();fs::from_empty_safe(|_:Port,x:u64,y:u64|x==y,core::library(),driver::programs(bank),states,driver::labels(ts));}
pub proof fn count_bound(ts:Seq<core::Transition>)
    ensures a::count(ts)<=ts.len(),
    decreases ts.len(),
{if ts.len()>0 {count_bound(ts.drop_last());}}
impl FreshDriver {
    pub proof fn source_service_values(&self,bank:Seq<core::Blueprint>,state:g::Configuration<u64,core::Index>)
        requires self.wf(),self.represents(bank,state),fs::well_formed(core::library(),driver::programs(bank),state),
        ensures self.service_values()==crate::projection::project(state.state,ISet::full()),
    {
        crate::projection::unique_owner(state.state);
        crate::projection::equal_payload(state.state,self.inner.primitive_state(),ISet::full());
    }
    #[verifier::spinoff_prover]
    pub proof fn source_call_at(&self,bank:Seq<core::Blueprint>,commands:Seq<core::Command>,states:Seq<g::Configuration<u64,core::Index>>,ts:Seq<core::Transition>,i:int)
        requires path(bank,commands,states,ts),0<=i<commands.len()<=usize::MAX,commands.len()<=u64::MAX,
            self.wf(),self.quiescent_journals(),self.metadata_bound(i as nat),self.represents(bank,states[i]),self.next_id()==a::count(ts.take(i)),
            fs::well_formed(core::library(),driver::programs(bank),states[i]),
        ensures source::call(self,bank,states[i],states[i+1],ts[i]),exact::plain(states[i],states[i+1],ts[i]),self.command_enabled(commands[i]),
    {
        path_step(bank,commands,states,ts,i);
        count_bound(ts.take(i));
        assert(a::advance(a::count(ts.take(i)),ts[i],a::count(ts.take(i+1))));
        match ts[i] {core::Transition::Begin {actor}|core::Transition::Unload {actor}=>self.metadata_admission(actor,i as nat),_=>{}}
        self.source_command_admission(bank,states[i],states[i+1],ts[i]);
    }
}
pub proof fn prefix(bank:Seq<core::Blueprint>,commands:Seq<core::Command>,states:Seq<g::Configuration<u64,core::Index>>,ts:Seq<core::Transition>,i:int)
    requires path(bank,commands,states,ts),0<=i<=ts.len(),
    ensures path(bank,commands.take(i),states.take(i+1),ts.take(i)),
{
    assert(driver::labels(ts.take(i))==driver::labels(ts).take(i));
    assert forall|j:int|0<=j<i implies a::advance(a::count(ts.take(i).take(j)),ts.take(i)[j],a::count(ts.take(i).take(j+1))) by {
        assert(ts.take(i).take(j)==ts.take(j));assert(ts.take(i).take(j+1)==ts.take(j+1));
    }
}
#[verifier::spinoff_prover]
pub proof fn unique_path(bank:Seq<core::Blueprint>,commands:Seq<core::Command>,left:Seq<g::Configuration<u64,core::Index>>,lt:Seq<core::Transition>,right:Seq<g::Configuration<u64,core::Index>>,rt:Seq<core::Transition>)
    requires path(bank,commands,left,lt),path(bank,commands,right,rt),
        forall|i:int|0<=i<left.len() ==> fs::well_formed(core::library(),driver::programs(bank),left[i]),
    ensures left==right,lt==rt,
    decreases commands.len(),
{
    hide(path);hide(fs::step);hide(fs::well_formed);hide(exact::step);
    path_bounds(bank,commands,left,lt);path_bounds(bank,commands,right,rt);
    if commands.len()>0 {
        let i=commands.len() as int-1;
        prefix(bank,commands,left,lt,i);prefix(bank,commands,right,rt,i);
        unique_path(bank,commands.take(i),left.take(i+1),lt.take(i),right.take(i+1),rt.take(i));
        assert(left.take(i+1)==right.take(i+1));
        assert(left.take(i+1)[i]==left[i]);assert(right.take(i+1)[i]==right[i]);
        assert(left[i]==right[i]);
        path_step(bank,commands,left,lt,i);path_step(bank,commands,right,rt,i);
        exact::unique(bank,left[i],left[i+1],lt[i],right[i+1],rt[i],a::count(lt.take(i)));
        assert(left==left.take(i+1).push(left[i+1]));assert(right==right.take(i+1).push(right[i+1]));
        assert(lt==lt.take(i).push(lt[i]));assert(rt==rt.take(i).push(rt[i]));
    } else {
        assert(left =~= right);assert(lt =~= rt);
    }
}
impl ScriptReport {
    pub open spec fn replays(&self,bank:Seq<core::Blueprint>,commands:Seq<core::Command>)->bool {
        forall|states:Seq<g::Configuration<u64,core::Index>>,ts:Seq<core::Transition>|path(bank,commands,states,ts) ==>
            self.error.is_none() && self.transitions@==ts && self.machine.represents(bank,states.last())
    }
    pub proof fn establish_replay(&self,bank:Seq<core::Blueprint>,commands:Seq<core::Command>)
        requires self.refines(bank),admitted(bank,commands) ==> self.error.is_none(),
            self.error.is_none() ==> self.transitions.len()==commands.len(),
            forall|i:int|0<=i<self.transitions.len() ==> self.transitions[i].command()==commands[i],
        ensures self.replays(bank,commands),
    {
        let actual=self.source_execution(bank);
        assert forall|states:Seq<g::Configuration<u64,core::Index>>,ts:Seq<core::Transition>|path(bank,commands,states,ts) implies
            self.error.is_none() && self.transitions@==ts && self.machine.represents(bank,states.last()) by {
            assert(admitted(bank,commands)) by {assert(path(bank,commands,(states,ts).0,(states,ts).1));}
            unique_path(bank,commands,actual,self.transitions@,states,ts);
        }
    }
}
}
