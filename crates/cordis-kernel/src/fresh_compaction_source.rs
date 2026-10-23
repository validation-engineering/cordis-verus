//! Connect executable compacted commands to the same actual source witness.
use super::Plan;
#[cfg(verus_keep_ghost)]
use super::{renamed, selected};
#[cfg(verus_keep_ghost)]
use crate::{
    alpha as n, closed_region_deletion as region, fresh_equivariance as e, fresh_grammar as f,
    fresh_semantics as fs,
    mixed_driver::fresh::{
        self as driver, allocation as a,
        dispatch::{exact, shape},
        names, ScriptReport,
    },
    mixed_driver::{library, library_theory, Blueprint, Index, Transition},
    mixed_grammar as g, projection as p, Port,
};
use vstd::prelude::*;
verus! {
pub open spec fn mask(ts:Seq<Transition>,keep:Seq<bool>,r:region::Region)->bool {
    ts.len()==keep.len() && forall|i:int|0<=i<ts.len() ==> keep[i]==r.keep(ts[i].label().0,ts[i].label().1)
}
pub open spec fn witness(report:&ScriptReport,bank:Seq<Blueprint>,states:Seq<g::Configuration<u64,Index>>)->bool {
    &&& fs::execution(library(),driver::programs(bank),states,driver::labels(report.transitions@))
    &&& states.first()==g::empty::<u64,Index>() && report.machine.represents(bank,states.last())
    &&& shape::trace(bank,states) && exact::trace(states,report.transitions@)
    &&& a::payloads(report.transitions@,states) && a::history(report.transitions@,report.machine.next_id())
}
pub proof fn labels(ts:Seq<Transition>,keep:Seq<bool>,r:region::Region)
    requires mask(ts,keep,r),
    ensures driver::labels(selected(ts,keep))==region::fresh_trace::kept(driver::labels(ts),r),
    decreases ts.len(),
{
    if ts.len()>0 {
        labels(ts.drop_last(),keep.drop_last(),r);
        assert(driver::labels(ts.drop_last())==driver::labels(ts).drop_last());
        if keep.last() {
            assert(driver::labels(selected(ts,keep))==driver::labels(selected(ts.drop_last(),keep.drop_last())).push(driver::label(ts.last())));
        }
    }
}
pub proof fn deletion_payloads(ts:Seq<Transition>,keep:Seq<bool>,states:Seq<g::Configuration<u64,Index>>,r:region::Region,rho:spec_fn(nat)->nat)
    requires mask(ts,keep,r),a::payloads(ts,states),
    ensures a::payloads(selected(ts,keep),region::fresh_trace::delete(states,driver::labels(ts),r,rho)),
    decreases ts.len(),
{
    if ts.len()>0 {
        deletion_payloads(ts.drop_last(),keep.drop_last(),states.drop_last(),r,rho);
        assert(driver::labels(ts.drop_last())==driver::labels(ts).drop_last());
        if keep.last() {
            let t=ts.last();let z=region::configuration(states.last(),r,rho);
            assert(a::payload(t,states.last()));
            match t {Transition::Insert {actor,..}=>{assert(!r.born.contains(actor));},_=>{}}
            assert(a::payload(t,z));
            a::append_payload(selected(ts.drop_last(),keep.drop_last()),region::fresh_trace::delete(states.drop_last(),driver::labels(ts.drop_last()),r,rho),t,z);
        }
    }
}
pub proof fn rename_payloads(r:n::Renaming,ts:Seq<Transition>,states:Seq<g::Configuration<u64,Index>>)
    requires n::bijective(r),a::payloads(ts,states),
    ensures a::payloads(renamed(r,ts),e::configurations(r,f::action_map(f::name_free::<Index>(),r),states)),
        driver::labels(renamed(r,ts))==e::labels(r,driver::labels(ts)),
{
    let h=f::action_map(f::name_free::<Index>(),r);
    assert forall|i:int|0<=i<ts.len() implies a::payload(renamed(r,ts)[i],e::configurations(r,h,states)[i+1]) by {
        let t=ts[i];let z=states[i+1];assert(a::payload(t,z));
        match t {Transition::Insert {actor,..}=>{n::observations(r,z.state.control,actor);},_=>{}}
    }
    assert(driver::labels(renamed(r,ts)) =~= e::labels(r,driver::labels(ts))) by {
        assert forall|i:int|0<=i<ts.len() implies driver::labels(renamed(r,ts))[i]==e::labels(r,driver::labels(ts))[i] by {names::label(r,ts[i]);}
    }
}
/// Table values and service keys are unaffected by changing fiber identities.
pub proof fn projection<U>(r:n::Renaming,a:crate::semantics::State<U>)
    requires n::bijective(r),crate::preservation::well_formed(a),
    ensures p::project(n::context(r,a),ISet::full())==p::project(a,ISet::full()),
{
    p::unique_owner(a);n::shaped_forward(r,a);let z=n::context(r,a);
    assert forall|key:Port,x:usize,y:usize|p::owns(z,key,x) && p::owns(z,key,y) implies x==y by {
        assert(p::owns(a,key,(r.backward)(x)) && p::owns(a,key,(r.backward)(y)));
        assert((r.backward)(x)==(r.backward)(y));
        assert((r.forward)((r.backward)(x))==x);assert((r.forward)((r.backward)(y))==y);
    }
    assert(p::project(z,ISet::full()) =~= p::project(a,ISet::full())) by {
        assert forall|key:Port|p::project(z,ISet::full()).dom().contains(key)==p::project(a,ISet::full()).dom().contains(key) by {
            if p::project(z,ISet::full()).dom().contains(key) {
                let owner=choose|owner:usize|p::owns(z,key,owner);assert(p::owns(a,key,(r.backward)(owner)));
            }
            if p::project(a,ISet::full()).dom().contains(key) {
                let owner=choose|owner:usize|p::owns(a,key,owner);n::observations(r,a.control,owner);assert(p::owns(z,key,(r.forward)(owner)));
            }
        }
        assert forall|key:Port|p::project(a,ISet::full()).dom().contains(key) implies p::project(z,ISet::full())[key]==p::project(a,ISet::full())[key] by {
            let owner=choose|owner:usize|p::owns(a,key,owner);n::observations(r,a.control,owner);
            p::lookup(a,ISet::full(),key,owner);p::lookup(z,ISet::full(),key,(r.forward)(owner));
        }
    }
}
impl Plan {
    /// Construct the legal target for the actual prepared transition records.
    /// This includes Insert payloads and each compacted Child choice. It also
    /// includes the runtime shape and synchronous branch consumed by the real
    /// runner's completeness contract. No executable success is assumed.
    pub proof fn source_execution(&self,report:&ScriptReport,bank:Seq<Blueprint>,states:Seq<g::Configuration<u64,Index>>,keep:Seq<bool>,r:region::Region)
        ->(target:Seq<g::Configuration<u64,Index>>)
        requires self.matches(report.transitions@,keep),witness(report,bank,states),mask(report.transitions@,keep,r),region::trace::admissible(states,r),
        ensures driver::replay::path(bank,self.transitions@.map(|_:int,t:Transition|t.command()),target,self.transitions@),
            fs::execution(library(),driver::programs(bank),target,driver::labels(self.transitions@)),
            target.first()==g::empty::<u64,Index>(),a::payloads(self.transitions@,target),shape::trace(bank,target),exact::trace(target,self.transitions@),
            target==e::configurations(self.names.renaming(),f::action_map(f::name_free::<Index>(),self.names.renaming()),region::fresh_trace::target(states,driver::labels(report.transitions@),r)),
            region::trace::settled(states.last(),r) ==> p::project(target.last().state,ISet::full())==p::project(states.last().state,ISet::full()),
    {
        let rho=self.names.renaming();self.names.bijection();
        library_theory();crate::observational_grammar::exact_theory(|_:Port,a:u64,b:u64|a==b,library());
        region::fresh_trace::from_source(|_:Port,a:u64,b:u64|a==b,library(),driver::programs(bank),states,driver::labels(report.transitions@),r);
        let deleted=region::fresh_trace::target(states,driver::labels(report.transitions@),r);
        shape::deleted_trace(bank,states,driver::labels(report.transitions@),r,|t:nat|region::index(states.last().history,r,t));
        shape::renamed_trace(bank,deleted,rho);
        exact::transport::deletion(bank,states,report.transitions@,keep,r);
        exact::transport::renaming(rho,deleted,selected(report.transitions@,keep));
        labels(report.transitions@,keep,r);
        deletion_payloads(report.transitions@,keep,states,r,|t:nat|region::index(states.last().history,r,t));
        rename_payloads(rho,selected(report.transitions@,keep),deleted);
        driver::program_natural(bank);f::name_free_action::<Index>();
        e::natural_from_empty(rho,f::name_free::<Index>(),|_:Port,a:u64,b:u64|a==b,library(),driver::programs(bank),deleted,region::fresh_trace::kept(driver::labels(report.transitions@),r));
        let target=e::configurations(rho,f::action_map(f::name_free::<Index>(),rho),deleted);
        if region::trace::settled(states.last(),r) {
            region::trace::closing_observation(states.last(),r,|t:nat|region::index(states.last().history,r,t));
            p::unique_owner(deleted.last().state);projection(rho,deleted.last().state);
        }
        target
    }
    /// The ordinary runner's completeness contract closes the constructed
    /// source execution to a real replay, including all recorded outcomes.
    pub proof fn replay_result(&self,report:&ScriptReport,bank:Seq<Blueprint>,states:Seq<g::Configuration<u64,Index>>,keep:Seq<bool>,r:region::Region,actual:&ScriptReport)
        requires self.matches(report.transitions@,keep),witness(report,bank,states),mask(report.transitions@,keep,r),region::trace::admissible(states,r),
            actual.machine.wf(),actual.replays(bank,self.transitions@.map(|_:int,t:Transition|t.command())),
        ensures actual.error.is_none(),actual.transitions@==self.transitions@,
            actual.machine.represents(bank,e::configurations(self.names.renaming(),f::action_map(f::name_free::<Index>(),self.names.renaming()),region::fresh_trace::target(states,driver::labels(report.transitions@),r)).last()),
            region::trace::settled(states.last(),r) ==> actual.machine.service_values()==p::project(states.last().state,ISet::full()),
    {
        let target=self.source_execution(report,bank,states,keep,r);
        assert(actual.machine.represents(bank,target.last()));
        driver::replay::well_formed(bank,self.transitions@.map(|_:int,t:Transition|t.command()),target,self.transitions@);
        actual.machine.source_service_values(bank,target.last());
    }

}
}
