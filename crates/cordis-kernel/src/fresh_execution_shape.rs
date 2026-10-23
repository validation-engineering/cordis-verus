//! Runtime shape retained by the actual script witness and region compaction.
//! Source legality alone permits partial active publications. The executable
//! interpreter requires complete active tables and the installed declarations.
use super::FreshDriver;
#[cfg(verus_keep_ghost)]
use crate::{
    alpha as n, closed_region_deletion as region, fresh_equivariance as e, fresh_grammar as f,
    mixed_driver::{self as core, Blueprint, Index},
    mixed_grammar as mx, semantics as s, Phase,
};
use vstd::prelude::*;
verus! {
pub open spec fn configuration(bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>)->bool {
    &&& a.roots.dom()==a.state.control.fibers.dom() && a.state.tables.dom()==a.state.control.fibers.dom()
    &&& s::total_active(a.state)
    &&& forall|actor:usize|s::registered(a.state,actor) ==> {
        let root=a.roots[actor];
        &&& root.blueprint<bank.len() && root.pc==0
        &&& super::forward::declarations(bank,root.blueprint)
        &&& a.state.control.fibers[actor].dependencies==core::ports(bank[root.blueprint as int].dependencies())
        &&& a.state.control.fibers[actor].provisions==core::ports(bank[root.blueprint as int].provisions())
        &&& forall|i:int|0<=i<=root.blueprint ==> bank[i].valid(i as usize)
    }
}
pub proof fn observations(bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,actor:usize)
    requires configuration(bank,a),s::registered(a.state,actor),
    ensures a.roots[actor].blueprint<bank.len(),a.roots[actor].pc==0,
        super::forward::declarations(bank,a.roots[actor].blueprint),
        a.state.control.fibers[actor].dependencies==core::ports(bank[a.roots[actor].blueprint as int].dependencies()),
        a.state.control.fibers[actor].provisions==core::ports(bank[a.roots[actor].blueprint as int].provisions()),
        forall|i:int|0<=i<=a.roots[actor].blueprint ==> bank[i].valid(i as usize),
        a.state.control.fibers[actor].phase==Phase::Active ==> a.state.tables[actor].dom()==a.state.control.fibers[actor].provisions,
{ }
pub open spec fn trace(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>)->bool {
    forall|i:int|0<=i<states.len() ==> configuration(bank,states[i])
}
impl FreshDriver {
    pub proof fn source_runtime_shape(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>)
        requires self.wf(),self.unique_declarations(),self.represents(bank,a),
        ensures configuration(bank,a),
    {
        self.inner.paper_total(a.state);
        assert(a.state.tables.dom() =~= a.state.control.fibers.dom());
        assert forall|actor:usize|s::registered(a.state,actor) implies {
            let root=a.roots[actor];
            &&& root.blueprint<bank.len() && root.pc==0
            &&& super::forward::declarations(bank,root.blueprint)
            &&& a.state.control.fibers[actor].dependencies==core::ports(bank[root.blueprint as int].dependencies())
            &&& a.state.control.fibers[actor].provisions==core::ports(bank[root.blueprint as int].provisions())
            &&& forall|i:int|0<=i<=root.blueprint ==> bank[i].valid(i as usize)
        } by {
            let bp=self.inner.rows[actor as int].blueprint;
            assert(self.inner.layout(actor as int));assert(self.inner.bank_valid(bp));
            assert(self.inner.blueprints[bp as int].same(&bank[bp as int]));
            assert forall|i:int|0<=i<=bp implies bank[i].valid(i as usize) by {
                assert(self.inner.blueprints[i].valid(i as usize));assert(self.inner.blueprints[i].same(&bank[i]));
            }
        }
    }
}
pub proof fn append(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,z:mx::Configuration<u64,Index>)
    requires trace(bank,states),configuration(bank,z),
    ensures trace(bank,states.push(z)),
{assert forall|i:int|0<=i<states.push(z).len() implies configuration(bank,states.push(z)[i]) by {
    if i<states.len() {assert(configuration(bank,states[i]));}else {assert(i==states.len());}
}}
pub proof fn deletion(bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,region:region::Region,rho:spec_fn(nat)->nat)
    requires configuration(bank,a),
    ensures configuration(bank,region::configuration(a,region,rho)),
{
    let z=region::configuration(a,region,rho);
    assert(z.roots.dom() =~= z.state.control.fibers.dom());
    assert(z.state.tables.dom() =~= z.state.control.fibers.dom());
    assert forall|actor:usize|s::registered(z.state,actor) && z.state.control.fibers[actor].phase==Phase::Active
        implies z.state.tables[actor].dom()==z.state.control.fibers[actor].provisions by {
        assert(!region.episodes.contains(actor));assert(s::registered(a.state,actor));
    }
    assert forall|actor:usize|s::registered(z.state,actor) implies {
        let root=z.roots[actor];
        &&& root.blueprint<bank.len() && root.pc==0
        &&& super::forward::declarations(bank,root.blueprint)
        &&& z.state.control.fibers[actor].dependencies==core::ports(bank[root.blueprint as int].dependencies())
        &&& z.state.control.fibers[actor].provisions==core::ports(bank[root.blueprint as int].provisions())
        &&& forall|i:int|0<=i<=root.blueprint ==> bank[i].valid(i as usize)
    } by {assert(s::registered(a.state,actor));}
}
pub proof fn renaming(bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,rho:n::Renaming)
    requires configuration(bank,a),n::bijective(rho),
    ensures configuration(bank,f::configuration(rho,f::action_map(f::name_free::<Index>(),rho),a)),
{
    let z=f::configuration(rho,f::action_map(f::name_free::<Index>(),rho),a);
    assert(z.roots.dom() =~= z.state.control.fibers.dom());
    assert(z.state.tables.dom() =~= z.state.control.fibers.dom());
    assert forall|actor:usize|s::registered(z.state,actor) && z.state.control.fibers[actor].phase==Phase::Active
        implies z.state.tables[actor].dom()==z.state.control.fibers[actor].provisions by {
        let prior=(rho.backward)(actor);n::observations(rho,a.state.control,prior);assert(s::registered(a.state,prior));
    }
    assert forall|actor:usize|s::registered(z.state,actor) implies {
        let root=z.roots[actor];
        &&& root.blueprint<bank.len() && root.pc==0
        &&& super::forward::declarations(bank,root.blueprint)
        &&& z.state.control.fibers[actor].dependencies==core::ports(bank[root.blueprint as int].dependencies())
        &&& z.state.control.fibers[actor].provisions==core::ports(bank[root.blueprint as int].provisions())
        &&& forall|i:int|0<=i<=root.blueprint ==> bank[i].valid(i as usize)
    } by {
        let prior=(rho.backward)(actor);n::observations(rho,a.state.control,prior);assert(s::registered(a.state,prior));
        assert(z.roots[actor]==a.roots[prior]);
    }
}
pub proof fn deleted_trace(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,labels:Seq<crate::fresh_semantics::Label>,region:region::Region,rho:spec_fn(nat)->nat)
    requires trace(bank,states),states.len()==labels.len()+1,
    ensures trace(bank,region::fresh_trace::delete(states,labels,region,rho)),
    decreases labels.len(),
{
    if labels.len()>0 {
        deleted_trace(bank,states.drop_last(),labels.drop_last(),region,rho);
        if region.keep(labels.last().0,labels.last().1) {
            deletion(bank,states.last(),region,rho);
            append(bank,region::fresh_trace::delete(states.drop_last(),labels.drop_last(),region,rho),region::configuration(states.last(),region,rho));
        }
    } else {deletion(bank,states.first(),region,rho);}
}
pub proof fn renamed_trace(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,rho:n::Renaming)
    requires trace(bank,states),n::bijective(rho),
    ensures trace(bank,e::configurations(rho,f::action_map(f::name_free::<Index>(),rho),states)),
{
    assert forall|i:int|0<=i<states.len() implies configuration(bank,e::configurations(rho,f::action_map(f::name_free::<Index>(),rho),states)[i]) by {
        renaming(bank,states[i],rho);
    }
}
}
