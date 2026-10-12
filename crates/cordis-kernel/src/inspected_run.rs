//! A caller that constructs the R1 certificate from actual execution.
//! No source state, successful-call assumption or recovery witness is an input.
use super::{run_script, Blueprint, Command, ScriptReport};
#[cfg(verus_keep_ghost)]
use crate::{
    fresh_semantics as fs, guarded_components as c,
    mixed_driver::{context, Index},
    mixed_grammar as m, refinement as r,
};
use crate::{mixed_driver::Receipt, Port};
use vstd::prelude::*;

verus! {

pub struct InspectedReport {
    pub run:ScriptReport,
    pub value:Option<u64>,
    pub inverse:Option<Receipt>,
}
impl InspectedReport {
    pub closed spec fn certified(&self,bank:Seq<crate::mixed_driver::Blueprint>,actor:usize,key:Port,index:usize)->bool {
        let machine=&self.run.machine;let view=machine.reified();
        &&& self.run.refines(bank)
        &&& self.value==context::read(view,actor,key)
        &&& self.inverse==if r::registered(view.control,actor) && index<machine.journal(actor).len() {Some(machine.journal(actor)[index as int])} else {None}
        &&& forall|n:usize| r::registered(view.control,n) ==> c::component(crate::mixed_driver::library(),super::programs(view.bank),n,
            view.control.fibers[n].dependencies.union(view.control.fibers[n].provisions),view.control.fibers[n].provisions,view.roots[n])
        &&& exists|states:Seq<m::Configuration<u64,Index>>| {
            &&& fs::execution(crate::mixed_driver::library(),super::programs(bank),states,super::labels(self.run.transitions@))
            &&& states.first()==m::empty::<u64,Index>()
            &&& context::interprets(view,bank,states.last())
        }
    }
}

/// Includes failure reports: the successfully executed prefix has the same
/// value and function interpretation, and the first failed command stays Err.
pub fn run_inspected(blueprints:Vec<Blueprint>,commands:&[Command],actor:usize,key:Port,index:usize)->(out:InspectedReport)
    ensures out.run.machine.wf(),
        out.certified(blueprints@.map(|_:int,bp:Blueprint|bp.compiled()),actor,key,index),
        out.run.error.is_none() ==> out.run.transitions.len()==commands.len(),
        out.run.error.is_some() ==> out.run.transitions.len()<commands.len(),
{
    let ghost bank=blueprints@.map(|_:int,bp:Blueprint|bp.compiled());
    let run=run_script(blueprints,commands);
    proof {
        let states=run.source_execution(bank);
        run.machine.reified_representation(bank,states.last());
        let view=run.machine.reified();
        assert forall|n:usize| r::registered(view.control,n) implies c::component(crate::mixed_driver::library(),super::programs(view.bank),n,
            view.control.fibers[n].dependencies.union(view.control.fibers[n].provisions),view.control.fibers[n].provisions,view.roots[n]) by {
            run.machine.root_component(n);
        }
    }
    let value=run.machine.read(actor,key);
    let inverse=run.machine.inverse_at(actor,index);
    InspectedReport {run,value,inverse}
}

} // verus!
