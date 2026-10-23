//! Complete input domains of the real Fresh command dispatcher.
//! These predicates describe checks on the input machine, not successful calls.
#[cfg(verus_keep_ghost)]
use super::Command;
use super::FreshDriver;
#[cfg(verus_keep_ghost)]
use crate::{mixed_driver as core, mixed_grammar as mx, refinement as r, semantics as s, Phase};
use vstd::prelude::*;
verus! {
/// Each concrete inverse preserves registration and phase. Child inverses
/// retire their captured child; they do not erase it or alter its lifecycle.
pub proof fn restore_control_frame(receipts:Seq<core::Receipt>,a:s::State<u64>)
    requires core::restore_receipts(receipts,a).is_some(),
    ensures core::restore_receipts(receipts,a).unwrap().control.fibers.dom()==a.control.fibers.dom(),
        forall|n:usize|r::registered(a.control,n) ==> core::restore_receipts(receipts,a).unwrap().control.fibers[n].phase==a.control.fibers[n].phase,
    decreases receipts.len(),
{
    if receipts.len()>0 {
        let receipt=receipts.last();let b=mx::undo(receipt.model(),a).unwrap();
        match receipt.inverse {core::Inverse::Unit=>{},core::Inverse::Provision {..}=>{},core::Inverse::Xor {..}=>{},core::Inverse::Child {..}=>{}}
        assert(b.control.fibers.dom()==a.control.fibers.dom());
        assert forall|n:usize|r::registered(a.control,n) implies b.control.fibers[n].phase==a.control.fibers[n].phase by { }
        restore_control_frame(receipts.drop_last(),b);
        assert forall|n:usize|r::registered(a.control,n) implies core::restore_receipts(receipts,a).unwrap().control.fibers[n].phase==a.control.fibers[n].phase by {
            assert(r::registered(b.control,n));
            assert(core::restore_receipts(receipts.drop_last(),b).unwrap().control.fibers[n].phase==b.control.fibers[n].phase);
        }
    }
}
pub proof fn primitive_control_frame(bank:Seq<core::Blueprint>,blueprint:usize,instruction:core::Instruction,a:s::State<u64>,actor:usize)
    requires mx::run(core::library(),core::instruction_node(bank,blueprint,instruction),a,actor).is_some(),
    ensures {
        let z=mx::run(core::library(),core::instruction_node(bank,blueprint,instruction),a,actor).unwrap().state;
        &&& forall|n:usize|r::registered(a.control,n) ==> r::registered(z.control,n) && z.control.fibers[n].phase==a.control.fibers[n].phase
        &&& forall|n:usize|r::registered(z.control,n) && !r::registered(a.control,n) ==> match instruction {
            core::Instruction::Child {expected,..}=>n==expected && z.control.fibers[n].phase==Phase::Inactive,_=>false}
    },
{match instruction {core::Instruction::Unit=>{},core::Instruction::Provide {..}=>{},core::Instruction::Xor {..}=>{},core::Instruction::Child {..}=>{}}}

impl FreshDriver {
    pub proof fn same_quiescent_journals(&self,other:&Self)
        requires self.wf(),other.wf(),self.same(other),other.quiescent_journals(),
        ensures self.quiescent_journals(),
    {self.inner.kernel.unchanged_observations(&other.inner.kernel);}

    pub open spec fn depart_enabled(&self,actor:usize)->bool {
        r::registered(self.control(),actor)
            && (self.control().fibers[actor].phase==Phase::Loading || self.control().fibers[actor].phase==Phase::Active)
            && !r::coherent(self.control(),actor)
    }
    pub open spec fn command_enabled(&self,command:Command)->bool {
        match command {
            Command::Insert {parent,blueprint}=>self.insertion_enabled(parent,blueprint),
            Command::Begin {actor}=>self.begin_enabled(actor),
            Command::Step {actor}=>self.step_enabled(actor),
            Command::Retire {actor}=>r::registered(self.control(),actor),
            Command::Depart {actor}=>self.depart_enabled(actor),
            Command::Unload {actor}=>self.unload_enabled(actor),
            Command::Remove {actor}=>self.remove_enabled(actor),
        }
    }
    pub proof fn same_command_domain(&self,other:&Self,command:Command)
        requires self.wf(),other.wf(),self.same(other),
        ensures self.command_enabled(command)==other.command_enabled(command),
    {
        self.inner.kernel.unchanged_observations(&other.inner.kernel);
        match command {
            Command::Insert {parent,blueprint}=>self.same_start_domains(other,parent,blueprint,0),
            Command::Begin {actor}=>self.same_start_domains(other,None,0,actor),
            Command::Step {actor}=>self.same_step_domain(other,actor),
            Command::Unload {actor}=>self.same_unload_domain(other,actor),
            Command::Remove {actor}=>{
                reveal(crate::Kernel::removal_enabled);
                self.inner.same_primitive_state(&other.inner);
                assert(self.inner.unreferenced(actor)==other.inner.unreferenced(actor));
            },
            _=>{},
        }
    }
}
}

#[path = "fresh_dispatch_source.rs"]
pub mod source;

#[path = "fresh_execution_shape.rs"]
pub mod shape;

#[path = "fresh_dispatch_step.rs"]
pub mod forward;

#[path = "fresh_dispatch_exact.rs"]
pub mod exact;

#[path = "fresh_runtime_metadata.rs"]
pub mod metadata;
