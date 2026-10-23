//! Forward source admission from retained runtime shape and finite allocation limits.
use super::FreshDriver;
#[cfg(verus_keep_ghost)]
use crate::{
    fresh_grammar as f, fresh_semantics as fs,
    mixed_driver::fresh::{self as driver, programs},
    mixed_driver::{self as core, Blueprint, Index, Instruction},
    mixed_grammar as mx, refinement as r, semantics as s, Phase,
};
use vstd::prelude::*;
verus! {
pub open spec fn declarations(bank:Seq<Blueprint>,blueprint:usize)->bool {
    blueprint<bank.len() && crate::distinct_ports(bank[blueprint as int].dependencies())
        && crate::distinct_ports(bank[blueprint as int].provisions())
}
impl FreshDriver {
    pub proof fn source_insert_admission(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,z:mx::Configuration<u64,Index>,actor:usize,parent:Option<usize>,blueprint:usize)
        requires self.wf(),self.represents(bank,a),fs::step(core::library(),programs(bank),a,z,actor,r::Rule::Insert,None),
            driver::allocation::payload(core::Transition::Insert {actor,parent,blueprint},z),
            super::shape::configuration(bank,z),self.next_id()<usize::MAX,
        ensures self.insertion_enabled(parent,blueprint),
    {
        self.inner.reified_insertion_domain(parent,blueprint);
        self.inner.kernel.paper_insert_domain(parent,self.inner.blueprints[blueprint as int].dependencies(),self.inner.blueprints[blueprint as int].provisions());
        r::insertion_has_domain(a.state.control,z.state.control,actor);
        super::shape::observations(bank,z,actor);
        assert(z.roots[actor]==(Index {blueprint,pc:0}));
        assert(forall|i:int|0<=i<=z.roots[actor].blueprint ==> bank[i].valid(i as usize));
        assert(z.state.control.fibers[actor].provisions==core::ports(bank[blueprint as int].provisions()));
        assert(self.inner.blueprints[blueprint as int].same(&bank[blueprint as int]));
        assert(self.inner.bank_valid(blueprint)) by {
            assert forall|i:int|0<=i<=blueprint implies self.inner.blueprints[i].valid(i as usize) by {
                assert(bank[i].valid(i as usize));assert(self.inner.blueprints[i].same(&bank[i]));
            }
        }
        assert(self.inner.kernel.next_id()==self.next_id());
        assert(crate::distinct_ports(self.inner.blueprints[blueprint as int].dependencies()));
        assert(crate::distinct_ports(self.inner.blueprints[blueprint as int].provisions()));
        assert(r::insertion_domain(self.control(),parent,core::ports(self.inner.blueprints[blueprint as int].provisions())));
    }
    /// The remaining premise is the finite allocation limit;
    /// source evaluation and complete publication establish the value checks.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    pub proof fn source_step_admission(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,z:mx::Configuration<u64,Index>,actor:usize,rule:r::Rule,choice:Option<usize>)
        requires self.wf(),self.represents(bank,a),fs::well_formed(core::library(),programs(bank),a),
            fs::step(core::library(),programs(bank),a,z,actor,rule,choice),rule==r::Rule::Iter || rule==r::Rule::Finish,
            super::shape::configuration(bank,z),
            choice.is_some() ==> choice.unwrap()==self.next_id() && self.next_id()<usize::MAX,
        ensures self.step_enabled(actor),
    {
        let current=a.current[actor].unwrap();let blueprint=self.inner.rows[actor as int].blueprint;
        let pc=self.inner.rows[actor as int].current.unwrap();
        self.inner.row_bounds(actor);
        assert(current==(Index {blueprint,pc}));
        let template=self.inner.installed_instruction(actor);let instruction=self.selected_instruction(actor);
        assert(self.inner.blueprints[blueprint as int].same(&bank[blueprint as int]));
        assert(template.valid(pc,self.inner.blueprints[blueprint as int].code.len(),blueprint,self.inner.blueprints[blueprint as int].dependencies(),self.inner.blueprints[blueprint as int].provisions()));
        match template {Instruction::Child {..}=>{assert(choice==Some(self.inner.rows.len()));},_=>{assert(choice.is_none());}}
        driver::instantiate_instruction(bank,blueprint,template,self.inner.rows.len());
        core::instruction_bank(self.inner.blueprints@,bank,blueprint,instruction);
        assert(f::instantiate(programs(bank)(actor)(current),choice)==Some(core::instruction_node(self.inner.blueprints@,blueprint,instruction)));
        core::run_payload(self.inner.blueprints@,blueprint,instruction,self.inner.primitive_state(),a.state,actor);
        self.inner.paper_total(a.state);s::total_targets_agree(a.state,actor,a.state.control.fibers[actor].committed);
        assert(self.inner.ready(actor));
        let y=mx::run(core::library(),core::instruction_node(self.inner.blueprints@,blueprint,instruction),self.inner.primitive_state(),actor).unwrap();
        assert(mx::run(core::library(),core::instruction_node(self.inner.blueprints@,blueprint,instruction),self.inner.primitive_state(),actor).is_some());
        if let Instruction::Child {blueprint:child,..}=instruction {
            super::shape::observations(bank,z,choice.unwrap());
            assert(z.roots[choice.unwrap()]==(Index {blueprint:child,pc:0}));
            assert(declarations(bank,child));
            assert(self.inner.bank_valid(child)) by {
                assert(child<blueprint);
                assert forall|i:int|0<=i<=child implies self.inner.blueprints[i].valid(i as usize) by {assert(self.inner.blueprints[i].valid(i as usize));}
            }
            assert(self.inner.blueprints[child as int].same(&bank[child as int]));
        }
        self.primitive_admission(actor,blueprint,instruction);
        if instruction.continuation().is_none() {
            assert(rule==r::Rule::Finish);assert(z.state.control.fibers[actor].phase==Phase::Active);
            super::shape::observations(bank,z,actor);
            assert(z.state.tables[actor].dom()==z.state.control.fibers[actor].provisions);
            assert(y.state.tables[actor].dom()==self.control().fibers[actor].provisions);
            self.complete_admission(actor,blueprint,instruction);
        }
    }
    #[verifier::spinoff_prover]
    proof fn primitive_admission(&self,actor:usize,blueprint:usize,instruction:Instruction)
        requires self.wf(),r::registered(self.control(),actor),
            mx::run(core::library(),core::instruction_node(self.inner.blueprints@,blueprint,instruction),self.inner.primitive_state(),actor).is_some(),
            match instruction {Instruction::Child {expected,blueprint:child,..}=>expected==self.next_id() && self.next_id()<usize::MAX
                && self.inner.bank_valid(child) && declarations(self.inner.blueprints@,child),_=>true},
        ensures self.inner.primitive_enabled(actor,instruction),
    {
        match instruction {
            Instruction::Provide {key,..}=>{self.inner.table_declaration(actor,key);},
            Instruction::Child {blueprint:child,..}=>{
                self.inner.kernel.paper_insert_domain(Some(actor),self.inner.blueprints[child as int].dependencies(),self.inner.blueprints[child as int].provisions());
                assert(r::insertion_domain(self.control(),Some(actor),core::ports(self.inner.blueprints[child as int].provisions())));
            },_=>{},
        }
    }
    #[verifier::spinoff_prover]
    proof fn complete_admission(&self,actor:usize,blueprint:usize,instruction:Instruction)
        requires self.wf(),r::registered(self.control(),actor),
            mx::run(core::library(),core::instruction_node(self.inner.blueprints@,blueprint,instruction),self.inner.primitive_state(),actor).is_some(),
            mx::run(core::library(),core::instruction_node(self.inner.blueprints@,blueprint,instruction),self.inner.primitive_state(),actor).unwrap().state.tables[actor].dom()==self.control().fibers[actor].provisions,
        ensures self.inner.complete_after(actor,instruction),
    {
        let y=mx::run(core::library(),core::instruction_node(self.inner.blueprints@,blueprint,instruction),self.inner.primitive_state(),actor).unwrap();
        assert forall|i:int|0<=i<self.inner.tables[actor as int].view().len() implies
            self.inner.tables[actor as int].view()[i].value.is_some()
                || match instruction {Instruction::Provide {key,..}=>self.inner.tables[actor as int].view()[i].key==key,_=>false} by {
            let key=self.inner.tables[actor as int].view()[i].key;
            self.inner.table_declaration(actor,key);
            assert(self.inner.tables[actor as int].find(key)==Some(i as usize));
            assert(self.control().fibers[actor].provisions.contains(key));
            assert(y.state.tables[actor].dom().contains(key));
            match instruction {Instruction::Unit=>{},Instruction::Provide {..}=>{},Instruction::Xor {..}=>{},Instruction::Child {..}=>{}}
        }
    }

}
}
