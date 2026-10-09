//! Dynamic child allocation over the same verified tables and mixed journal.
//!
//! The installed template contains a binder, not an expected child identity.
//! Each actual Child instruction reads the current allocator immediately before
//! insertion. Shared execution, inverse and transaction primitives live in the
//! parent module; old receipts retain their captured identity.
#[cfg(verus_keep_ghost)]
use super::Receipt;
pub use super::{Command, Departure, DriverError, Index, Outcome, Transition};
use super::{Inverse, MixedDriver};
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, fresh_grammar as fg, fresh_semantics as fs, mixed_grammar as mx,
    observational_grammar as og, refinement as r, semantics as s,
};
use crate::{Phase, Port};
use vstd::prelude::*;

verus! {

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Instruction {
    Unit,
    Provide {key:Port,value:u64,next:Option<usize>},
    Xor {key:Port,mask:u64,next:Option<usize>},
    Child {blueprint:usize,next:Option<usize>},
}
impl Instruction {
    pub open spec fn compiled(&self)->super::Instruction {
        match *self {
            Self::Unit=>super::Instruction::Unit,
            Self::Provide {key,value,next}=>super::Instruction::Provide {key,value,next},
            Self::Xor {key,mask,next}=>super::Instruction::Xor {key,mask,next},
            Self::Child {blueprint,next}=>super::Instruction::Child {expected:0,blueprint,next},
        }
    }
    fn compile(self)->(out:super::Instruction) ensures out==self.compiled(), {
        match self {
            Self::Unit=>super::Instruction::Unit,
            Self::Provide {key,value,next}=>super::Instruction::Provide {key,value,next},
            Self::Xor {key,mask,next}=>super::Instruction::Xor {key,mask,next},
            Self::Child {blueprint,next}=>super::Instruction::Child {expected:0,blueprint,next},
        }
    }
}
pub struct Blueprint {inner:super::Blueprint}
impl Blueprint {
    pub closed spec fn compiled(&self)->super::Blueprint {self.inner}
    pub fn new(dependencies:Vec<Port>,provisions:Vec<Port>,code:Vec<Instruction>)->(out:Self)
        ensures out.compiled().dependencies()==dependencies@,out.compiled().provisions()==provisions@,
            out.compiled().code()==code@.map(|_:int,instruction:Instruction|instruction.compiled()),
    {
        let mut compiled:Vec<super::Instruction>=Vec::new();let mut i=0;
        while i<code.len()
            invariant i<=code.len(),compiled.len()==i,forall|j:int|0<=j<i ==> compiled[j]==code[j].compiled(),
            decreases code.len()-i,
        {compiled.push(code[i].compile());i+=1;}
        assert(compiled@ =~= code@.map(|_:int,instruction:Instruction|instruction.compiled()));
        Self {inner:super::Blueprint::new(dependencies,provisions,compiled)}
    }
}

pub open spec fn instruction_node(bank:Seq<super::Blueprint>,blueprint:usize,instruction:super::Instruction)->fg::Node<Port,u64,u64,(),Index> {
    match instruction {
        super::Instruction::Unit=>fg::Node::Dependent {node:d::Node::Unit},
        super::Instruction::Provide {key,value,next}=>fg::Node::Dependent {node:d::Node::Provision {key,value,next:super::continuation(blueprint,next)}},
        super::Instruction::Xor {key,mask,next}=>fg::Node::Dependent {node:d::Node::Operation {operation:key,argument:mask,select:|_:()|super::continuation(blueprint,next)}},
        super::Instruction::Child {blueprint:child,next,..}=>fg::Node::FreshChild {
            dependencies:super::ports(bank[child as int].dependencies()),provisions:super::ports(bank[child as int].provisions()),
            body:|_:usize|(Index {blueprint:child,pc:0},super::continuation(blueprint,next))},
    }
}
pub open spec fn programs(bank:Seq<super::Blueprint>)->fg::Programs<Port,u64,u64,(),Index> {
    |_:usize| |id:Index|instruction_node(bank,id.blueprint,
        if id.blueprint<bank.len() && id.pc<bank[id.blueprint as int].code().len() {bank[id.blueprint as int].code()[id.pc as int]} else {super::Instruction::Unit})
}
/// The compiled family contains no fiber names in its continuation indices.
/// Its binder accepts the allocated identity while keeping the same installed code.
pub proof fn program_natural(bank:Seq<super::Blueprint>)
    ensures fg::natural(fg::name_free::<Index>(),programs(bank)),
{
    let action=fg::name_free::<Index>();let ps=programs(bank);
    assert forall|rho:crate::alpha::Renaming,actor:usize,id:Index,selected:Option<usize>|crate::alpha::bijective(rho) implies
        #[trigger] fg::instantiate(ps((rho.forward)(actor))((action.apply)(rho,id)),crate::alpha::parent(rho,selected))
            ==fg::instantiate(fg::node(rho,fg::action_map(action,rho),ps(actor)(id)),crate::alpha::parent(rho,selected)) by {
        let h=fg::action_map(action,rho);
        let instruction=if id.blueprint<bank.len() && id.pc<bank[id.blueprint as int].code().len() {bank[id.blueprint as int].code()[id.pc as int]} else {super::Instruction::Unit};
        let original=instruction_node(bank,id.blueprint,instruction);
        assert(ps(actor)(id)==original);
        match original {
            fg::Node::Dependent {node:d::Node::Operation {select,..}}=>{
                assert((|b:()|fg::next(h,select(b))) =~= select);
            },
            fg::Node::FreshChild {body,..}=>{
                assert((|child:usize| {let prior=body((rho.backward)(child));((h.forward)(prior.0),fg::next(h,prior.1))}) =~= body);
            },_=>{},
        }
        assert(fg::node(rho,h,original)==original);
    }
}
pub open spec fn choice(outcome:Outcome)->Option<usize> {
    match outcome {Outcome::Child {child,..}=>Some(child),_=>None}
}
pub proof fn instantiate_instruction(bank:Seq<super::Blueprint>,blueprint:usize,instruction:super::Instruction,allocation:usize)
    ensures {
        let concrete=match instruction {super::Instruction::Child {blueprint,next,..}=>super::Instruction::Child {expected:allocation,blueprint,next},_=>instruction};
        let selected=match instruction {super::Instruction::Child {..}=>Some(allocation),_=>None};
        fg::instantiate(instruction_node(bank,blueprint,instruction),selected)==Some(super::instruction_node(bank,blueprint,concrete))
    },
{match instruction {super::Instruction::Child {..}=>{},_=>{}}}

/// Instantiate only the child identity; the installed blueprint and
/// continuation remain part of the original instruction.
fn instantiate_template(draft:&MixedDriver,template:super::Instruction)->(out:super::Instruction)
    ensures out==match template {
        super::Instruction::Child {blueprint:child_blueprint,next:child_next,..}=>super::Instruction::Child {
            expected:draft.rows.len(),blueprint:child_blueprint,next:child_next,
        },
        _=>template,
    },
{
    match template {
        super::Instruction::Child {blueprint,next,..}=>super::Instruction::Child {expected:draft.rows.len(),blueprint,next},
        _=>template,
    }
}

/// Expose the receipt kind and acting fiber frame needed by commit_landing.
/// The wrapper can then compose execution contracts without unfolding the
/// table operation or rechecking its captured provider in the same query.
#[verifier::spinoff_prover]
proof fn instruction_receipt_metadata(bank:Seq<super::Blueprint>,blueprint:usize,instruction:super::Instruction,
    a:s::State<u64>,actor:usize,receipt:Receipt)
    requires mx::run(super::library(),super::instruction_node(bank,blueprint,instruction),a,actor).is_some(),
        receipt.model()==mx::run(super::library(),super::instruction_node(bank,blueprint,instruction),a,actor).unwrap().receipt,
    ensures (match receipt.inverse {super::Inverse::Child {child}=>Some(child),_=>None})
        ==match instruction {super::Instruction::Child {expected,..}=>Some(expected),_=>None},
        s::registered(mx::run(super::library(),super::instruction_node(bank,blueprint,instruction),a,actor).unwrap().state,actor),
        mx::run(super::library(),super::instruction_node(bank,blueprint,instruction),a,actor).unwrap().state.control.fibers[actor]
            ==a.control.fibers[actor],
{
    match instruction {
        super::Instruction::Child {expected,..}=>{
            assert(!r::registered(a.control,expected));
            assert(expected!=actor);
        },
        _=>{},
    }
}

pub struct FreshDriver {inner:super::MixedDriver}
impl FreshDriver {
    pub closed spec fn control(&self)->r::State {self.inner.control()}
    pub closed spec fn ack(&self,after:&Self,actor:usize,rule:r::Rule,selected:Option<usize>)->bool {self.inner.fresh_ack(&after.inner,actor,rule,selected)}
    pub closed spec fn wf(&self)->bool {self.inner.wf()}
    pub closed spec fn same(&self,other:&Self)->bool {self.inner.same(&other.inner)}
    pub closed spec fn journal(&self,actor:usize)->Seq<super::Receipt> {self.inner.journal(actor)}
    pub closed spec fn next_id(&self)->nat {self.inner.rows.len() as nat}
    /// Preserve the concrete insertion checks, including the full valid bank prefix.
    pub closed spec fn insertion_enabled(&self,parent:Option<usize>,blueprint:usize)->bool {
        self.inner.insertion_enabled(parent,blueprint)
    }
    /// Guarded cleanup and the exact inverse domain of the retained journal.
    pub closed spec fn unload_enabled(&self,actor:usize)->bool {self.inner.unload_enabled(actor)}
    pub proof fn same_unload_domain(&self,other:&Self,actor:usize)
        requires self.wf(),other.wf(),self.same(other),
        ensures self.unload_enabled(actor)==other.unload_enabled(actor),
    {self.inner.same_unload_domain(&other.inner,actor);}
    /// Classify the actual remaining inverse journal, not all installed code.
    pub closed spec fn unit_child_journal(&self,actor:usize)->bool {self.inner.unit_child_journal(actor)}
    pub closed spec fn cleanup_permitted(&self,actor:usize)->bool {self.inner.cleanup_permitted(actor)}
    pub closed spec fn unit_child_recovery(&self)->bool {self.inner.unit_child_recovery()}
    /// The existing real source execution supplies current retention, rather
    /// than an assumption that this actor's inverse sequence will succeed.
    pub proof fn unit_child_recovery_from_source(&self,bank:Seq<super::Blueprint>,a:mx::Configuration<u64,Index>)
        requires self.wf(),self.represents(bank,a),fs::well_formed(super::library(),programs(bank),a),
        ensures self.unit_child_recovery(),
    {self.inner.unit_child_recovery_from_source(bank,a);}
    pub proof fn unit_child_unload_domain(&self,actor:usize)
        requires self.wf(),self.unit_child_recovery(),self.unit_child_journal(actor),
        ensures self.unload_enabled(actor)==self.cleanup_permitted(actor),
    {self.inner.unit_child_unload_domain(actor);}
    /// Starting an episode also requires an empty retained journal. The kernel
    /// predicate includes target availability and its bounded generation counter.
    pub closed spec fn begin_enabled(&self,id:usize)->bool {
        r::registered(self.control(),id) && id<self.inner.rows.len()
            && self.inner.rows[id as int].journal.len()==0 && self.inner.kernel.begin_enabled(id)
    }
    proof fn same_begin_check(left:&crate::Kernel,right:&crate::Kernel,id:usize)
        requires left.wf(),right.wf(),left.unchanged(right),
        ensures left.begin_enabled(id)==right.begin_enabled(id),
    {
        left.unchanged_observations(right);
        left.paper_observations(id);right.paper_observations(id);
        if left.registered(id) {left.generation_frame(right,id);}
        reveal(crate::Kernel::begin_enabled);
        reveal(crate::Kernel::unavailable);
        reveal(crate::Kernel::has_provider);
        reveal(crate::Kernel::active_provider);
        reveal(crate::Kernel::unchanged);
    }
    pub proof fn same_start_domains(&self,other:&Self,parent:Option<usize>,blueprint:usize,id:usize)
        requires self.wf(),other.wf(),self.same(other),
        ensures self.insertion_enabled(parent,blueprint)==other.insertion_enabled(parent,blueprint),
            self.begin_enabled(id)==other.begin_enabled(id),
    {
        self.inner.same_insertion_domain(&other.inner,parent,blueprint);
        Self::same_begin_check(&self.inner.kernel,&other.inner.kernel,id);
        self.inner.kernel.unchanged_observations(&other.inner.kernel);
    }
    pub proof fn same_step_domain(&self,other:&Self,actor:usize)
        requires self.wf(),other.wf(),self.same(other),
        ensures self.step_enabled(actor)==other.step_enabled(actor),
    {
        self.inner.same_domains(&other.inner,actor,self.selected_instruction(actor));
        if self.inner.ready(actor) {
            assert(self.selected_instruction(actor)==other.selected_instruction(actor));
        }
    }
    /// The runtime selects a fresh identity at this step, while retaining the
    /// installed child blueprint and continuation.
    pub closed spec fn selected_instruction(&self,actor:usize)->super::Instruction {
        match self.inner.installed_instruction(actor) {
            super::Instruction::Child {blueprint,next,..}=>super::Instruction::Child {
                expected:self.inner.rows.len(),blueprint,next,
            },
            instruction=>instruction,
        }
    }
    /// Exact synchronous step domain. Fresh allocation does not bypass value,
    /// child registration, or terminal provision requirements.
    pub closed spec fn step_enabled(&self,actor:usize)->bool {
        self.inner.ready(actor) && self.inner.instruction_enabled(actor,self.selected_instruction(actor))
    }
    /// Remaining forward positions plus the possible terminal Unit call.
    /// An invalid/missing position still allows one real call to report its error.
    pub closed spec fn run_budget(&self,actor:usize)->nat {
        if actor<self.inner.rows.len() {
            let row=self.inner.rows[actor as int];
            if row.blueprint<self.inner.blueprints.len() && row.current.is_some()
                && row.current.unwrap()<=self.inner.blueprints[row.blueprint as int].code().len() {
                (self.inner.blueprints[row.blueprint as int].code().len()-row.current.unwrap()) as nat+1
            } else {1}
        } else {1}
    }
    pub closed spec fn run_finished(&self,actor:usize)->bool {
        r::registered(self.control(),actor) && self.control().fibers[actor].phase==Phase::Active
            && actor<self.inner.rows.len() && self.inner.rows[actor as int].current.is_none()
    }
    pub proof fn run_budget_bounds(&self,actor:usize)
        requires self.wf(),
        ensures 1<=self.run_budget(actor)<=usize::MAX as nat+1,
    { }
    pub closed spec fn bank(&self)->Seq<super::Blueprint> {self.inner.blueprints@}
    pub closed spec fn represents(&self,bank:Seq<super::Blueprint>,a:mx::Configuration<u64,Index>)->bool {self.inner.represents(bank,a)}
    pub fn new(blueprints:Vec<Blueprint>)->(out:Self)
        ensures out.wf(),out.represents(out.bank(),mx::empty()),
            super::bank_same(out.bank(),blueprints@.map(|_:int,bp:Blueprint|bp.compiled())),
            out.represents(blueprints@.map(|_:int,bp:Blueprint|bp.compiled()),mx::empty()),
    {
        let mut compiled:Vec<super::Blueprint>=Vec::new();let mut i=0;
        while i<blueprints.len()
            invariant i<=blueprints.len(),compiled.len()==i,forall|j:int|0<=j<i ==> compiled[j].same(&blueprints[j].inner),
            decreases blueprints.len()-i,
        {compiled.push(blueprints[i].inner.duplicate());i+=1;}
        let out=Self {inner:super::MixedDriver::new(compiled)};
        assert(super::bank_same(out.bank(),blueprints@.map(|_:int,bp:Blueprint|bp.compiled())));out
    }
    pub fn insert(&mut self,parent:Option<usize>,blueprint:usize)->(out:Result<usize,DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).same(old(self)),
            out.is_ok()==old(self).insertion_enabled(parent,blueprint),
            out.is_ok() ==> old(self).ack(final(self),out.unwrap(),r::Rule::Insert,None),
    {
        let mut draft=self.inner.duplicate();
        let ghost initial=draft;
        proof {draft.same_insertion_domain(&self.inner,parent,blueprint);}
        match draft.insert_inner(parent,blueprint) {
            Err(e)=>Err(e),Ok(id)=>{proof {draft.fresh_administrative_simulation(&initial,id,r::Rule::Insert);reveal(MixedDriver::fresh_ack);}*self=Self {inner:draft};Ok(id)},
        }
    }
    pub fn begin(&mut self,id:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).same(old(self)),
            out.is_ok()==old(self).begin_enabled(id),
            out.is_ok() ==> old(self).ack(final(self),id,r::Rule::Begin,None),
    {
        if !self.inner.registered(id) {return Err(DriverError::Unknown);}
        if !self.inner.rows[id].journal.is_empty() {return Err(DriverError::Retained);}
        let mut draft=self.inner.duplicate();
        let ghost initial=draft;
        proof {Self::same_begin_check(&draft.kernel,&self.inner.kernel,id);}
        match draft.kernel.begin(id) {
            Err(e)=>Err(DriverError::Kernel(e)),
            Ok(())=>{draft.rows[id].current=Some(0);proof {draft.fresh_administrative_simulation(&initial,id,r::Rule::Begin);reveal(MixedDriver::fresh_ack);}*self=Self {inner:draft};Ok(())},
        }
    }
    pub fn retire(&mut self,id:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> old(self).ack(final(self),id,r::Rule::Retire,None),
    {
        let mut draft=self.inner.duplicate();
        let ghost initial=draft;
        match draft.kernel.retire(id) {Err(e)=>Err(DriverError::Kernel(e)),Ok(())=>{proof {draft.fresh_administrative_simulation(&initial,id,r::Rule::Retire);reveal(MixedDriver::fresh_ack);}*self=Self {inner:draft};Ok(())}}
    }
    pub fn depart(&mut self,id:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> r::registered(old(self).control(),id) && old(self).ack(final(self),id,if old(self).control().fibers[id].phase==Phase::Loading {r::Rule::Divert} else {r::Rule::Leave},None),
    {
        if !self.inner.registered(id) {return Err(DriverError::Unknown);}
        let mut draft=self.inner.duplicate();
        let ghost initial=draft;
        match draft.kernel.leave_if_changed(id) {
            Err(e)=>Err(DriverError::Kernel(e)),
            Ok(())=>{draft.rows[id].current=None;proof {draft.fresh_administrative_simulation(&initial,id,if initial.control().fibers[id].phase==Phase::Loading {r::Rule::Divert} else {r::Rule::Leave});reveal(MixedDriver::fresh_ack);}*self=Self {inner:draft};Ok(())},
        }
    }
    pub fn unload(&mut self,actor:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).same(old(self)),
            out.is_ok()==old(self).unload_enabled(actor),
            old(self).unit_child_recovery() && old(self).unit_child_journal(actor)
                ==> out.is_ok()==old(self).cleanup_permitted(actor),
            out.is_ok() ==> old(self).ack(final(self),actor,r::Rule::Unload,None),
    {
        proof {
            if self.unit_child_recovery() && self.unit_child_journal(actor) {self.unit_child_unload_domain(actor);}
        }
        let mut draft=self.inner.duplicate();
        let ghost initial=draft;
        proof {draft.same_unload_domain(&self.inner,actor);}
        match draft.unload_inner(actor) {Err(e)=>Err(e),Ok(())=>{
            proof {draft.fresh_unload_simulation(&initial,actor);reveal(MixedDriver::fresh_ack);}
            *self=Self {inner:draft};Ok(())
        }}
    }
    pub fn remove(&mut self,id:usize)->(out:Result<(),DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> old(self).ack(final(self),id,r::Rule::Remove,None),
    {
        if !self.inner.registered(id) {return Err(DriverError::Unknown);}
        if !self.inner.table_empty(id) {return Err(DriverError::NonemptyTable);}
        let mut owner=0;
        while owner<self.inner.rows.len()
            invariant owner<=self.inner.rows.len(),self.inner.wf(),*self==*old(self),self.inner.table(id).is_empty(),
                forall|n:int,j:int| #![trigger self.inner.rows[n].journal[j]] 0<=n<owner && 0<=j<self.inner.rows[n].journal.len()
                    ==> self.inner.rows[n].journal[j].inverse!=(Inverse::Child {child:id}),
            decreases self.inner.rows.len()-owner,
        {
            let mut i=0;
            while i<self.inner.rows[owner].journal.len()
                invariant owner<self.inner.rows.len(),i<=self.inner.rows[owner as int].journal.len(),self.inner.wf(),*self==*old(self),
                    forall|j:int| 0<=j<i ==> self.inner.rows[owner as int].journal[j].inverse!=(Inverse::Child {child:id}),
                decreases self.inner.rows[owner as int].journal.len()-i,
            {
                if let Inverse::Child {child}=self.inner.rows[owner].journal[i].inverse {
                    if child==id {return Err(DriverError::Retained);}
                }
                i+=1;
            }
            owner+=1;
        }
        let mut draft=self.inner.duplicate();
        let ghost initial=draft;
        proof {assert(initial.unreferenced(id));}
        match draft.kernel.remove(id) {Err(e)=>Err(DriverError::Kernel(e)),Ok(())=>{
            proof {draft.fresh_administrative_simulation(&initial,id,r::Rule::Remove);reveal(MixedDriver::fresh_ack);}
            *self=Self {inner:draft};Ok(())
        }}
    }
    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    pub fn step(&mut self,actor:usize)->(out:Result<Outcome,DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).same(old(self)),
            out.is_ok()==old(self).step_enabled(actor),
            out.is_err() ==> final(self).run_budget(actor)==old(self).run_budget(actor)
                && final(self).step_enabled(actor)==old(self).step_enabled(actor)
                && final(self).journal(actor)==old(self).journal(actor),
            out.is_ok() ==> if super::outcome_rule(out.unwrap())==r::Rule::Iter {
                final(self).run_budget(actor)<old(self).run_budget(actor)
            } else {final(self).run_finished(actor)},
            out.is_ok() ==> final(self).journal(actor).len()==old(self).journal(actor).len()+1
                && (choice(out.unwrap()).is_some() ==> choice(out.unwrap()).unwrap()==old(self).next_id())
                && old(self).ack(final(self),actor,super::outcome_rule(out.unwrap()),choice(out.unwrap())),
    {
        hide(crate::grammar_lift::run);
        let mut draft=self.inner.duplicate();
        let ghost initial=draft;
        proof {
            initial.same_domains(&self.inner,actor,self.selected_instruction(actor));
            draft.kernel.paper_iteration_guard(actor);
            reveal(MixedDriver::ready);
            reveal(MixedDriver::installed_instruction);
            reveal(MixedDriver::instruction_enabled);
        }
        if !draft.registered(actor) {return Err(DriverError::Unknown);}
        if let Err(e)=draft.kernel.check_iteration(actor) {return Err(DriverError::Kernel(e));}
        proof {draft.row_bounds(actor);}
        let pc=match draft.rows[actor].current {None=>return Err(DriverError::InvalidInstruction),Some(pc)=>pc};
        let blueprint=draft.rows[actor].blueprint;let length=draft.blueprints[blueprint].code.len();
        proof {assert(old(self).run_budget(actor)==(length-pc) as nat+1);}
        let template=if pc==length {super::Instruction::Unit} else {draft.blueprints[blueprint].code[pc]};
        let instruction=instantiate_template(&draft,template);
        proof {
            assert(initial.ready(actor));
            assert(template==initial.installed_instruction(actor));
            assert(instruction==self.selected_instruction(actor));
            assert(template.valid(pc,length,blueprint,initial.blueprints[blueprint as int].dependencies(),
                initial.blueprints[blueprint as int].provisions()));
            assert(instruction.continuation()==template.continuation());
        }
        let next=match instruction {super::Instruction::Unit=>None,super::Instruction::Provide {next,..}=>next,
            super::Instruction::Xor {next,..}=>next,super::Instruction::Child {next,..}=>next};
        if let Some(next)=next {if next<=pc || next>length {return Err(DriverError::InvalidInstruction);}}
        let receipt=draft.execute(actor,blueprint,instruction)?;
        let ghost landed=draft;
        proof {instruction_receipt_metadata(initial.blueprints@,blueprint,instruction,initial.primitive_state(),actor,receipt);}
        draft.commit_landing(actor,receipt,next)?;
        let outcome=match receipt.inverse {
            super::Inverse::Child {child}=>Outcome::Child {child,finished:next.is_none()},
            _=>if next.is_none() {Outcome::Finished} else {Outcome::Advanced},
        };
        proof {
            draft.fresh_landing_simulation(&initial,&landed,actor,blueprint,pc,template,instruction,receipt,next,outcome);
            reveal(MixedDriver::fresh_ack);
        }
        *self=Self {inner:draft};
        proof {
            if next.is_some() {
                assert(self.inner.rows[actor as int].current==next);
                assert(self.inner.rows[actor as int].blueprint==blueprint);
                assert(self.inner.blueprints[blueprint as int].code().len()==length);
                assert(self.run_budget(actor)==(length-next.unwrap()) as nat+1);
                assert(self.run_budget(actor)<old(self).run_budget(actor));
            } else {assert(self.run_finished(actor));}
        }
        Ok(outcome)
    }
    /// Dispatch through the same checked executable methods used individually.
    pub fn apply(&mut self,command:Command)->(out:Result<Transition,DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_err() ==> final(self).same(old(self)),
            preparation::preparation_command(command) ==> out.is_ok()==old(self).preparation_enabled(command),
            match command {Command::Unload {actor}=>out.is_ok()==old(self).unload_enabled(actor),_=>true},
            out.is_ok() ==> out.unwrap().command()==command
                && old(self).ack(final(self),label(out.unwrap()).0,label(out.unwrap()).1,label(out.unwrap()).2),
    {
        let transition=match command {
            Command::Insert {parent,blueprint}=>Transition::Insert {parent,blueprint,actor:self.insert(parent,blueprint)?},
            Command::Begin {actor}=>{self.begin(actor)?;Transition::Begin {actor}},
            Command::Step {actor}=>Transition::Step {actor,outcome:self.step(actor)?},
            Command::Retire {actor}=>{self.retire(actor)?;Transition::Retire {actor}},
            Command::Depart {actor}=>{
                let departure=if self.phase(actor)==Some(Phase::Loading) {Departure::Divert} else {Departure::Leave};
                self.depart(actor)?;Transition::Depart {actor,departure}
            },
            Command::Unload {actor}=>{self.unload(actor)?;Transition::Unload {actor}},
            Command::Remove {actor}=>{self.remove(actor)?;Transition::Remove {actor}},
        };
        Ok(transition)
    }
    pub proof fn advance_source(&self,after:&Self,bank:Seq<super::Blueprint>,a:mx::Configuration<u64,Index>,actor:usize,rule:r::Rule,selected:Option<usize>)->(z:mx::Configuration<u64,Index>)
        requires self.represents(bank,a),fs::well_formed(super::library(),programs(bank),a),self.ack(after,actor,rule,selected),
        ensures fs::step(super::library(),programs(bank),a,z,actor,rule,selected),after.represents(bank,z),fs::well_formed(super::library(),programs(bank),z),
    {
        reveal(MixedDriver::fresh_ack);weak_theory();
        assert(self.inner.fresh_ack(&after.inner,actor,rule,selected));
        assert(self.inner.represents(bank,a));
        assert(exists|z:mx::Configuration<u64,Index>| fs::step(super::library(),programs(bank),a,z,actor,rule,selected) && after.inner.represents(bank,z));
        let z=choose|z:mx::Configuration<u64,Index>| fs::step(super::library(),programs(bank),a,z,actor,rule,selected) && after.inner.represents(bank,z);
        fs::configuration_preservation(|_:Port,x:u64,y:u64|x==y,super::library(),programs(bank),a,z,actor,rule,selected);z
    }
    pub proof fn same_representation(&self,other:&Self,bank:Seq<super::Blueprint>,a:mx::Configuration<u64,Index>)
        requires self.wf(),other.wf(),self.same(other),other.represents(bank,a),
        ensures self.represents(bank,a),
    {self.inner.same_representation(&other.inner,bank,a);}
    pub fn phase(&self,actor:usize)->(out:Option<Phase>)
        ensures out==if r::registered(self.control(),actor) {Some(self.control().fibers[actor].phase)} else {None},
    {self.inner.phase(actor)}
    pub fn retired(&self,actor:usize)->bool {self.inner.retired(actor)}
    pub fn read(&self,actor:usize,key:Port)->Option<u64> requires self.wf(), {self.inner.read(actor,key)}
    pub fn inverse_count(&self,actor:usize)->Option<usize> requires self.wf(), {self.inner.inverse_count(actor)}
}

proof fn weak_theory()
    ensures og::primitive_theory(|_:Port,x:u64,y:u64|x==y,super::library()),
{super::library_theory();og::exact_theory(|_:Port,x:u64,y:u64|x==y,super::library());}

pub proof fn program_member(bank:Seq<super::Blueprint>,actor:usize,id:Index)
    requires id.blueprint<bank.len(),id.pc<=bank[id.blueprint as int].code().len(),
        forall|i:int| #![trigger bank[i]] 0<=i<=id.blueprint ==> bank[i].valid(i as usize),
    ensures fg::member(super::library(),programs(bank),actor,
        super::ports(bank[id.blueprint as int].dependencies()).union(super::ports(bank[id.blueprint as int].provisions())),
        super::ports(bank[id.blueprint as int].provisions()),id),
    decreases id.blueprint,bank[id.blueprint as int].code().len()-id.pc,
{
    let bp=bank[id.blueprint as int];let keys=super::ports(bp.dependencies()).union(super::ports(bp.provisions()));
    let provisions=super::ports(bp.provisions());let ps=programs(bank);
    assert(bp.valid(id.blueprint));reveal(super::Blueprint::valid);
    if id.pc<bp.code().len() {
        let instruction=bp.code()[id.pc as int];
        assert(instruction.valid(id.pc,bp.code.len(),id.blueprint,bp.dependencies(),bp.provisions()));
        let next=instruction.continuation();
        if next.is_some() {program_member(bank,actor,Index {blueprint:id.blueprint,pc:next.unwrap()});}
        if let super::Instruction::Child {blueprint,..}=instruction {
            assert forall|child:usize| fg::members(super::library(),ps).contains((child,
                super::ports(bank[blueprint as int].dependencies()).union(super::ports(bank[blueprint as int].provisions())),
                super::ports(bank[blueprint as int].provisions()),Index {blueprint,pc:0})) by {
                program_member(bank,child,Index {blueprint,pc:0});
            }
        }
    }
    assert(fg::obligation(super::library(),ps(actor)(id),actor,keys,provisions,fg::members(super::library(),ps)));
    fg::constructor_member(super::library(),ps,actor,keys,provisions,id);
}

/// Pin the source record to the allocation choice before reasoning about
/// driver rows. Keeping this equality separate avoids unfolding the complete
/// landing history inside every row and journal obligation.
#[verifier::spinoff_prover]
proof fn selected_landing_entry(bank:Seq<super::Blueprint>,a:mx::Configuration<u64,Index>,actor:usize,selected:Option<usize>)
    ensures fs::entry(super::library(),programs(bank),a,actor,selected)==(mx::Entry {
        input:a.state,iterator:a.current[actor].unwrap(),
        landed:fg::run(super::library(),programs(bank)(actor)(a.current[actor].unwrap()),a.state,actor,selected).unwrap(),
    }),
{ }

impl MixedDriver {
    #[verifier::opaque]
    closed spec fn fresh_ack(&self,after:&Self,actor:usize,rule:r::Rule,selected:Option<usize>)->bool {
        forall|bank:Seq<super::Blueprint>,a:mx::Configuration<u64,Index>| self.represents(bank,a) && fs::well_formed(super::library(),programs(bank),a)
            ==> exists|z:mx::Configuration<u64,Index>| fs::step(super::library(),programs(bank),a,z,actor,rule,selected) && after.represents(bank,z)
    }
    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    proof fn fresh_administrative_simulation(&self,initial:&Self,actor:usize,rule:r::Rule)
        requires self.wf(),initial.wf(),r::step(initial.control(),self.control(),actor,rule),
            rule==r::Rule::Insert || rule==r::Rule::Remove || rule==r::Rule::Retire || rule==r::Rule::Begin || rule==r::Rule::Divert || rule==r::Rule::Leave,
            self.blueprints@==initial.blueprints@,self.rows.len()>=initial.rows.len(),
            forall|i:int| 0<=i<initial.rows.len() ==> self.tables[i]==initial.tables[i],
            forall|i:int| 0<=i<initial.rows.len() && i!=actor ==> self.rows[i]==initial.rows[i],
            (rule==r::Rule::Insert ==> actor==initial.rows.len() && self.rows.len()==initial.rows.len()+1
                && self.table(actor).is_empty() && self.journal(actor).len()==0 && self.rows[actor as int].current.is_none()),
            (rule!=r::Rule::Insert ==> self.rows.len()==initial.rows.len()
                && self.rows[actor as int].blueprint==initial.rows[actor as int].blueprint
                && self.journal(actor)==initial.journal(actor)),
            (rule==r::Rule::Begin ==> self.journal(actor).len()==0 && self.rows[actor as int].current==Some(0)),
            (rule==r::Rule::Divert || rule==r::Rule::Leave ==> self.rows[actor as int].current.is_none()),
            (rule==r::Rule::Retire ==> self.rows[actor as int].current==initial.rows[actor as int].current),
            (rule==r::Rule::Remove ==> initial.table(actor).is_empty() && initial.unreferenced(actor)),
        ensures initial.fresh_ack(self,actor,rule,None),
    {
        reveal(MixedDriver::fresh_ack);weak_theory();
        assert forall|bank:Seq<super::Blueprint>,a:mx::Configuration<u64,Index>| initial.represents(bank,a) && fs::well_formed(super::library(),programs(bank),a)
            implies exists|z:mx::Configuration<u64,Index>| fs::step(super::library(),programs(bank),a,z,actor,rule,None) && self.represents(bank,z) by {
            let z=self.administrative(a,actor,rule);
            initial.paper_total(a.state);
            if rule==r::Rule::Insert {
                let bp=self.rows[actor as int].blueprint;
                assert(self.layout(actor as int));assert(self.bank_valid(bp));
                assert forall|i:int| #![trigger bank[i]] 0<=i<=bp implies bank[i].valid(i as usize) by {
                    assert(self.blueprints[i].valid(i as usize));assert(self.blueprints[i].same(&bank[i]));
                }
                program_member(bank,actor,Index {blueprint:bp,pc:0});
                assert(crate::preservation::insert_map(a.state,z.state,actor)) by {
                    assert(z.state.tables==a.state.tables.insert(actor,IMap::empty())) by {
                        assert(z.state.tables =~= a.state.tables.insert(actor,IMap::empty())) by {
                            assert forall|n:usize| z.state.tables.dom().contains(n) implies z.state.tables[n]==a.state.tables.insert(actor,IMap::empty())[n] by {
                                if n!=actor {initial.kernel.paper_observations(n);assert(self.tables[n as int]==initial.tables[n as int]);}
                            }
                        }
                    }
                }
            } else if rule==r::Rule::Begin {
                s::total_targets_agree(a.state,actor,self.control().fibers[actor].committed);
            } else if rule==r::Rule::Divert || rule==r::Rule::Leave {
                s::total_targets_agree(a.state,actor,a.state.control.fibers[actor].committed);
            } else if rule==r::Rule::Remove {
                assert(crate::child_history::remove_unreferenced(mx::kind(a.history),a.state,actor)) by {
                    assert forall|n:usize,token:nat| s::registered(a.state,n) && a.state.accumulators[n].contains(token)
                        implies mx::kind(a.history)(token)!=Some(actor) by {
                        let i=choose|i:int|0<=i<a.state.accumulators[n].len() && a.state.accumulators[n][i]==token;
                        assert(a.history[token as int].landed.receipt==initial.journal(n)[i].model());
                        assert(initial.rows[n as int].journal[i].inverse!=(super::Inverse::Child {child:actor}));
                        match initial.journal(n)[i].inverse {super::Inverse::Child {child}=>{assert(child!=actor);},_=>{},}
                    }
                }
            }
            assert(fs::step(super::library(),programs(bank),a,z,actor,rule,None));
            fs::state_preservation(|_:Port,x:u64,y:u64|x==y,super::library(),programs(bank),a,z,actor,rule,None);
            assert(self.control().fibers.dom() =~= z.state.control.fibers.dom()) by {
                assert forall|n:usize| self.control().fibers.dom().contains(n)==z.state.control.fibers.dom().contains(n) by {
                    if n!=actor {assert(r::registered(self.control(),n)==r::registered(initial.control(),n));}
                }
            }
            assert(self.control().fibers =~= z.state.control.fibers) by {
                assert forall|n:usize| r::registered(self.control(),n) implies self.control().fibers[n]==z.state.control.fibers[n] by {
                    if n!=actor {assert(self.control().fibers[n]==initial.control().fibers[n]);}
                }
            }
            assert(self.tables() =~= z.state.tables) by {
                assert forall|n:usize| r::registered(self.control(),n) implies self.table(n)==z.state.tables[n] by {
                    if n!=actor || rule!=r::Rule::Insert {initial.kernel.paper_observations(n);assert(self.tables[n as int]==initial.tables[n as int]);}
                }
            }
            assert forall|n:usize| r::registered(self.control(),n) implies {
                &&& n<self.rows.len()
                &&& z.roots[n]==(Index {blueprint:self.rows[n as int].blueprint,pc:0})
                &&& z.current[n]==super::continuation(self.rows[n as int].blueprint,self.rows[n as int].current)
                &&& z.state.effects[n]==0 && z.state.iterators[n]==crate::dependent_lift::marker(z.current[n])
                &&& z.state.accumulators[n].len()==self.journal(n).len()
                &&& forall|i:int| #![trigger z.state.accumulators[n][i]] 0<=i<self.journal(n).len() ==> {
                    let token=z.state.accumulators[n][i];token<z.history.len() && z.history[token as int].landed.receipt==self.journal(n)[i].model()
                }
            } by {
                if n!=actor || rule!=r::Rule::Insert {
                    assert(r::registered(initial.control(),n));
                    if n!=actor {assert(self.rows[n as int]==initial.rows[n as int]);}
                }
            }
            assert(self.represents(bank,z));
        }
    }
    #[verifier::spinoff_prover]
    proof fn fresh_unload_simulation(&self,initial:&Self,actor:usize)
        requires self.wf(),initial.wf(),
            r::registered(initial.control(),actor),initial.control().fibers[actor].phase==Phase::Unloading,!r::relied(initial.control(),actor),
            self.journal(actor).len()==0,self.rows[actor as int].current.is_none(),
            self.rows.len()==initial.rows.len(),self.blueprints@==initial.blueprints@,
            self.rows[actor as int].blueprint==initial.rows[actor as int].blueprint,
            forall|i:int| 0<=i<initial.rows.len() && i!=actor ==> self.rows[i]==initial.rows[i],
            super::restore_receipts(initial.journal(actor),initial.primitive_state()).is_some(),
            self.primitive_state()==s::edit(super::restore_receipts(initial.journal(actor),initial.primitive_state()).unwrap(),actor,Phase::Inactive,ISet::empty(),None,Seq::empty()),
        ensures initial.fresh_ack(self,actor,r::Rule::Unload,None),
    {
        reveal(MixedDriver::fresh_ack);weak_theory();
        assert forall|bank:Seq<super::Blueprint>,a:mx::Configuration<u64,Index>| initial.represents(bank,a) && fs::well_formed(super::library(),programs(bank),a)
            implies exists|z:mx::Configuration<u64,Index>| fs::step(super::library(),programs(bank),a,z,actor,r::Rule::Unload,None) && self.represents(bank,z) by {
            assert forall|i:int| #![trigger a.state.accumulators[actor][i]] 0<=i<a.state.accumulators[actor].len() implies {
                let token=a.state.accumulators[actor][i];token<a.history.len()
                    && a.history[token as int].landed.receipt==initial.journal(actor)[i].model() && initial.journal(actor)[i].actor==actor
            } by {assert(initial.rows[actor as int].journal[i].actor==actor);}
            super::restore_journal(a.history,a.state.accumulators[actor],initial.journal(actor),a.state,actor);
            super::restore_payload(initial.journal(actor),initial.primitive_state(),a.state);
            let restored=mx::restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();
            let z=mx::unload(a,actor);
            assert(fs::step(super::library(),programs(bank),a,z,actor,r::Rule::Unload,None));
            fs::restore_preservation(super::library(),programs(bank),a.history,a.state.accumulators[actor],a.state,actor);
            fs::state_preservation(|_:Port,x:u64,y:u64|x==y,super::library(),programs(bank),a,z,actor,r::Rule::Unload,None);
            assert(self.physical(z.state));
            assert forall|n:usize| r::registered(self.control(),n) implies {
                &&& n<self.rows.len()
                &&& z.roots[n]==(Index {blueprint:self.rows[n as int].blueprint,pc:0})
                &&& z.current[n]==super::continuation(self.rows[n as int].blueprint,self.rows[n as int].current)
                &&& z.state.effects[n]==0 && z.state.iterators[n]==crate::dependent_lift::marker(z.current[n])
                &&& z.state.accumulators[n].len()==self.journal(n).len()
                &&& forall|i:int| #![trigger z.state.accumulators[n][i]] 0<=i<self.journal(n).len() ==> {
                    let token=z.state.accumulators[n][i];token<z.history.len() && z.history[token as int].landed.receipt==self.journal(n)[i].model()
                }
            } by {
                assert(r::registered(initial.control(),n));
                if n!=actor {assert(self.rows[n as int]==initial.rows[n as int]);}
            }
            assert(self.represents(bank,z));
        }
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    proof fn fresh_landing_simulation(&self,initial:&Self,landed:&Self,actor:usize,blueprint:usize,pc:usize,
        template:super::Instruction,instruction:super::Instruction,receipt:Receipt,next:Option<usize>,outcome:Outcome)
        requires self.wf(),initial.wf(),landed.wf(),actor<initial.rows.len(),
            r::registered(initial.control(),actor),initial.control().fibers[actor].phase==Phase::Loading,r::coherent(initial.control(),actor),
            initial.rows[actor as int].blueprint==blueprint,initial.rows[actor as int].current==Some(pc),
            template==if pc==initial.blueprints[blueprint as int].code.len() {super::Instruction::Unit} else {initial.blueprints[blueprint as int].code[pc as int]},
            instruction==match template {super::Instruction::Child {blueprint,next,..}=>super::Instruction::Child {expected:initial.rows.len(),blueprint,next},_=>template},
            choice(outcome)==match template {super::Instruction::Child {..}=>Some(initial.rows.len()),_=>None},
            next==instruction.continuation(),super::outcome_rule(outcome)==if next.is_some() {r::Rule::Iter} else {r::Rule::Finish},
            initial.blueprints@==landed.blueprints@,self.blueprints@==initial.blueprints@,
            {
                let y=mx::run(super::library(),super::instruction_node(initial.blueprints@,blueprint,instruction),initial.primitive_state(),actor);
                y.is_some() && landed.physical(y.unwrap().state) && receipt.model()==y.unwrap().receipt
            },
            landed.rows.len()>=initial.rows.len(),self.rows.len()==landed.rows.len(),self.tables@==landed.tables@,
            forall|i:int| 0<=i<initial.rows.len() ==> landed.rows[i]==initial.rows[i],
            forall|i:int| 0<=i<self.rows.len() && i!=actor ==> self.rows[i]==landed.rows[i],
            self.rows[actor as int].blueprint==blueprint,self.rows[actor as int].current==next,
            self.journal(actor)==initial.journal(actor).push(receipt),
            match instruction {
                super::Instruction::Child {expected,blueprint,..}=>expected==initial.rows.len() && landed.rows.len()==initial.rows.len()+1
                    && landed.rows[initial.rows.len() as int].blueprint==blueprint
                    && landed.rows[initial.rows.len() as int].current.is_none()
                    && landed.rows[initial.rows.len() as int].journal.len()==0,
                _=>landed.rows.len()==initial.rows.len(),
            },
            next.is_none() ==> r::step(landed.control(),self.control(),actor,r::Rule::Finish),
            next.is_some() ==> self.control()==landed.control(),
        ensures initial.fresh_ack(self,actor,super::outcome_rule(outcome),choice(outcome)),
    {
        hide(fs::entry);
        reveal(MixedDriver::fresh_ack);
        let length=initial.blueprints[blueprint as int].code.len();
        weak_theory();
            assert forall|bank:Seq<super::Blueprint>,a:mx::Configuration<u64,Index>| initial.represents(bank,a) && fs::well_formed(super::library(),programs(bank),a) implies {
                let rule=super::outcome_rule(outcome);let z=fs::land(super::library(),programs(bank),a,actor,if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active},choice(outcome));
                fs::step(super::library(),programs(bank),a,z,actor,rule,choice(outcome)) && self.represents(bank,z)
            } by {
                let rule=super::outcome_rule(outcome);let phase=if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active};
                let z=fs::land(super::library(),programs(bank),a,actor,phase,choice(outcome));
                selected_landing_entry(bank,a,actor,choice(outcome));
                assert(a.current[actor]==Some(Index {blueprint,pc}));
                assert(bank[blueprint as int].same(&initial.blueprints[blueprint as int]));
                assert(instruction.valid(pc,length,blueprint,initial.blueprints[blueprint as int].dependencies(),initial.blueprints[blueprint as int].provisions()));
                super::instruction_bank(initial.blueprints@,bank,blueprint,instruction);
                instantiate_instruction(bank,blueprint,template,initial.rows.len());
                assert(programs(bank)(actor)(a.current[actor].unwrap())==instruction_node(bank,blueprint,template));
                assert(fg::instantiate(programs(bank)(actor)(a.current[actor].unwrap()),choice(outcome))==Some(super::instruction_node(initial.blueprints@,blueprint,instruction)));
                super::run_payload(initial.blueprints@,blueprint,instruction,initial.primitive_state(),a.state,actor);
                let y=fg::run(super::library(),programs(bank)(actor)(a.current[actor].unwrap()),a.state,actor,choice(outcome)).unwrap();
                assert(landed.physical(y.state));assert(y.receipt==receipt.model());
                assert(y.next==super::continuation(blueprint,next));
                initial.paper_total(a.state);
                s::total_targets_agree(a.state,actor,a.state.control.fibers[actor].committed);
                assert(fs::step(super::library(),programs(bank),a,z,actor,rule,choice(outcome)));
                fs::frame(|_:Port,u:u64,v:u64|u==v,super::library(),programs(bank),a,z,actor,rule,choice(outcome));
                fs::state_preservation(|_:Port,u:u64,v:u64|u==v,super::library(),programs(bank),a,z,actor,rule,choice(outcome));
                assert(self.control().fibers.dom() =~= z.state.control.fibers.dom()) by {
                    assert forall|n:usize| self.control().fibers.dom().contains(n)==z.state.control.fibers.dom().contains(n) by {
                        if n!=actor {assert(r::registered(self.control(),n)==r::registered(landed.control(),n));}
                    }
                }
                assert(self.control().fibers =~= z.state.control.fibers) by {
                    assert forall|n:usize| r::registered(self.control(),n) implies self.control().fibers[n]==z.state.control.fibers[n] by {
                        if n!=actor {assert(self.control().fibers[n]==landed.control().fibers[n]);}
                    }
                }
                assert(self.tables() =~= z.state.tables);
                assert forall|n:usize| r::registered(self.control(),n) implies {
                    &&& n<self.rows.len()
                    &&& z.roots[n]==(Index {blueprint:self.rows[n as int].blueprint,pc:0})
                    &&& z.current[n]==super::continuation(self.rows[n as int].blueprint,self.rows[n as int].current)
                    &&& z.state.effects[n]==0 && z.state.iterators[n]==crate::dependent_lift::marker(z.current[n])
                    &&& z.state.accumulators[n].len()==self.journal(n).len()
                    &&& forall|i:int| #![trigger z.state.accumulators[n][i]] 0<=i<self.journal(n).len() ==> {
                        let token=z.state.accumulators[n][i];token<z.history.len()
                            && z.history[token as int].landed.receipt==self.journal(n)[i].model()
                    }
                } by {
                    if n<initial.rows.len() {
                        assert(r::registered(initial.control(),n));
                        if n!=actor {assert(self.rows[n as int]==initial.rows[n as int]);}
                        assert forall|i:int| #![trigger z.state.accumulators[n][i]] 0<=i<self.journal(n).len() implies {
                            let token=z.state.accumulators[n][i];token<z.history.len()
                                && z.history[token as int].landed.receipt==self.journal(n)[i].model()
                        } by {
                            if n==actor && i==initial.journal(actor).len() {
                                assert(z.history[z.state.accumulators[n][i] as int].landed.receipt==receipt.model());
                            } else {
                                assert(i<initial.journal(n).len());
                                let token=a.state.accumulators[n][i];
                                assert(a.history[token as int].landed.receipt==initial.journal(n)[i].model());
                            }
                        }
                    }
                }
                assert(self.represents(bank,z));
            }
    }


}

pub open spec fn label(transition:Transition)->fs::Label {
    (transition.label().0,transition.label().1,match transition {Transition::Step {outcome,..}=>choice(outcome),_=>None})
}
pub open spec fn labels(transitions:Seq<Transition>)->Seq<fs::Label> {transitions.map(|_:int,t:Transition|label(t))}

/// Results of a finite, synchronous script. The first failure stops execution;
/// the successful prefix and its actual machine remain available to the caller.
pub struct ScriptReport {pub machine:FreshDriver,pub transitions:Vec<Transition>,pub error:Option<DriverError>}
impl ScriptReport {
    pub closed spec fn refines(&self,bank:Seq<super::Blueprint>)->bool {
        exists|states:Seq<mx::Configuration<u64,Index>>| {
            &&& fs::execution(super::library(),programs(bank),states,labels(self.transitions@)) && states.first()==mx::empty::<u64,Index>()
            &&& self.machine.represents(bank,states.last())
            &&& forall|i:int|0<=i<states.len() ==> fs::well_formed(super::library(),programs(bank),states[i]) && crate::preservation::resource_safe(states[i].state)
        }
    }
    /// Expose the source history already established by the actual script,
    /// including the safe prefix returned when a checked command fails.
    pub proof fn source_execution(&self,bank:Seq<super::Blueprint>)->(states:Seq<mx::Configuration<u64,Index>>)
        requires self.refines(bank),
        ensures fs::execution(super::library(),programs(bank),states,labels(self.transitions@)),
            states.first()==mx::empty::<u64,Index>(),self.machine.represents(bank,states.last()),
            forall|i:int|0<=i<states.len() ==> fs::well_formed(super::library(),programs(bank),states[i])
                && crate::preservation::resource_safe(states[i].state),
    {
        choose|states:Seq<mx::Configuration<u64,Index>>| {
            &&& fs::execution(super::library(),programs(bank),states,labels(self.transitions@))
                && states.first()==mx::empty::<u64,Index>()
            &&& self.machine.represents(bank,states.last())
            &&& forall|i:int|0<=i<states.len() ==> fs::well_formed(super::library(),programs(bank),states[i])
                && crate::preservation::resource_safe(states[i].state)
        }
    }
    proof fn establish(&self,bank:Seq<super::Blueprint>,states:Seq<mx::Configuration<u64,Index>>)
        requires self.machine.wf(),fs::execution(super::library(),programs(bank),states,labels(self.transitions@)),states.first()==mx::empty::<u64,Index>(),
            self.machine.represents(bank,states.last()),
        ensures self.refines(bank),self.machine.unit_child_recovery(),
    {
        weak_theory();fs::from_empty_safe(|_:Port,x:u64,y:u64|x==y,super::library(),programs(bank),states,labels(self.transitions@));
        self.machine.unit_child_recovery_from_source(bank,states.last());
    }
}

/// Executes until the first checked error. The successful prefix refines one
/// source execution from new/empty, with no caller-supplied model or history.
/// A failed Insert/Begin/Step is disabled in the returned machine under its
/// exact implementation domain. A failed Unload with an actual Unit/Child
/// journal has a disabled kernel cleanup guard: its inverse domain follows from
/// the constructed history. Other commands and individual error variants remain
/// outside these domains. Checked errors preserve the machine.
#[verifier::spinoff_prover]
pub fn run_script(blueprints:Vec<Blueprint>,commands:&[Command])->(out:ScriptReport)
    ensures out.machine.wf(),out.machine.unit_child_recovery(),
        out.refines(blueprints@.map(|_:int,bp:Blueprint|bp.compiled())),out.transitions.len()<=commands.len(),
        out.error.is_none() ==> out.transitions.len()==commands.len(),
        out.error.is_some() ==> out.transitions.len()<commands.len(),
        out.error.is_some() && preparation::preparation_command(commands[out.transitions.len() as int])
            ==> !out.machine.preparation_enabled(commands[out.transitions.len() as int]),
        out.error.is_some() ==> match commands[out.transitions.len() as int] {
            Command::Unload {actor}=>out.machine.unit_child_journal(actor) ==> !out.machine.cleanup_permitted(actor),
            _=>true,
        },
        forall|i:int|0<=i<out.transitions.len() ==> out.transitions[i].command()==commands[i],
{
    let ghost bank=blueprints@.map(|_:int,bp:Blueprint|bp.compiled());
    let mut machine=FreshDriver::new(blueprints);let mut transitions:Vec<Transition>=Vec::new();let mut i=0;
    let ghost mut states=seq![mx::empty::<u64,Index>()];
    proof {fs::empty_well_formed(super::library(),programs(bank));}
    while i<commands.len()
        invariant i<=commands.len(),transitions.len()==i,machine.wf(),bank==blueprints@.map(|_:int,bp:Blueprint|bp.compiled()),
            forall|j:int|0<=j<i ==> transitions[j].command()==commands[j],
            states.first()==mx::empty::<u64,Index>(),fs::execution(super::library(),programs(bank),states,labels(transitions@)),
            machine.represents(bank,states.last()),fs::well_formed(super::library(),programs(bank),states.last()),
        decreases commands.len()-i,
    {
        let ghost before=machine;
        match machine.apply(commands[i]) {
            Err(error)=>{
                proof {
                    machine.same_representation(&before,bank,states.last());
                    machine.same_preparation_domain(&before,commands[i as int]);
                    if let Command::Unload {actor}=commands[i as int] {machine.same_unload_domain(&before,actor);}
                }
                let out=ScriptReport {machine,transitions,error:Some(error)};
                proof {
                    out.establish(bank,states);
                    if let Command::Unload {actor}=commands[i as int] {
                        if out.machine.unit_child_journal(actor) {out.machine.unit_child_unload_domain(actor);}
                    }
                }
                return out;
            },
            Ok(transition)=>{
                let ghost previous=transitions@;
                transitions.push(transition);
                proof {
                    let z=before.advance_source(&machine,bank,states.last(),label(transition).0,label(transition).1,label(transition).2);
                    let full=states.push(z);
                    assert(labels(transitions@)==labels(previous).push(label(transition)));
                    append_source(bank,states,labels(previous),z,label(transition));
                    states=full;
                }
                i+=1;
            },
        }
    }
    let out=ScriptReport {machine,transitions,error:None};
    proof {out.establish(bank,states);}out
}

proof fn append_source(bank:Seq<super::Blueprint>,states:Seq<mx::Configuration<u64,Index>>,prefix:Seq<fs::Label>,z:mx::Configuration<u64,Index>,label:fs::Label)
    requires fs::execution(super::library(),programs(bank),states,prefix),fs::step(super::library(),programs(bank),states.last(),z,label.0,label.1,label.2),
    ensures fs::execution(super::library(),programs(bank),states.push(z),prefix.push(label)),
{
    assert forall|i:int|0<=i<prefix.len()+1 implies fs::step(super::library(),programs(bank),states.push(z)[i],states.push(z)[i+1],prefix.push(label)[i].0,prefix.push(label)[i].1,prefix.push(label)[i].2) by {
        if i<prefix.len() {assert(fs::step(super::library(),programs(bank),states[i],states[i+1],prefix[i].0,prefix[i].1,prefix[i].2));}
        else {assert(i==prefix.len());assert(states.push(z)[i]==states.last());}
    }
}

}

#[path = "admitted_fresh_driver.rs"]
pub mod admitted;

#[path = "fresh_run.rs"]
pub mod runner;
pub use runner::RunReport;

#[path = "fresh_bootstrap.rs"]
pub mod bootstrap;
pub use bootstrap::{run_from_empty, FromEmptyReport, FromEmptyStatus};

#[path = "fresh_preparation.rs"]
pub mod preparation;
