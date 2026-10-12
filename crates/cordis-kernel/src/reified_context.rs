//! Finite context representation of the executable mixed/fresh interpreter.
//!
//! Programs and inverse receipts are data, interpreted as strict partial maps.
//! This avoids the unrestricted self-function product in Definition 28. The
//! entire live context has an interpretation: control, service values, roots,
//! continuations, allocation and actual inverse journals. Nothing asserts that
//! arbitrary Rust or JavaScript callbacks belong to this closed effect language.
#[cfg(verus_keep_ghost)]
use super::{continuation, fresh, restore_journal, restore_receipts};
use super::{Blueprint, Index, MixedDriver, Receipt};
#[cfg(verus_keep_ghost)]
use crate::{
    fresh_grammar as f, guarded_components as c, mixed_grammar as m, refinement as r,
    semantics as s, Port,
};
use vstd::prelude::*;

verus! {

pub struct Context {
    pub bank:Seq<Blueprint>,
    pub control:crate::refinement::State,
    pub tables:IMap<usize,IMap<crate::Port,u64>>,
    pub roots:IMap<usize,Index>,
    pub current:IMap<usize,Option<Index>>,
    pub journals:IMap<usize,Seq<Receipt>>,
    pub allocation:nat,
}

pub open spec fn read(context:Context,actor:usize,key:Port)->Option<u64> {
    if r::registered(context.control,actor) && context.tables[actor].dom().contains(key) {Some(context.tables[actor][key])} else {None}
}
pub open spec fn accumulator(context:Context,actor:usize,input:s::State<u64>)->Option<s::State<u64>> {
    if !r::registered(context.control,actor) {None} else {restore_receipts(context.journals[actor],input)}
}
/// Actual function interpretation, quantified independently of the current
/// store. Both strict inverse failure and successful outputs are identical.
pub open spec fn interprets(context:Context,bank:Seq<Blueprint>,source:m::Configuration<u64,Index>)->bool {
    &&& super::bank_same(context.bank,bank)
    &&& context.control==source.state.control && context.tables==source.state.tables
    &&& context.roots==source.roots && context.current==source.current
    &&& context.journals.dom()==source.state.control.fibers.dom()
    &&& forall|actor:usize| r::registered(context.control,actor) ==> {
        &&& fresh::programs(context.bank)(actor)(context.roots[actor])==fresh::programs(bank)(actor)(source.roots[actor])
        &&& (context.current[actor].is_some() ==> fresh::programs(context.bank)(actor)(context.current[actor].unwrap())==fresh::programs(bank)(actor)(source.current[actor].unwrap()))
    }
    &&& forall|actor:usize,input:s::State<u64>| r::registered(context.control,actor)
        ==> #[trigger] accumulator(context,actor,input)==m::restore(source.history,source.state.accumulators[actor],input,actor)
}

/// The same strict registration rule with explicit finite-machine limits.
/// Blueprint validation and duplicate Vec declarations are represented, too.
pub open spec fn insertion_enabled(context:Context,parent:Option<usize>,blueprint:usize)->bool {
    &&& blueprint<context.bank.len()
    &&& forall|i:int| #![trigger context.bank[i]] 0<=i<=blueprint ==> context.bank[i].valid(i as usize)
    &&& context.allocation<usize::MAX
    &&& crate::distinct_ports(context.bank[blueprint as int].dependencies())
    &&& crate::distinct_ports(context.bank[blueprint as int].provisions())
    &&& r::insertion_domain(context.control,parent,super::ports(context.bank[blueprint as int].provisions()))
}

/// Equal stored code denotes the same instruction, including its dependent
/// continuation. Validated child indices are interpreted in the same bank.
pub proof fn program_at_same(left:Seq<Blueprint>,right:Seq<Blueprint>,actor:usize,id:Index)
    requires super::bank_same(left,right),id.blueprint<left.len(),left[id.blueprint as int].valid(id.blueprint),
    ensures fresh::programs(left)(actor)(id)==fresh::programs(right)(actor)(id),
{
    let bp=left[id.blueprint as int];
    assert(bp.same(&right[id.blueprint as int]));
    if id.pc<bp.code().len() {
        assert(bp.code()[id.pc as int].valid(id.pc,bp.code().len() as usize,id.blueprint,bp.dependencies(),bp.provisions()));
        if let super::Instruction::Child {blueprint,..}=bp.code()[id.pc as int] {
            assert(blueprint<left.len());assert(left[blueprint as int].same(&right[blueprint as int]));
        }
    }
}

impl MixedDriver {
    pub closed spec fn reified(&self)->Context {
        Context {bank:self.blueprints@,control:self.control(),tables:self.tables(),allocation:self.rows.len() as nat,
            roots:IMap::new(|n:usize|r::registered(self.control(),n),|n:usize|Index {blueprint:self.rows[n as int].blueprint,pc:0}),
            current:IMap::new(|n:usize|r::registered(self.control(),n),|n:usize|continuation(self.rows[n as int].blueprint,self.rows[n as int].current)),
            journals:IMap::new(|n:usize|r::registered(self.control(),n),|n:usize|self.journal(n))}
    }

    /// Export the read law without exposing the private context representation
    /// to the parent module's executable implementation.
    pub proof fn read_interpretation(&self,actor:usize,key:Port)
        ensures read(self.reified(),actor,key)==if r::registered(self.control(),actor) && self.table(actor).dom().contains(key) {Some(self.table(actor)[key])} else {None},
    { }

    pub proof fn reified_insertion_domain(&self,parent:Option<usize>,blueprint:usize)
        requires self.wf(),
        ensures self.insertion_enabled(parent,blueprint)==insertion_enabled(self.reified(),parent,blueprint),
    {
        if blueprint<self.blueprints.len() {
            self.kernel.paper_insert_domain(parent,self.blueprints[blueprint as int].dependencies(),self.blueprints[blueprint as int].provisions());
        }
    }

    /// Establishes the strong function-field bridge from the real Vec journal,
    /// not from an assumed equality of history identifiers.
    pub proof fn reified_representation(&self,bank:Seq<Blueprint>,source:m::Configuration<u64,Index>)
        requires self.wf(),self.represents(bank,source),
        ensures interprets(self.reified(),bank,source),
    {
        let context=self.reified();
        assert(context.roots =~= source.roots);
        assert(context.current =~= source.current) by {
            assert forall|n:usize| r::registered(context.control,n) implies context.current[n]==source.current[n] by {
                assert(source.roots[n]==context.roots[n]);
            }
        }
        assert forall|actor:usize| r::registered(context.control,actor) implies {
            &&& fresh::programs(context.bank)(actor)(context.roots[actor])==fresh::programs(bank)(actor)(source.roots[actor])
            &&& (context.current[actor].is_some() ==> fresh::programs(context.bank)(actor)(context.current[actor].unwrap())==fresh::programs(bank)(actor)(source.current[actor].unwrap()))
        } by {
            assert(actor<self.rows.len());
            let bp=self.rows[actor as int].blueprint;
            assert(self.bank_valid(bp));
            program_at_same(context.bank,bank,actor,context.roots[actor]);
            if context.current[actor].is_some() {program_at_same(context.bank,bank,actor,context.current[actor].unwrap());}
        }
        assert forall|actor:usize,input:s::State<u64>| r::registered(context.control,actor)
            implies #[trigger] accumulator(context,actor,input)==m::restore(source.history,source.state.accumulators[actor],input,actor) by {
            assert(actor<self.rows.len());
            let tokens=source.state.accumulators[actor];let receipts=self.journal(actor);
            assert forall|i:int| #![trigger tokens[i]] 0<=i<tokens.len() implies {
                tokens[i]<source.history.len() && source.history[tokens[i] as int].landed.receipt==receipts[i].model() && receipts[i].actor==actor
            } by {assert(self.rows[actor as int].journal[i].actor==actor);}
            restore_journal(source.history,tokens,receipts,input,actor);
        }
    }

    /// Every installed root is a semantic Component of the strict revision,
    /// including parents whose code dynamically creates children.
    pub proof fn root_component(&self,actor:usize)
        requires self.wf(),r::registered(self.control(),actor),
        ensures c::component(super::library(),fresh::programs(self.reified().bank),actor,
            self.control().fibers[actor].dependencies.union(self.control().fibers[actor].provisions),
            self.control().fibers[actor].provisions,self.reified().roots[actor]),
    {
        self.kernel.paper_observations(actor);
        assert(actor<self.rows.len());
        let bp=self.rows[actor as int].blueprint;
        assert(self.layout(actor as int));assert(self.bank_valid(bp));
        super::library_theory();
        fresh::program_member(self.blueprints@,actor,Index {blueprint:bp,pc:0});
        c::member_is_component(|_:Port,a:u64,b:u64|a==b,super::library(),fresh::programs(self.blueprints@),actor,
            super::ports(self.blueprints[bp as int].dependencies()).union(super::ports(self.blueprints[bp as int].provisions())),
            super::ports(self.blueprints[bp as int].provisions()),Index {blueprint:bp,pc:0});
    }

    /// Read-only inspection of the actual inverse data; it does not execute or
    /// manufacture cleanup and does not expose a mutable journal reference.
    pub fn inverse_at(&self,actor:usize,index:usize)->(out:Option<Receipt>)
        requires self.wf(),
        ensures out==if r::registered(self.control(),actor) && index<self.journal(actor).len() {Some(self.journal(actor)[index as int])} else {None},
    {
        if !self.registered(actor) {return None;}
        if index>=self.rows[actor].journal.len() {None} else {Some(self.rows[actor].journal[index])}
    }
}

/// The source and executable root/current fields denote identical strict
/// calls on every context input and allocation choice, not just this store.
pub proof fn function_correspondence(context:Context,bank:Seq<Blueprint>,source:m::Configuration<u64,Index>,actor:usize,input:s::State<u64>,choice:Option<usize>)
    requires interprets(context,bank,source),r::registered(context.control,actor),
    ensures f::run(super::library(),fresh::programs(context.bank)(actor)(context.roots[actor]),input,actor,choice)
            ==f::run(super::library(),fresh::programs(bank)(actor)(source.roots[actor]),input,actor,choice),
        context.current[actor].is_some() ==> f::run(super::library(),fresh::programs(context.bank)(actor)(context.current[actor].unwrap()),input,actor,choice)
            ==f::run(super::library(),fresh::programs(bank)(actor)(source.current[actor].unwrap()),input,actor,choice),
        accumulator(context,actor,input)==m::restore(source.history,source.state.accumulators[actor],input,actor),
{ }

/// A nontrivial inhabitant is constructed by an existing checked execution;
/// the carrier is neither assumed inhabited nor reduced to a singleton.
pub proof fn nontrivial_carrier()
    ensures c::carrier(super::library(),crate::mixed_examples::trace().last().state),
        c::carrier(super::library(),m::empty::<u64,Index>().state),
        crate::mixed_examples::trace().last().state!=m::empty::<u64,Index>().state,
        crate::mixed_examples::trace().last().state.tables[1usize].dom().contains(crate::mixed_examples::key(1)),
        crate::mixed_examples::trace().last().state.tables[1usize][crate::mixed_examples::key(1)]==42,
{
    crate::mixed_examples::parent_recovers_with_active_child();
    crate::mixed_examples::actual_execution();
    assert(crate::mixed_examples::trace().last()==crate::mixed_examples::trace()[9]);
    m::empty_well_formed(super::library(),super::programs(Seq::empty()));
    reveal(crate::mixed_examples::trace);
    assert(r::registered(crate::mixed_examples::trace().last().state.control,1));
}

/// Equality of the read-only API observation with the source's actual values.
pub proof fn value_correspondence(context:Context,bank:Seq<Blueprint>,source:m::Configuration<u64,Index>,actor:usize,key:Port)
    requires interprets(context,bank,source),
    ensures read(context,actor,key)==if s::registered(source.state,actor) && source.state.tables[actor].dom().contains(key) {Some(source.state.tables[actor][key])} else {None},
{ }

} // verus!
